-------------------------------- MODULE X86TSO --------------------------------
(***************************************************************************)
(* A reusable model of the x86-TSO memory model.                            *)
(*                                                                         *)
(* Every core has a private FIFO store buffer in front of a single shared   *)
(* memory. A store lands in the issuing core's buffer and becomes visible   *)
(* to everyone else only when it drains. A load reads the newest buffered   *)
(* store to that location if the core has one (store forwarding), otherwise *)
(* it reads memory.                                                        *)
(*                                                                         *)
(* That is the whole model, and it is what makes StoreLoad the one          *)
(* reordering x86 permits: a core's store can still be sitting in its own   *)
(* buffer while its own later load of a *different* location has already    *)
(* taken its value from memory. Loads are not reordered with loads, stores  *)
(* are not reordered with stores, and a core always sees its own stores.    *)
(*                                                                         *)
(* Instantiate it by declaring `buf` and `mem` and defining `Procs` and     *)
(* `Locs`, then `TSO == INSTANCE X86TSO`. `SBLitmus.tla` validates the      *)
(* model against the classic store-buffer litmus; `BfTreeCprHandshake.tla`  *)
(* and `BfTreeCprSweep.tla` build the Bf-Tree handshake on top of it.       *)
(*                                                                         *)
(* Operators                                                               *)
(*   TSOInit(m)         initial state: empty buffers, memory `m`            *)
(*   Load(p, loc)       value p reads from loc (store forwarding)           *)
(*   Store(p, loc, v)   plain MOV: append to p's buffer                     *)
(*   LockedStore(..)    LOCK-prefixed store / XCHG: drains, then writes     *)
(*   Rmw(p, loc, v)     read-modify-write; same barrier as LockedStore      *)
(*   Fence(p)           MFENCE: blocks until p's buffer is empty            *)
(*   Flush(p)           one buffered store of p becomes globally visible    *)
(*   Drained(p)         TRUE when p's buffer is empty                       *)
(*                                                                         *)
(* `Store`, `LockedStore`, `Rmw`, `Fence` and `Flush` are actions: each      *)
(* constrains both `buf'` and `mem'`, so a client action that uses one must *)
(* not also specify them.                                                   *)
(*                                                                         *)
(* A LOCKed operation is modelled as *enabled only when the buffer is       *)
(* already empty* rather than as draining it itself. For safety checking    *)
(* the two are equivalent, because `Flush` is always enabled and TLC will   *)
(* explore the drain-then-write orderings.                                  *)
(***************************************************************************)
EXTENDS Integers, Sequences

CONSTANTS
    Procs,      \* the set of cores
    Locs        \* the set of shared memory locations

VARIABLES
    buf,        \* buf[p] : sequence of [loc |-> Locs, val |-> _], oldest first
    mem         \* mem[loc] : the globally visible value

tsoVars == <<buf, mem>>

MaxOf(S) == CHOOSE x \in S : \A y \in S : y <= x

TSOInit(initial) ==
    /\ buf = [p \in Procs |-> <<>>]
    /\ mem = initial

Drained(p) == buf[p] = <<>>

(***************************************************************************)
(* A load takes the newest value this core has buffered for `loc`, and only *)
(* falls through to memory when it has none. This is store forwarding: it   *)
(* is why a core never fails to see its own writes, even though other cores *)
(* may not see them yet.                                                    *)
(***************************************************************************)
Load(p, loc) ==
    LET pending == { i \in DOMAIN buf[p] : buf[p][i].loc = loc }
    IN  IF pending = {} THEN mem[loc] ELSE buf[p][MaxOf(pending)].val

(***************************************************************************)
(* A plain store retires into the buffer. It is NOT globally visible yet --  *)
(* this single fact is the whole bug class these specs are about.           *)
(***************************************************************************)
Store(p, loc, val) ==
    /\ buf' = [buf EXCEPT ![p] = Append(buf[p], [loc |-> loc, val |-> val])]
    /\ mem' = mem

(***************************************************************************)
(* A LOCK-prefixed store (which is how rustc lowers a SeqCst store on       *)
(* x86-64: XCHG) is globally visible when it executes.                      *)
(***************************************************************************)
LockedStore(p, loc, val) ==
    /\ Drained(p)
    /\ mem' = [mem EXCEPT ![loc] = val]
    /\ buf' = buf

Rmw(p, loc, val) == LockedStore(p, loc, val)

Fence(p) ==
    /\ Drained(p)
    /\ UNCHANGED tsoVars

(***************************************************************************)
(* FIFO drain: the oldest buffered store of `p` becomes globally visible.    *)
(* Always enabled while the buffer is non-empty, so TLC explores every       *)
(* interleaving of drains with the cores' own steps.                         *)
(***************************************************************************)
Flush(p) ==
    /\ buf[p] # <<>>
    /\ mem' = [mem EXCEPT ![Head(buf[p]).loc] = Head(buf[p]).val]
    /\ buf' = [buf EXCEPT ![p] = Tail(buf[p])]

FlushAny == \E p \in Procs : Flush(p)

TypeOK ==
    /\ mem \in [Locs -> Int]
    /\ buf \in [Procs -> Seq([loc : Locs, val : Int])]
===============================================================================
