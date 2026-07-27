-------------------------- MODULE BfTreeCprHandshake --------------------------
(***************************************************************************)
(* Bf-Tree's CPR snapshot PHASE TRANSITION on x86-TSO.                     *)
(*                                                                         *)
(* Source: bf-tree @ ad17a2e, src/snapshot.rs                              *)
(*   Worker  reserve_thread_slot   :415 CAS thread_slots[tid]              *)
(*                                 :420 LOAD  global_state                 *)
(*                                 :421 STORE thread_local_states[tid]     *)
(*                                      (-> :304 set_local_state)          *)
(*                                 :432 LOAD  global_state (double-check)  *)
(*   Manager advance_global_state  :332 STORE global_state                 *)
(*           check_if_phase_completed :342 LOAD thread_local_states[..]    *)
(*                                                                         *)
(* Both sides store to their own location and then load the other's. That  *)
(* is the SB litmus of memory-models/X86TSO.tla with the two threads doing *)
(* real work, so the same StoreLoad window applies: each core's store sits  *)
(* in its private FIFO buffer while its own later load already executes.    *)
(*                                                                         *)
(* The comment at snapshot.rs:426-431 claims the :432 double-check rules    *)
(* this out. It does not: the double-check is the *load* half of the        *)
(* worker's own store-then-load, so it can read a stale global_state for    *)
(* exactly as long as the announce is still buffered.                       *)
(*                                                                         *)
(* Fix values                                                              *)
(*   "None"          Release store / Acquire load. On x86 a release store   *)
(*                   is a plain MOV and an acquire load is a plain MOV, so  *)
(*                   nothing here is fenced.        -> VIOLATED             *)
(*   "SeqCstStores"  SeqCst on the two stores only. rustc lowers a SeqCst   *)
(*                   store to XCHG, a LOCKed RMW that drains the buffer.    *)
(*                   -> HOLDS. See the note at the bottom: this is a fact   *)
(*                   about x86 codegen, NOT about the Rust memory model,    *)
(*                   under which stores-only is still broken.               *)
(***************************************************************************)
EXTENDS Integers, Sequences

CONSTANT Fix

W == "worker"
M == "manager"
Procs == {W, M}

\* Packed (phase | version) states. Only the transition matters, not the bits.
OldState     == 0
NewState     == 1
InvalidState == 9      \* INVALID_SNAPSHOT_STATE (u64::MAX in the source)

VARIABLES buf, mem, wSeen, wCommitted, mPhaseDone, pcW, pcM
vars == <<buf, mem, wSeen, wCommitted, mPhaseDone, pcW, pcM>>

Max(S) == CHOOSE x \in S : \A y \in S : y <= x

\* Store forwarding: newest buffered write to f in p's buffer, else memory.
Load(p, f) ==
    LET idxs == { i \in DOMAIN buf[p] : buf[p][i].f = f }
    IN  IF idxs = {} THEN mem[f] ELSE buf[p][Max(idxs)].v

FencedStores == Fix = "SeqCstStores"

Init ==
    /\ buf = [p \in Procs |-> <<>>]
    /\ mem = [ gs |-> OldState, tls |-> InvalidState, slot |-> 0 ]
    /\ wSeen = InvalidState
    /\ wCommitted = FALSE
    /\ mPhaseDone = FALSE
    /\ pcW = "cas"
    /\ pcM = "advance"

\* FIFO drain: the head of a core's store buffer becomes globally visible.
Flush(p) ==
    /\ buf[p] # <<>>
    /\ mem' = [mem EXCEPT ![Head(buf[p]).f] = Head(buf[p]).v]
    /\ buf' = [buf EXCEPT ![p] = Tail(buf[p])]
    /\ UNCHANGED <<wSeen, wCommitted, mPhaseDone, pcW, pcM>>

\* Worker --------------------------------------------------------------------

\* :415 compare_exchange(false, true, AcqRel, Relaxed). A LOCKed RMW, so it is
\* a full barrier -- but it sits BEFORE the announce store, so it orders
\* nothing that matters here. Modelled as a drain plus an immediate write.
Cas ==
    /\ pcW = "cas"
    /\ mem.slot = 0
    /\ buf[W] = <<>>
    /\ mem' = [mem EXCEPT !.slot = 1]
    /\ pcW' = "read"
    /\ UNCHANGED <<buf, wSeen, wCommitted, mPhaseDone, pcM>>

\* :420 let global_state = self.global_state.load(Acquire)
Read ==
    /\ pcW = "read"
    /\ wSeen' = Load(W, "gs")
    /\ pcW' = "announce"
    /\ UNCHANGED <<buf, mem, wCommitted, mPhaseDone, pcM>>

\* :421 -> :304 self.thread_local_states[tid].store(state, Release)
Announce ==
    /\ pcW = "announce"
    /\ IF FencedStores
       THEN /\ buf[W] = <<>>
            /\ mem' = [mem EXCEPT !.tls = wSeen]
            /\ UNCHANGED buf
       ELSE /\ buf' = [buf EXCEPT ![W] = Append(buf[W], [f |-> "tls", v |-> wSeen])]
            /\ UNCHANGED mem
    /\ pcW' = "check"
    /\ UNCHANGED <<wSeen, wCommitted, mPhaseDone, pcM>>

\* :432 let current_global = self.global_state.load(Acquire)
\* Equal means "the phase did not move under me" -> commit. Otherwise roll back.
Check ==
    /\ pcW = "check"
    /\ IF Load(W, "gs") = wSeen
       THEN /\ wCommitted' = TRUE
            /\ UNCHANGED buf
       ELSE /\ wCommitted' = FALSE
            /\ buf' = [buf EXCEPT ![W] = Append(buf[W], [f |-> "tls", v |-> InvalidState])]
    /\ pcW' = "done"
    /\ UNCHANGED <<mem, wSeen, mPhaseDone, pcM>>

\* Manager -------------------------------------------------------------------

\* :332 self.global_state.store(new_state, Release)
Advance ==
    /\ pcM = "advance"
    /\ IF FencedStores
       THEN /\ buf[M] = <<>>
            /\ mem' = [mem EXCEPT !.gs = NewState]
            /\ UNCHANGED buf
       ELSE /\ buf' = [buf EXCEPT ![M] = Append(buf[M], [f |-> "gs", v |-> NewState])]
            /\ UNCHANGED mem
    /\ pcM' = "scan"
    /\ UNCHANGED <<wSeen, wCommitted, mPhaseDone, pcW>>

\* :342 check_if_phase_completed: every slot is INVALID or already in the
\* target state. One worker slot, so one load.
Scan ==
    /\ pcM = "scan"
    /\ LET v == Load(M, "tls")
       IN mPhaseDone' = (v = InvalidState \/ v = NewState)
    /\ pcM' = "done"
    /\ UNCHANGED <<buf, mem, wSeen, wCommitted, pcW>>

Next ==
    \/ Cas \/ Read \/ Announce \/ Check
    \/ Advance \/ Scan
    \/ (\E p \in Procs : Flush(p))

Spec == Init /\ [][Next]_vars

(***************************************************************************)
(* SAFETY: the manager must never conclude the phase is complete while a    *)
(* worker is live in the phase it just left. This is precisely the property *)
(* snapshot.rs:426-431 says the double-check establishes.                   *)
(*                                                                         *)
(* When it fails, the manager runs the new phase's action -- and for the    *)
(* Sweep phase that action reclaims inner nodes. See BfTreeCprSweep.tla.    *)
(***************************************************************************)
PhaseCompletionIsSound == ~ (wCommitted /\ wSeen = OldState /\ mPhaseDone)

(***************************************************************************)
(* NOTE ON "SeqCstStores"                                                  *)
(*                                                                         *)
(* This spec models the MACHINE. On x86-64 a SeqCst store lowers to XCHG,   *)
(* which drains the buffer, so promoting only the stores does close the     *)
(* window in hardware and TLC reports HOLDS.                                *)
(*                                                                         *)
(* That is NOT a licence to fix it that way. Rust's memory model is not     *)
(* x86-TSO: the SeqCst total order constrains SeqCst operations only, so an *)
(* Acquire load on either side is not in it and the reordering stays        *)
(* permitted by the language. Checking the same handshake in C11/RC11 with  *)
(* GenMC reports a safety violation for stores-only, and again for          *)
(* loads-only, and no errors only when both are SeqCst -- see the results   *)
(* table in tla/README.md.                                                  *)
(*                                                                         *)
(* The disagreement is the point: TLC says what this hardware does, GenMC   *)
(* says what the language promises, and a fix has to satisfy the language.  *)
(***************************************************************************)
=============================================================================
