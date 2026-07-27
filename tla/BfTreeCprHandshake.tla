-------------------------- MODULE BfTreeCprHandshake --------------------------
(***************************************************************************)
(* Bf-Tree's CPR snapshot PHASE TRANSITION, on the x86-TSO model in         *)
(* X86TSO.tla.                                                              *)
(*                                                                         *)
(* Source: src/snapshot.rs                                                 *)
(*   Worker  reserve_thread_slot      CAS   thread_slots[tid]              *)
(*                                    LOAD  global_state                   *)
(*                                    STORE thread_local_states[tid]       *)
(*                                          (via set_local_state)          *)
(*                                    LOAD  global_state (double-check)    *)
(*   Manager advance_global_state     STORE global_state                   *)
(*           check_if_phase_completed LOAD  thread_local_states[..]        *)
(*                                                                         *)
(* Both sides store to their own location and then load the other's. That   *)
(* is SBLitmus.tla with the two cores doing real work, so the same          *)
(* StoreLoad window applies: each core's store sits in its private FIFO     *)
(* buffer while its own later load has already executed.                    *)
(*                                                                         *)
(* The comment in `reserve_thread_slot` claims the double-check rules this  *)
(* out. It does not: the double-check is the *load* half of the worker's    *)
(* own store-then-load, so it can read a stale global_state for exactly as  *)
(* long as the announce is still buffered.                                  *)
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

\* gs   = global_state
\* tls  = thread_local_states[tid]  (one worker, so one slot)
\* slot = thread_slots[tid]
Locs == {"gs", "tls", "slot"}

\* Packed (phase | version) states. Only the transition matters, not the bits.
OldState     == 0
NewState     == 1
InvalidState == 9      \* INVALID_SNAPSHOT_STATE (u64::MAX in the source)

VARIABLES buf, mem, wSeen, wCommitted, mPhaseDone, pcW, pcM
vars == <<buf, mem, wSeen, wCommitted, mPhaseDone, pcW, pcM>>

TSO == INSTANCE X86TSO

FencedStores == Fix = "SeqCstStores"

\* Release store vs SeqCst store, chosen by the Fix constant.
Announce(p, loc, val) ==
    IF FencedStores THEN TSO!LockedStore(p, loc, val) ELSE TSO!Store(p, loc, val)

Init ==
    /\ TSO!TSOInit([l \in Locs |->
           IF l = "gs" THEN OldState ELSE IF l = "tls" THEN InvalidState ELSE 0])
    /\ wSeen = InvalidState
    /\ wCommitted = FALSE
    /\ mPhaseDone = FALSE
    /\ pcW = "cas"
    /\ pcM = "advance"

DoFlush(p) ==
    /\ TSO!Flush(p)
    /\ UNCHANGED <<wSeen, wCommitted, mPhaseDone, pcW, pcM>>

\* Worker --------------------------------------------------------------------

\* compare_exchange(false, true, AcqRel, Relaxed). A LOCKed RMW, so it is a
\* full barrier -- but it sits BEFORE the announce store, so it orders nothing
\* that matters here.
Cas ==
    /\ pcW = "cas"
    /\ TSO!Load(W, "slot") = 0
    /\ TSO!Rmw(W, "slot", 1)
    /\ pcW' = "read"
    /\ UNCHANGED <<wSeen, wCommitted, mPhaseDone, pcM>>

\* let global_state = self.global_state.load(Acquire)
Read ==
    /\ pcW = "read"
    /\ wSeen' = TSO!Load(W, "gs")
    /\ pcW' = "announce"
    /\ UNCHANGED <<buf, mem, wCommitted, mPhaseDone, pcM>>

\* set_local_state: self.thread_local_states[tid].store(state, Release)
DoAnnounce ==
    /\ pcW = "announce"
    /\ Announce(W, "tls", wSeen)
    /\ pcW' = "check"
    /\ UNCHANGED <<wSeen, wCommitted, mPhaseDone, pcM>>

\* let current_global = self.global_state.load(Acquire)
\* Equal means "the phase did not move under me" -> commit. Otherwise roll back.
Check ==
    /\ pcW = "check"
    /\ IF TSO!Load(W, "gs") = wSeen
       THEN /\ wCommitted' = TRUE
            /\ UNCHANGED <<buf, mem>>
       ELSE /\ wCommitted' = FALSE
            /\ TSO!Store(W, "tls", InvalidState)
    /\ pcW' = "done"
    /\ UNCHANGED <<wSeen, mPhaseDone, pcM>>

\* Manager -------------------------------------------------------------------

\* self.global_state.store(new_state, Release)
Advance ==
    /\ pcM = "advance"
    /\ Announce(M, "gs", NewState)
    /\ pcM' = "scan"
    /\ UNCHANGED <<wSeen, wCommitted, mPhaseDone, pcW>>

\* check_if_phase_completed: every slot is INVALID or already in the target
\* state. One worker slot, so one load.
Scan ==
    /\ pcM = "scan"
    /\ LET v == TSO!Load(M, "tls")
       IN  mPhaseDone' = (v = InvalidState \/ v = NewState)
    /\ pcM' = "done"
    /\ UNCHANGED <<buf, mem, wSeen, wCommitted, pcW>>

Next ==
    \/ Cas \/ Read \/ DoAnnounce \/ Check
    \/ Advance \/ Scan
    \/ (\E p \in Procs : DoFlush(p))

Spec == Init /\ [][Next]_vars

(***************************************************************************)
(* SAFETY: the manager must never conclude the phase is complete while a    *)
(* worker has committed to the phase it just left. This is precisely the    *)
(* property the comment in `reserve_thread_slot` says the double-check      *)
(* establishes.                                                             *)
(*                                                                         *)
(* When it fails, the manager runs the new phase's action -- and for the    *)
(* Sweep phase that action treats the tree as frozen. See BfTreeCprSweep.   *)
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
(* permitted by the language. Both GenMC under RC11 and Miri reject         *)
(* stores-only, and reject loads-only, and are clean only when both sides   *)
(* are SeqCst -- see the table in tla/README.md.                            *)
(*                                                                         *)
(* The disagreement is the point: TLC says what this hardware does, GenMC   *)
(* and Miri say what the language promises, and a fix has to satisfy the    *)
(* language.                                                                *)
(***************************************************************************)
===============================================================================
