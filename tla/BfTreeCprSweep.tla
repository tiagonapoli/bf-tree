----------------------------- MODULE BfTreeCprSweep -----------------------------
(***************************************************************************)
(* Bf-Tree's CPR snapshot SWEEP FREEZE on x86-TSO.                          *)
(*                                                                         *)
(* Source: bf-tree @ ad17a2e, src/snapshot.rs                              *)
(*   Manager sweep                   :556 STORE pause_snapshot = true      *)
(*                                   :558 LOAD  thread_local_states[..]    *)
(*                                        (check_if_phase_completed)       *)
(*                                   :561+ traverse the tree and reclaim   *)
(*   Worker  reserve_thread_slot     :406 LOAD  pause_snapshot (early out) *)
(*                                   :415 CAS   thread_slots[tid]          *)
(*                                   :421 STORE thread_local_states[tid]   *)
(*                                   :434 LOAD  pause_snapshot (re-check)  *)
(*                                                                         *)
(* Same StoreLoad window as BfTreeCprHandshake.tla, but here the manager's  *)
(* next act is destructive. sweep's three-phase comment (:550-553) reads:   *)
(*                                                                         *)
(*   Phase 1: Block all snapshot id reservation, drain the thread table.    *)
(*   Phase 2: Traverse the tree and take snapshots of inner nodes ...       *)
(*   Phase 3: Unblock snapshot id reservation.                              *)
(*                                                                         *)
(* Phase 1 is a store-then-load on both sides, so the drain can report an   *)
(* empty thread table while the worker is being handed a slot. The tree is  *)
(* then not frozen, and phase 2 collects and reclaims inner nodes under a   *)
(* live writer.                                                            *)
(*                                                                         *)
(* This is the Bf-Tree analogue of LightEpoch.tla: same invariant, same     *)
(* shape of counterexample, different codebase and language.                *)
(*                                                                         *)
(* Fix values are as in BfTreeCprHandshake.tla: "None" -> VIOLATED,         *)
(* "SeqCstStores" -> HOLDS on x86 only.                                     *)
(***************************************************************************)
EXTENDS Integers, Sequences

CONSTANT Fix

W == "worker"
M == "manager"
Procs == {W, M}

LiveState    == 0
InvalidState == 9      \* INVALID_SNAPSHOT_STATE

VARIABLES buf, mem, holds, pcW, pcM
vars == <<buf, mem, holds, pcW, pcM>>

Max(S) == CHOOSE x \in S : \A y \in S : y <= x

Load(p, f) ==
    LET idxs == { i \in DOMAIN buf[p] : buf[p][i].f = f }
    IN  IF idxs = {} THEN mem[f] ELSE buf[p][Max(idxs)].v

FencedStores == Fix = "SeqCstStores"

Init ==
    /\ buf = [p \in Procs |-> <<>>]
    /\ mem = [ pause |-> 0, tls |-> InvalidState, slot |-> 0, freed |-> 0 ]
    /\ holds = FALSE
    /\ pcW = "early"
    /\ pcM = "pause"

Flush(p) ==
    /\ buf[p] # <<>>
    /\ mem' = [mem EXCEPT ![Head(buf[p]).f] = Head(buf[p]).v]
    /\ buf' = [buf EXCEPT ![p] = Tail(buf[p])]
    /\ UNCHANGED <<holds, pcW, pcM>>

\* Worker --------------------------------------------------------------------

\* :406 if self.pause_snapshot.load(Acquire) { return Err(()) }
Early ==
    /\ pcW = "early"
    /\ IF Load(W, "pause") = 1
       THEN pcW' = "done"
       ELSE pcW' = "cas"
    /\ UNCHANGED <<buf, mem, holds, pcM>>

\* :415 compare_exchange(false, true, AcqRel, Relaxed). A LOCKed RMW, hence a
\* full barrier -- but it precedes the announce store, so it orders nothing.
Cas ==
    /\ pcW = "cas"
    /\ mem.slot = 0
    /\ buf[W] = <<>>
    /\ mem' = [mem EXCEPT !.slot = 1]
    /\ pcW' = "announce"
    /\ UNCHANGED <<buf, holds, pcM>>

\* :421 -> :304 announce that this slot is live.
Announce ==
    /\ pcW = "announce"
    /\ IF FencedStores
       THEN /\ buf[W] = <<>>
            /\ mem' = [mem EXCEPT !.tls = LiveState]
            /\ UNCHANGED buf
       ELSE /\ buf' = [buf EXCEPT ![W] = Append(buf[W], [f |-> "tls", v |-> LiveState])]
            /\ UNCHANGED mem
    /\ pcW' = "recheck"
    /\ UNCHANGED <<holds, pcM>>

\* :434 || self.pause_snapshot.load(Acquire)  -> roll back, else the slot is
\* granted and the caller may mutate the tree structure.
Recheck ==
    /\ pcW = "recheck"
    /\ IF Load(W, "pause") = 1
       THEN /\ holds' = FALSE
            /\ buf' = [buf EXCEPT ![W] = Append(buf[W], [f |-> "tls", v |-> InvalidState])]
            /\ pcW' = "done"
       ELSE /\ holds' = TRUE
            /\ pcW' = "use"
            /\ UNCHANGED buf
    /\ UNCHANGED <<mem, pcM>>

\* The guard is held: the caller is inside the tree (try_split_inner, write_inner,
\* WriteGuard::insert, ...) dereferencing inner nodes.
Use ==
    /\ pcW = "use"
    /\ holds' = FALSE
    /\ pcW' = "done"
    /\ UNCHANGED <<buf, mem, pcM>>

\* Manager -------------------------------------------------------------------

\* :556 self.pause_snapshot.store(true, Release)
Pause ==
    /\ pcM = "pause"
    /\ IF FencedStores
       THEN /\ buf[M] = <<>>
            /\ mem' = [mem EXCEPT !.pause = 1]
            /\ UNCHANGED buf
       ELSE /\ buf' = [buf EXCEPT ![M] = Append(buf[M], [f |-> "pause", v |-> 1])]
            /\ UNCHANGED mem
    /\ pcM' = "drain"
    /\ UNCHANGED <<holds, pcW>>

\* :558 check_if_phase_completed(INVALID_SNAPSHOT_STATE): if every slot reads
\* INVALID the tree is considered frozen and phase 2 reclaims inner nodes.
Drain ==
    /\ pcM = "drain"
    /\ IF Load(M, "tls") = InvalidState
       THEN /\ mem' = [mem EXCEPT !.freed = 1]
            /\ pcM' = "done"
       ELSE /\ pcM' = "retry"
            /\ UNCHANGED mem
    /\ UNCHANGED <<buf, holds, pcW>>

\* The real code spins here. One retry is enough to show the loop does not
\* help: the decision was already taken on a stale read.
Retry ==
    /\ pcM = "retry"
    /\ pcM' = "drain"
    /\ UNCHANGED <<buf, mem, holds, pcW>>

Next ==
    \/ Early \/ Cas \/ Announce \/ Recheck \/ Use
    \/ Pause \/ Drain \/ Retry
    \/ (\E p \in Procs : Flush(p))

Spec == Init /\ [][Next]_vars

(***************************************************************************)
(* SAFETY: sweep must never reclaim an inner node while a worker still      *)
(* holds a slot and is inside the tree.                                     *)
(***************************************************************************)
NoUseAfterFree == ~ (mem.freed = 1 /\ holds)
=============================================================================
