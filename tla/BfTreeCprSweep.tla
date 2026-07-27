---------------------------- MODULE BfTreeCprSweep ----------------------------
(***************************************************************************)
(* Bf-Tree's CPR snapshot SWEEP FREEZE, on the x86-TSO model in X86TSO.tla. *)
(*                                                                         *)
(* Source: src/snapshot.rs                                                 *)
(*   Manager sweep                    STORE pause_snapshot = true          *)
(*                                    LOAD  thread_local_states[..]        *)
(*                                          (check_if_phase_completed)     *)
(*                                    then traverse the tree               *)
(*   Worker  reserve_thread_slot      LOAD  pause_snapshot (early out)     *)
(*                                    CAS   thread_slots[tid]              *)
(*                                    STORE thread_local_states[tid]       *)
(*                                    LOAD  pause_snapshot (re-check)      *)
(*                                                                         *)
(* Same StoreLoad window as BfTreeCprHandshake.tla, but here what follows   *)
(* the handshake is unsynchronised access to the tree. sweep's three-phase  *)
(* comment reads:                                                          *)
(*                                                                         *)
(*   Phase 1: Block all snapshot id reservation, drain the thread table.    *)
(*   Phase 2: Traverse the tree and take snapshots of inner nodes ...       *)
(*   Phase 3: Unblock snapshot id reservation.                              *)
(*                                                                         *)
(* Phase 1 is a store-then-load on both sides, so the drain can report an   *)
(* empty thread table while the worker is being handed a slot. The tree is  *)
(* then not frozen, and phase 2 walks it dereferencing raw *const InnerNode *)
(* pointers, twice noting "No need for WriteGuard as the tree structure is  *)
(* frozen and there are no active writers".                                 *)
(*                                                                         *)
(* `unsafeAccess` below stands for that phase-2 access. The invariant is    *)
(* that it never coincides with a live writer.                              *)
(*                                                                         *)
(* Fix values are as in BfTreeCprHandshake.tla: "None" -> VIOLATED,         *)
(* "SeqCstStores" -> HOLDS on x86 only.                                     *)
(***************************************************************************)
EXTENDS Integers, Sequences

CONSTANT Fix

W == "worker"
M == "manager"

Procs == {W, M}

\* pause = pause_snapshot
\* tls   = thread_local_states[tid]
\* slot  = thread_slots[tid]
Locs == {"pause", "tls", "slot"}

LiveState    == 0
InvalidState == 9      \* INVALID_SNAPSHOT_STATE

VARIABLES buf, mem, holds, unsafeAccess, pcW, pcM
vars == <<buf, mem, holds, unsafeAccess, pcW, pcM>>

TSO == INSTANCE X86TSO

FencedStores == Fix = "SeqCstStores"

Announce(p, loc, val) ==
    IF FencedStores THEN TSO!LockedStore(p, loc, val) ELSE TSO!Store(p, loc, val)

Init ==
    /\ TSO!TSOInit([l \in Locs |->
           IF l = "tls" THEN InvalidState ELSE 0])
    /\ holds = FALSE
    /\ unsafeAccess = FALSE
    /\ pcW = "early"
    /\ pcM = "pause"

DoFlush(p) ==
    /\ TSO!Flush(p)
    /\ UNCHANGED <<holds, unsafeAccess, pcW, pcM>>

\* Worker --------------------------------------------------------------------

\* if self.pause_snapshot.load(Acquire) { return Err(()) }
Early ==
    /\ pcW = "early"
    /\ IF TSO!Load(W, "pause") = 1 THEN pcW' = "done" ELSE pcW' = "cas"
    /\ UNCHANGED <<buf, mem, holds, unsafeAccess, pcM>>

\* compare_exchange(false, true, AcqRel, Relaxed). A LOCKed RMW, hence a full
\* barrier -- but it precedes the announce store, so it orders nothing here.
Cas ==
    /\ pcW = "cas"
    /\ TSO!Load(W, "slot") = 0
    /\ TSO!Rmw(W, "slot", 1)
    /\ pcW' = "announce"
    /\ UNCHANGED <<holds, unsafeAccess, pcM>>

\* set_local_state: announce that this slot is live.
DoAnnounce ==
    /\ pcW = "announce"
    /\ Announce(W, "tls", LiveState)
    /\ pcW' = "recheck"
    /\ UNCHANGED <<holds, unsafeAccess, pcM>>

\* || self.pause_snapshot.load(Acquire)  -> roll back, else the slot is granted
\* and the caller may mutate the tree structure.
Recheck ==
    /\ pcW = "recheck"
    /\ IF TSO!Load(W, "pause") = 1
       THEN /\ holds' = FALSE
            /\ TSO!Store(W, "tls", InvalidState)
            /\ pcW' = "done"
       ELSE /\ holds' = TRUE
            /\ UNCHANGED <<buf, mem>>
            /\ pcW' = "use"
    /\ UNCHANGED <<unsafeAccess, pcM>>

\* The slot is held: the caller is inside the tree (try_split_inner,
\* write_inner, WriteGuard::insert, ...) mutating inner nodes.
Use ==
    /\ pcW = "use"
    /\ holds' = FALSE
    /\ pcW' = "done"
    /\ UNCHANGED <<buf, mem, unsafeAccess, pcM>>

\* Manager -------------------------------------------------------------------

\* self.pause_snapshot.store(true, Release)
Pause ==
    /\ pcM = "pause"
    /\ Announce(M, "pause", 1)
    /\ pcM' = "drain"
    /\ UNCHANGED <<holds, unsafeAccess, pcW>>

\* check_if_phase_completed(INVALID_SNAPSHOT_STATE): if every slot reads
\* INVALID the tree is considered frozen and phase 2 walks it without guards.
Drain ==
    /\ pcM = "drain"
    /\ IF TSO!Load(M, "tls") = InvalidState
       THEN /\ unsafeAccess' = TRUE
            /\ pcM' = "done"
       ELSE /\ UNCHANGED unsafeAccess
            /\ pcM' = "retry"
    /\ UNCHANGED <<buf, mem, holds, pcW>>

\* The real code spins here. One retry is enough to show the loop does not
\* help: the decision was already taken on a stale read.
Retry ==
    /\ pcM = "retry"
    /\ pcM' = "drain"
    /\ UNCHANGED <<buf, mem, holds, unsafeAccess, pcW>>

Next ==
    \/ Early \/ Cas \/ DoAnnounce \/ Recheck \/ Use
    \/ Pause \/ Drain \/ Retry
    \/ (\E p \in Procs : DoFlush(p))

Spec == Init /\ [][Next]_vars

(***************************************************************************)
(* SAFETY: sweep must never touch the tree structure unguarded while a      *)
(* worker still holds a slot and is inside the tree.                        *)
(***************************************************************************)
NoUnguardedAccess == ~ (unsafeAccess /\ holds)
===============================================================================
