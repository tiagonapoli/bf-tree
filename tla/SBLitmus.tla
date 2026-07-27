------------------------------- MODULE SBLitmus -------------------------------
(***************************************************************************)
(* The classic store-buffer (SB) litmus, on top of X86TSO.tla.              *)
(*                                                                         *)
(*   initially x = y = 0                                                    *)
(*                                                                         *)
(*     Core 1            Core 2                                            *)
(*       x <- 1            y <- 1                                          *)
(*       r1 <- y           r2 <- x                                         *)
(*                                                                         *)
(* Under sequential consistency at least one core must see the other's      *)
(* store, so `r1 = 0 /\ r2 = 0` is impossible. Under x86-TSO both stores    *)
(* can still be sitting in their own buffers when the loads execute, so it  *)
(* is permitted -- and Intel's own manual lists exactly this as allowed.    *)
(*                                                                         *)
(* This module exists to validate X86TSO.tla before anything is built on    *)
(* top of it. A memory model that did not admit this outcome would be too   *)
(* strong, and one that admitted it even with fences would be too weak, so  *)
(* both configurations are checked:                                        *)
(*                                                                         *)
(*   Fenced = FALSE  ->  VIOLATED  (the model does permit StoreLoad)        *)
(*   Fenced = TRUE   ->  HOLDS     (MFENCE closes it, and nothing else is   *)
(*                                  quietly closing it already)             *)
(*                                                                         *)
(* The Bf-Tree specs are the same shape with the two cores doing real work: *)
(* `x`/`y` become `global_state` and `thread_local_states[tid]`, and the    *)
(* forbidden outcome becomes "the manager declared the phase complete while *)
(* a reservation was still outstanding".                                    *)
(***************************************************************************)
EXTENDS Integers, Sequences

CONSTANT Fenced

P1 == "core1"
P2 == "core2"

Procs == {P1, P2}
Locs  == {"x", "y"}

VARIABLES buf, mem, r1, r2, pc
vars == <<buf, mem, r1, r2, pc>>

TSO == INSTANCE X86TSO

\* The location each core writes, and the one it then reads.
Writes(p) == IF p = P1 THEN "x" ELSE "y"
Reads(p)  == IF p = P1 THEN "y" ELSE "x"

Init ==
    /\ TSO!TSOInit([l \in Locs |-> 0])
    /\ r1 = -1
    /\ r2 = -1
    /\ pc = [p \in Procs |-> "store"]

DoStore(p) ==
    /\ pc[p] = "store"
    /\ TSO!Store(p, Writes(p), 1)
    /\ pc' = [pc EXCEPT ![p] = IF Fenced THEN "fence" ELSE "load"]
    /\ UNCHANGED <<r1, r2>>

DoFence(p) ==
    /\ pc[p] = "fence"
    /\ TSO!Fence(p)
    /\ pc' = [pc EXCEPT ![p] = "load"]
    /\ UNCHANGED <<r1, r2>>

DoLoad(p) ==
    /\ pc[p] = "load"
    /\ IF p = P1
       THEN /\ r1' = TSO!Load(p, Reads(p))
            /\ UNCHANGED r2
       ELSE /\ r2' = TSO!Load(p, Reads(p))
            /\ UNCHANGED r1
    /\ pc' = [pc EXCEPT ![p] = "done"]
    /\ UNCHANGED <<buf, mem>>

DoFlush(p) ==
    /\ TSO!Flush(p)
    /\ UNCHANGED <<r1, r2, pc>>

Next == \E p \in Procs : DoStore(p) \/ DoFence(p) \/ DoLoad(p) \/ DoFlush(p)

Spec == Init /\ [][Next]_vars

SequentiallyConsistent == ~ (r1 = 0 /\ r2 = 0)
===============================================================================
