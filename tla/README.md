# TLA+ models of the CPR snapshot handshake

An explicit **x86-TSO** memory model, and two specs that model the
`CPRSnapShotMgr` handshake in [`src/snapshot.rs`](../src/snapshot.rs) on top of
it and check it exhaustively with TLC.

They exist to answer one question precisely: *is the `Release`/`Acquire` pairing
in the snapshot handshake sufficient, or is `SeqCst` required?*

## Layout

| File | |
| --- | --- |
| `X86TSO.tla` | the memory model, on its own and reusable — per-core FIFO store buffers over a shared memory, with store forwarding |
| `SBLitmus.tla` | the classic store-buffer litmus, built on `X86TSO`. Validates the model before anything is built on it |
| `BfTreeCprHandshake.tla` | the phase transition (`advance_global_state` vs the announce + double-check) |
| `BfTreeCprSweep.tla` | the sweep freeze (`pause_snapshot` vs the same announce) |

`X86TSO.tla` declares `buf` and `mem` and exports `Load`, `Store`,
`LockedStore`, `Rmw`, `Fence`, `Flush` and `Drained`. A spec builds on it by
defining `Procs` and `Locs`, declaring the two variables, and writing

```tla
TSO == INSTANCE X86TSO
```

after which `TSO!Load(W, "gs")` and `TSO!Store(M, "gs", NewState)` are the only
things that touch memory. Nothing models ordering by hand.

The whole model is: a store lands in the issuing core's private FIFO buffer and
becomes visible to others only when it drains; a load takes the newest value
that core has buffered for the location, else memory. That single fact is why
StoreLoad is the one reordering x86 permits, and it is the entire bug.

`SBLitmus` is checked in both directions, because a memory model that failed to
admit the SB outcome would be too strong to trust, and one that admitted it
*even with fences* would be too weak:

| config | expectation |
| --- | --- |
| `Fenced = FALSE` | **VIOLATED** — the model does permit StoreLoad |
| `Fenced = TRUE` | HOLDS — `MFENCE` closes it, and nothing else was quietly closing it |

## Running

```sh
docker build -f tla/Dockerfile -t bftree-tla tla
docker run --rm bftree-tla
```

Or, with `tla2tools.jar` already on disk:

```sh
TLA_TOOLS=/path/to/tla2tools.jar tla/run.sh
```

## Results

| Spec | config | Invariant | Result |
| --- | --- | --- | --- |
| `SBLitmus` | `Fenced = FALSE` | `SequentiallyConsistent` | **VIOLATED** |
| `SBLitmus` | `Fenced = TRUE` | `SequentiallyConsistent` | HOLDS |
| `BfTreeCprHandshake` | `Fix = "None"` — upstream `Release`/`Acquire` | `PhaseCompletionIsSound` | **VIOLATED** |
| `BfTreeCprHandshake` | `Fix = "SeqCstStores"` | `PhaseCompletionIsSound` | HOLDS *(x86 only — see below)* |
| `BfTreeCprSweep` | `Fix = "None"` — upstream `Release`/`Acquire` | `NoUnguardedAccess` | **VIOLATED** |
| `BfTreeCprSweep` | `Fix = "SeqCstStores"` | `NoUnguardedAccess` | HOLDS *(x86 only — see below)* |

## What the counterexample looks like

`BfTreeCprHandshake` with `Fix = "None"`:

| # | Action | What happens |
| --- | --- | --- |
| 1 | `Advance` | Manager's `global_state.store(new, Release)` — a plain `MOV`, so it sits in the manager's store buffer |
| 2 | `Cas` | Worker takes a thread slot |
| 3 | `Scan` | Manager's `check_if_phase_completed` reads `thread_local_states`, still `INVALID` → declares the phase complete |
| 4 | `Read` | Worker loads `global_state` → still the **old** value (the store is buffered) |
| 5 | `DoAnnounce` | Worker stores the old state into its slot |
| 6 | `Check` | Worker's double-check loads `global_state` → **still** the old value → the values match, so the worker commits |

The manager has moved to the new phase and believes nobody is left in the old
one, while the worker is live in the old phase. Both sides store to their own
location and then load the other's — precisely `SBLitmus` with the two cores
doing real work. The `compare_exchange(AcqRel)` *is* a full barrier, but it sits
**before** the announce store, so it orders nothing that matters here.

`BfTreeCprSweep` is the same shape with a worse consequence: `sweep`'s phase 1
declares the tree frozen, then phase 2 walks it dereferencing raw
`*const InnerNode` pointers, twice noting *"No need for WriteGuard as the tree
structure is frozen and there are no active writers"*, while a writer still
holds a slot.

## Why `"SeqCstStores"` HOLDS here but is not a valid fix

These specs model the **machine**. On x86-64 `rustc` lowers a `SeqCst` store to
`XCHG` — a `LOCK`ed RMW that drains the store buffer — so promoting only the
stores does close the window in hardware, and TLC reports HOLDS.

That is a fact about x86 codegen, not about the **language**. Rust's memory
model is not x86-TSO: the `SeqCst` total order constrains `SeqCst` operations
only, so an `Acquire` load on either side is not part of it and the reordering
remains permitted. Both [GenMC](https://github.com/MPI-SWS/genmc) under C11/RC11
and Miri agree, and disagree with TLC here:

| stores | paired loads | GenMC (RC11) | Miri | TLC (x86-TSO) |
| --- | --- | --- | --- | --- |
| `Release` | `Acquire` | violation | fails | VIOLATED |
| `SeqCst` | `Acquire` | violation | fails | *HOLDS* |
| `Release` | `SeqCst` | violation | fails | — |
| `SeqCst` | `SeqCst` | clean | passes | HOLDS |

Every row is correct at its own level. The fix has to satisfy the language,
which is why the `SEQ_CST NEEDED HERE` comments in `src/snapshot.rs` call for
`SeqCst` on the stores **and** the paired loads (or an explicit `fence(SeqCst)`
between each store and the load that follows it).

## Relation to the Miri tests

[`src/snapshot/cpr_handshake_miri.rs`](../src/snapshot/cpr_handshake_miri.rs)
drives the real `CPRSnapShotMgr` under Miri's weak-memory emulation and observes
the same two failures. Miri *samples* executions, so it is evidence; TLC and
GenMC exhaustively explore their models, so they are proofs — of the model.

## Note on ARM64

`Release`/`Acquire` lower to `STLR`/`LDAR` on AArch64, and ARMv8's RCsc
semantics forbid `STLR` → `LDAR` reordering. ARM64 is therefore accidentally
safe here. **This is an x86-64 bug.**

