# TLA+ models of the CPR snapshot handshake

Two specs that model the `CPRSnapShotMgr` handshake in [`src/snapshot.rs`](../src/snapshot.rs)
on top of an explicit **x86-TSO** memory model (per-core FIFO store buffers with
store forwarding), and check it for safety.

They exist to answer one question precisely: *is the `Release`/`Acquire` pairing
in the snapshot handshake sufficient, or is `SeqCst` required?*

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

| Spec | `Fix` | Invariant | Result |
| --- | --- | --- | --- |
| `BfTreeCprHandshake` | `"None"` — upstream `Release`/`Acquire` | `PhaseCompletionIsSound` | **VIOLATED** |
| `BfTreeCprHandshake` | `"SeqCstStores"` | `PhaseCompletionIsSound` | HOLDS *(x86 only — see below)* |
| `BfTreeCprSweep` | `"None"` — upstream `Release`/`Acquire` | `NoUseAfterFree` | **VIOLATED** |
| `BfTreeCprSweep` | `"SeqCstStores"` | `NoUseAfterFree` | HOLDS *(x86 only — see below)* |

## What the counterexample looks like

`BfTreeCprHandshake` with `Fix = "None"`, six steps:

| # | Action | What happens |
| --- | --- | --- |
| 2 | `Advance` | Manager's `global_state.store(new, Release)` — a plain `MOV`, so it sits in the manager's store buffer |
| 3 | `Cas` | Worker takes a thread slot |
| 4 | `Scan` | Manager's `check_if_phase_completed` reads `thread_local_states`, still `INVALID` → declares the phase complete |
| 5 | `Read` | Worker loads `global_state` → still the **old** value (the store is buffered) |
| 6 | `Announce` | Worker stores the old state into its slot |
| 7 | `Check` | Worker's `:432` double-check loads `global_state` → **still** the old value → the values match, so the worker commits |

The manager has moved to the new phase and believes nobody is left in the old
one, while the worker is live in the old phase. Both sides store to their own
location and then load the other's — the [store-buffer (SB)
litmus](https://www.cl.cam.ac.uk/~pes20/weakmemory/), which x86-TSO permits.
The `:415` `compare_exchange(AcqRel)` *is* a full barrier, but it sits **before**
the announce store, so it orders nothing that matters here.

`BfTreeCprSweep` is the same shape with a destructive consequence: `sweep`'s
phase 1 declares the tree frozen, then phase 2 traverses and reclaims inner
nodes while a writer still holds a slot.

## Why `"SeqCstStores"` HOLDS here but is not a valid fix

These specs model the **machine**. On x86-64 `rustc` lowers a `SeqCst` store to
`XCHG` — a `LOCK`ed RMW that drains the store buffer — so promoting only the
stores does close the window in hardware, and TLC reports HOLDS.

That is a fact about x86 codegen, not about the **language**. Rust's memory
model is not x86-TSO: the `SeqCst` total order constrains `SeqCst` operations
only, so an `Acquire` load on either side is not part of it and the reordering
remains permitted. Checking the same handshake under C11/RC11 with
[GenMC](https://github.com/MPI-SWS/genmc) confirms it:

| stores | paired loads | GenMC verdict |
| --- | --- | --- |
| `Release` | `Acquire` | safety violation |
| `SeqCst` | `Acquire` | safety violation |
| `Release` | `SeqCst` | safety violation |
| `SeqCst` | `SeqCst` | no errors |

The disagreement is the point: TLC says what this hardware does, GenMC says what
the language promises, and a fix has to satisfy the language. Hence the
`SEQ_CST NEEDED HERE` comments in `src/snapshot.rs` call for `SeqCst` on the
stores **and** the paired loads (or an explicit `fence(SeqCst)` between each
store and the load that follows it).

## Relation to the Miri tests

[`src/snapshot/cpr_handshake_miri.rs`](../src/snapshot/cpr_handshake_miri.rs)
drives the real `CPRSnapShotMgr` under Miri's weak-memory emulation and observes
the same two failures. Miri *samples* executions, so it is evidence; TLC and
GenMC exhaustively explore their models, so they are proofs — of the model.

## Note on ARM64

`Release`/`Acquire` lower to `STLR`/`LDAR` on AArch64, and ARMv8's RCsc
semantics forbid `STLR` → `LDAR` reordering. ARM64 is therefore accidentally
safe here. **This is an x86-64 bug.**
