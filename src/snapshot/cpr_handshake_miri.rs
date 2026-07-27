// Copyright (c) Microsoft Corporation.
// Licensed under the MIT license.

//! Miri litmus tests for the CPR phase handshake in the parent module.
//!
//! Both tests drive the real `CPRSnapShotMgr`; the handshake itself is not
//! re-modelled here. They are compiled only under `cfg(miri)`, so a normal
//! `cargo test` never sees them.
//!
//! ```text
//! cargo +nightly miri test --lib snapshot::cpr_handshake_miri
//! ```
//!
//! # The shape of the bug
//!
//! The manager and a worker each store to their own location and then load the
//! other's, all under `Release`/`Acquire`:
//!
//! ```text
//!   Worker (`reserve_thread_slot`)         Manager
//!     STORE thread_local_states[tid]         STORE global_state / pause_snapshot
//!     LOAD  global_state / pause_snapshot    LOAD  thread_local_states[..]
//! ```
//!
//! `Release`/`Acquire` orders each thread's own accesses against that thread's
//! own release/acquire pairs, but it establishes nothing between two threads
//! that never synchronise on a common location. Neither load is required to
//! observe the other thread's store, so both can miss both. The manager then
//! reports the phase complete while a reservation is still outstanding in the
//! phase it just left -- exactly the interleaving the comment in
//! `reserve_thread_slot` says the double-check prevents.
//!
//! # What these tests do and do not establish
//!
//! Miri *samples* executions of the C++11-style weak memory model rather than
//! enumerating them, so a failure is evidence that the outcome is permitted,
//! and a clean run is not a proof that it is forbidden. Neither test says
//! anything about a specific ISA: Miri works on the language model, not on
//! x86-64 lowering. The claims about x86-64 store buffers, about ARM64 being
//! accidentally safe (`stlr`/`ldar` under RCsc), and about `SeqCst` being
//! required on both sides rather than on the stores alone come from the TLA+
//! x86-TSO models in `tla/` and from GenMC under RC11, both of which are
//! exhaustive.
//!
//! # Controls
//!
//! `ITERATIONS = 300`, on x86-64, `rustc` nightly.
//!
//! | `MIRIFLAGS` | source | test 1 | test 2 |
//! | --- | --- | --- | --- |
//! | `-Zmiri-seed=0..3` | as-is | assertion fires | UB: dangling reference (use-after-free) |
//! | `-Zmiri-seed=0..3 -Zmiri-disable-weak-memory-emulation` | as-is | passes | passes |
//! | `-Zmiri-seed=0..3` | every ordering promoted to `SeqCst` | passes | passes |
//!
//! The middle row is the load-bearing one. With weak memory emulation off Miri
//! still explores thread interleavings, but every atomic load reads the latest
//! value, so a failure there would indicate an ordinary scheduling bug. Both
//! tests pass in that configuration and fail with it on, under the same seeds
//! and the same source, which isolates the cause to weak memory rather than to
//! scheduling. `-Zmiri-track-weak-memory-loads` confirms it directly:
//!
//! ```text
//! note: weak memory emulation: outdated value returned from load at 0x...
//! ```
//!
//! Test 1's assertion is also unreachable under sequential consistency by
//! construction; see its doc comment.

use super::*;
use std::sync::atomic::Ordering;
use std::sync::mpsc;
use std::sync::Arc;
use std::thread;

/// Miri samples weak-memory behaviours rather than enumerating them, so each
/// litmus runs repeatedly. Both violations normally surface in the first few
/// iterations; see the control table above for the seeds this was checked on.
const ITERATIONS: usize = 300;

/// A raw pointer that can cross a thread boundary with its provenance intact.
///
/// Casting through `usize` would also compile, but it exposes the allocation
/// and hands the other thread a wildcard-provenance pointer, which weakens
/// Miri's aliasing checks and muddies the diagnostic. Passing the pointer
/// itself keeps the experiment about ordering and nothing else.
/// Derived `Clone`/`Copy` would add a `T: Copy` bound, which the pointee does
/// not satisfy; a pointer is `Copy` regardless of what it points to.
struct SendPtr<T>(*mut T);

impl<T> Clone for SendPtr<T> {
    fn clone(&self) -> Self { *self }
}

impl<T> Copy for SendPtr<T> {}

unsafe impl<T> Send for SendPtr<T> {}

/// A worker can commit to phase `x` after the manager has both advanced to
/// `x + 1` and satisfied itself that every thread is already there.
///
/// The manager's next act is to run the `x + 1` action against a tree that
/// still has an outstanding reservation from phase `x`.
///
/// # Why the assertion cannot fire under sequential consistency
///
/// The manager is the only writer of `global_state`, so under SC:
///
/// 1. `committed == old_state` means the worker's first `global_state` load
///    returned `old_state`, so that load precedes the manager's store.
/// 2. Reservation succeeded, so the worker's reload of its own slot equalled
///    its second `global_state` load. Coherence forces that reload to observe
///    the worker's own preceding announce store, so the second load also
///    returned `old_state` and likewise precedes the manager's store.
/// 3. The announce store sits between the two loads, so it too precedes the
///    manager's store.
/// 4. The manager's scan follows its own store, hence follows the announce, so
///    it must observe the slot holding `old_state` -- neither `INVALID` nor
///    `new_state` -- and `check_if_phase_completed` must return false.
///
/// So `phase_completed && committed == old_state` is unreachable under SC, and
/// a failure here cannot be explained by an ordinary thread schedule.
///
/// This establishes that the *reservation* was outstanding and committed to the
/// old state when the manager declared the phase complete. It does not
/// separately claim the worker thread was still physically executing.
#[test]
fn phase_can_complete_while_a_reservation_is_still_in_the_old_phase() {
    for iteration in 0..ITERATIONS {
        let mgr = Arc::new(CPRSnapShotMgr::new(0));
        let old_state = mgr.global_state.load(Ordering::Relaxed);

        let worker_mgr = mgr.clone();
        let worker = thread::spawn(move || worker_mgr.reserve_thread_slot().ok());

        let new_state = mgr.advance_global_state();
        let phase_completed = mgr.check_if_phase_completed(new_state);

        let Some((tid, version, phase_id)) = worker.join().unwrap() else {
            continue;
        };

        mgr.release_thread_slot(tid);

        let committed = CPRSnapShotMgr::new_snapshot_state(phase_id.as_raw(), version);
        assert!(
            !(phase_completed && committed == old_state),
            "iteration {iteration}: worker committed to the old state {old_state:#x}, \
             but the manager advanced to {new_state:#x} and reported the phase complete"
        );
    }
}

/// The freeze at the top of `sweep` has the same shape, and there the manager's
/// next act is to treat the tree as exclusively its own.
///
/// Once `check_if_phase_completed(INVALID_SNAPSHOT_STATE)` returns, `sweep`
/// walks the tree dereferencing raw `*const InnerNode` pointers and copying
/// each node, twice noting *"No need for WriteGuard as the tree structure is
/// frozen and there are no active writers"*. Every one of those accesses is
/// justified solely by the freeze this test breaks.
///
/// # This half is synthetic
///
/// `sweep` reads and snapshots inner nodes; it does not itself free them, so
/// the `Box` below is **not** a literal reproduction of a `sweep` call site.
/// What the test establishes against the real manager is the antecedent -- that
/// the freeze can declare the tree quiescent while a reservation succeeds. The
/// `Box` then stands in for an unsafe action predicated on that declaration, so
/// that Miri renders the consequence as a diagnostic rather than leaving it as
/// prose. In `sweep` itself the consequence is an unsynchronised read of a node
/// that a live writer may be splitting.
///
/// The dereference is gated on a message sent after the manager has already
/// decided and acted, so that whenever the freeze is unsound the outcome is a
/// deterministic use-after-free rather than a race the worker might win.
#[test]
fn sweep_freeze_can_admit_a_reservation_after_declaring_the_tree_frozen() {
    struct InnerNodeStandIn {
        magic: u64,
    }

    const MAGIC: u64 = 0x5AFE_0000_5AFE;

    for _ in 0..ITERATIONS {
        let mgr = Arc::new(CPRSnapShotMgr::new(0));
        let node = SendPtr(Box::into_raw(Box::new(InnerNodeStandIn { magic: MAGIC })));

        // Signals that the manager has finished its freeze decision and acted
        // on it. Nothing is ever sent to the manager, so the handshake window
        // itself gains no synchronisation.
        let (decided_tx, decided_rx) = mpsc::channel::<()>();

        let worker_mgr = mgr.clone();
        let worker = thread::spawn(move || {
            // Capture the whole `SendPtr`, not its field: RFC 2229 would
            // otherwise capture the bare `*mut T`, which is not `Send`.
            let node = node;

            let Ok((tid, _, _)) = worker_mgr.reserve_thread_slot() else {
                return;
            };

            // Holding a slot means the tree is not frozen, so by the protocol
            // this node is live and `sweep` cannot have touched it.
            let _ = decided_rx.recv();
            let n = unsafe { &*node.0 };
            assert_eq!(n.magic, MAGIC);

            worker_mgr.release_thread_slot(tid);
        });

        // `sweep` phase 1: block all reservations, then drain the thread table.
        mgr.pause_snapshot.store(true, Ordering::Release);
        let frozen = mgr.check_if_phase_completed(INVALID_SNAPSHOT_STATE);
        if frozen {
            drop(unsafe { Box::from_raw(node.0) });
        }

        // Only now may the worker act on the slot it was granted.
        let _ = decided_tx.send(());

        worker.join().unwrap();

        if !frozen {
            drop(unsafe { Box::from_raw(node.0) });
        }
    }
}
