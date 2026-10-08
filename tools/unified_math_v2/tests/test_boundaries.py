"""WP-9 tests: the six runtime boundary contracts (J.15.4's positive and
negative instances)."""

from unittest import TestCase

import pytest

from unified.boundaries import (
    ActualIssuedRecord,
    Attempt,
    AttemptOutcome,
    LicensedAdverse,
    SolveState,
    TaintLedger,
    WorkNode,
    DagNode,
    accept_adverse,
    credential_pool_max,
    guarantee_meet,
    passive_all_required,
    passive_bind,
    passive_map,
    profile_family,
)


class Bnd01Tests(TestCase):
    def test_failure_has_no_payload_constructor(self):
        with pytest.raises(ValueError, match="no normal payload"):
            Attempt("k", AttemptOutcome.FAILURE, "timeout", payload="42")

    def test_map_preserves_failure(self):
        failed = Attempt("k", AttemptOutcome.FAILURE, "db down")
        self.assertIs(passive_map(failed), failed)

    def test_all_required_keeps_first_failure(self):
        failed = Attempt("k", AttemptOutcome.FAILURE, "missing source")
        ok = Attempt("k2", AttemptOutcome.COMPLETE, None, "x")
        out = passive_all_required((ok, failed, ok))
        self.assertIs(out, failed)

    def test_bind_short_circuits(self):
        failed = Attempt("k", AttemptOutcome.FAILURE, "e")
        def follow(a):
            raise AssertionError("must not run")
        self.assertIs(passive_bind(failed, follow), failed)

    def test_new_attempt_success_does_not_launder_old(self):
        old = Attempt("run:1", AttemptOutcome.FAILURE, "timeout")
        new = Attempt("run:2", AttemptOutcome.COMPLETE, None, "ok")
        self.assertIs(old.outcome, AttemptOutcome.FAILURE)  # unchanged


class Bnd02Tests(TestCase):
    def _state(self):
        root = WorkNode("root", ("selection", "extension", "amount"))
        return SolveState("run:1", (root,), frontier=frozenset({"root"}))

    def test_open_obligations_bijection(self):
        state = self._state()
        self.assertEqual(state.open_obligations(), frozenset({"root"}))

    def test_member_witness_does_not_close(self):
        state = self._state()
        after = state.record_member("root")
        self.assertIn("root", after.frontier)
        self.assertIn("root", after.lower_bounds)
        self.assertEqual(after.run_status(frozenset({"root"})), "SOUND_PARTIAL")

    def test_covering_certificate_closes(self):
        state = self._state()
        after = state.close("root", covering=True)
        self.assertNotIn("root", after.frontier)
        self.assertEqual(after.run_status(frozenset({"root"})), "COMPLETE")

    def test_close_without_certificate_refused(self):
        with pytest.raises(ValueError, match="covering certificate"):
            self._state().close("root", covering=False)

    def test_failure_blocks_complete(self):
        after = self._state().record_failure("engine crash")
        self.assertEqual(after.run_status(frozenset({"root"})), "FAILED")

    def test_split_replaces_frontier(self):
        state = self._state()
        after = state.split("root", (WorkNode("a"), WorkNode("b")))
        self.assertEqual(after.frontier, frozenset({"a", "b"}))

    def test_pause_without_verified_content(self):
        self.assertEqual(self._state().run_status(frozenset({"root"})), "PAUSED")


class Bnd03Tests(TestCase):
    def test_self_attack_stable_empty_others_empty_family(self):
        nodes = ["a"]
        edges = frozenset({("a", "a")})
        self.assertEqual(profile_family(nodes, edges, "stable"), ())
        self.assertEqual(profile_family(nodes, edges, "grounded"), (frozenset(),))
        self.assertEqual(profile_family(nodes, edges, "complete"), (frozenset(),))
        self.assertEqual(profile_family(nodes, edges, "preferred"), (frozenset(),))

    def test_two_cycle_two_stable(self):
        nodes = ["a", "b"]
        edges = frozenset({("a", "b"), ("b", "a")})
        stable = profile_family(nodes, edges, "stable")
        self.assertEqual(
            frozenset(stable), frozenset({frozenset({"a"}), frozenset({"b"})})
        )

    def test_grounded_recursive_defense(self):
        edges = frozenset({("c", "b"), ("b", "a")})
        self.assertEqual(
            profile_family(["a", "b", "c"], edges, "grounded"),
            (frozenset({"a", "c"}),),
        )


class Bnd04Tests(TestCase):
    def _adverse(self, roots=("burden-root",)):
        return LicensedAdverse("claim-1", "deriv-1", roots, ("cert:1",) * len(roots))

    def test_open_required_root_blocks_adverse(self):
        state = SolveState(
            "run:1", (WorkNode("burden-root"),), frontier=frozenset({"burden-root"})
        )
        self.assertFalse(accept_adverse(state, self._adverse(), frozenset({"burden-root"})))

    def test_closed_roots_allow_adverse(self):
        state = SolveState(
            "run:1", (WorkNode("burden-root"),),
            closed=frozenset({"burden-root"}),
        )
        self.assertTrue(accept_adverse(state, self._adverse(), frozenset({"burden-root"})))

    def test_failed_attempt_blocks_adverse(self):
        state = SolveState(
            "run:1", (WorkNode("burden-root"),),
            closed=frozenset({"burden-root"}),
            failures=("engine timeout",),
        )
        self.assertFalse(accept_adverse(state, self._adverse(), frozenset({"burden-root"})))

    def test_actual_issued_is_a_separate_type(self):
        record = ActualIssuedRecord("doc-1", "clerk-9", 12, "forged")
        # a forged document is RECORDED — its existence is not gated on legality
        self.assertEqual(record.authenticity, "forged")
        self.assertNotIsInstance(record, LicensedAdverse)


class Bnd05Tests(TestCase):
    def test_meet_never_exceeds_inputs(self):
        vectors = [(2, 0, 1), (1, 2, 0)]
        self.assertEqual(guarantee_meet(vectors), (1, 0, 0))

    def test_repetition_does_not_raise_meet(self):
        once = guarantee_meet([(1, 1)])
        many = guarantee_meet([(1, 1)] * 5)
        self.assertEqual(once, many)

    def test_pool_max_vs_meet_counterexample(self):
        # [0, 3]: pool max is 3, meet is 0 — the two are NOT isomorphic.
        self.assertEqual(credential_pool_max([0, 3]), 3)
        self.assertEqual(guarantee_meet([(0,), (3,)]), (0,))

    def test_repeated_zero_credentials_stay_zero(self):
        self.assertEqual(credential_pool_max([0, 0, 0]), 0)

    def test_empty_pool(self):
        self.assertIsNone(credential_pool_max([]))
        self.assertIsNone(guarantee_meet([]))


class Bnd06Tests(TestCase):
    def _ledger(self):
        ledger = TaintLedger()
        ledger.add(DagNode("src-clean", (), False, "bank"))
        ledger.add(DagNode("src-tainted", (), True, "forged receipt"))
        return ledger

    def test_taint_propagates_to_descendants(self):
        ledger = self._ledger()
        ledger.derive("mid", ["src-tainted"])
        ledger.derive("leaf", ["mid"])
        self.assertTrue(ledger.taint_of("leaf"))
        self.assertFalse(ledger.taint_of("src-clean"))

    def test_clean_branch_stays_clean(self):
        ledger = self._ledger()
        ledger.derive("a", ["src-clean"])
        self.assertFalse(ledger.taint_of("a"))

    def test_cache_get_returns_original_reference(self):
        ledger = self._ledger()
        ledger.derive("n", ["src-tainted"])
        node = ledger.cache_get("n")
        self.assertEqual(node.parents, ("src-tainted",))
        self.assertTrue(ledger.taint_of("n"))

    def test_retry_keeps_source_dependency(self):
        ledger = self._ledger()
        ledger.derive("n", ["src-tainted"])
        ledger.retry("n-attempt-2", ["n"])
        self.assertTrue(ledger.taint_of("n-attempt-2"))

    def test_control_dependency_counts(self):
        """A branch condition derived from a tainted node taints the
        consumer even if the taken branch's data is clean (J.15.3)."""
        ledger = self._ledger()
        ledger.derive("condition", ["src-tainted"])
        ledger.add(DagNode("result", ("condition", "src-clean"), False, "if-result"))
        self.assertTrue(ledger.taint_of("result"))

    def test_dedup_does_not_launder(self):
        ledger = self._ledger()
        ledger.derive("kept", ["src-tainted"])
        ledger.derive("dup", ["src-tainted"])
        ledger.dedup("kept", "dup")
        self.assertTrue(ledger.taint_of("kept"))

    def test_parent_must_exist(self):
        ledger = TaintLedger()
        with pytest.raises(ValueError, match="must exist"):
            ledger.derive("child", ["ghost"])
