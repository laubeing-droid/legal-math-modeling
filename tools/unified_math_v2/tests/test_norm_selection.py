"""WP-2 tests: norm-selection full-solution semantics (plan §3.1–§3.2).

The A-beats-B-beats-C counterexample pins the contract: {A, C} is the
unique stable selection; a global-maximal screen that keeps only {A}
would drop the compatible candidate C and must fail this suite.
"""

from unittest import TestCase

import pytest

from unified.norm_selection import (
    MAX_CANDIDATES,
    NormCandidate,
    RenvoiMode,
    SelectionStatus,
    apply_override,
    enumerate_stable_selections,
    route_renvoi,
    strictest_common_actions,
)


def _cands(*ids):
    return tuple(NormCandidate(n, "CN") for n in ids)


class StableSelectionTests(TestCase):
    def test_abc_keeps_compatible_pair(self):
        result = enumerate_stable_selections(
            _cands("A", "B", "C"),
            frozenset({("A", "B"), ("B", "C")}),
        )
        # {A,C} satisfies: internally free, B excluded by A.  {A} alone is
        # INVALID: C ∉ S has no excluder — the exact counterexample to
        # global-maximal screening.
        self.assertEqual(result.status, SelectionStatus.RESOLVED)
        self.assertEqual(result.selections, (frozenset({"A", "C"}),))

    def test_isolated_candidate_must_be_adopted(self):
        result = enumerate_stable_selections(
            _cands("A", "B", "I"),
            frozenset({("A", "B")}),
        )
        self.assertEqual(
            result.selections,
            (frozenset({"A", "I"}),),
        )

    def test_two_isolated_candidates_single_solution(self):
        result = enumerate_stable_selections(_cands("I", "J"), frozenset())
        self.assertEqual(result.selections, (frozenset({"I", "J"}),))

    def test_authorized_same_rank_keeps_both_choices(self):
        result = enumerate_stable_selections(
            _cands("X", "Y"),
            frozenset({("X", "Y"), ("Y", "X")}),
        )
        self.assertEqual(
            result.selections, (frozenset({"X"}), frozenset({"Y"}))
        )

    def test_escalation_refers_instead_of_choosing(self):
        result = enumerate_stable_selections(
            _cands("X", "Y"),
            frozenset(),
            frozenset({frozenset({"X", "Y"})}),
        )
        self.assertIs(result.status, SelectionStatus.ESCALATE)
        self.assertEqual(result.selections, ())
        self.assertEqual(result.refer_pairs, (frozenset({"X", "Y"}),))

    def test_exclusion_cycle_is_conflict_not_wellformedness(self):
        result = enumerate_stable_selections(
            _cands("A", "B", "C"),
            frozenset({("A", "B"), ("B", "C"), ("C", "A")}),
        )
        self.assertIs(result.status, SelectionStatus.NORM_CONFLICT)

    def test_empty_candidates(self):
        result = enumerate_stable_selections((), frozenset())
        self.assertIs(result.status, SelectionStatus.EMPTY_CANDIDATES)

    def test_edge_outside_candidates_rejected(self):
        with pytest.raises(ValueError, match="outside candidate set"):
            enumerate_stable_selections(_cands("A"), frozenset({("A", "Z")}))

    def test_budget_guard(self):
        many = _cands(*[f"n{i}" for i in range(MAX_CANDIDATES + 1)])
        with pytest.raises(ValueError, match="exhaustive-enumeration budget"):
            enumerate_stable_selections(many, frozenset())

    def test_mutual_exclusion_pair_solutions(self):
        # Same-rank authorized choice mixed with an isolated candidate.
        result = enumerate_stable_selections(
            _cands("X", "Y", "I"),
            frozenset({("X", "Y"), ("Y", "X")}),
        )
        self.assertEqual(
            result.selections,
            (frozenset({"X", "I"}), frozenset({"Y", "I"})),
        )


class StrictestCommonTests(TestCase):
    def test_intersection_is_join(self):
        joined, empty = strictest_common_actions(
            [frozenset({"pay", "stop"}), frozenset({"pay", "inspect"})]
        )
        self.assertEqual(joined, frozenset({"pay"}))
        self.assertFalse(empty)

    def test_empty_intersection_is_infeasibility_not_invalidity(self):
        joined, empty = strictest_common_actions(
            [frozenset({"pay"}), frozenset({"stop"})]
        )
        self.assertTrue(empty)
        self.assertEqual(joined, frozenset())

    def test_requires_at_least_one_jurisdiction(self):
        with pytest.raises(ValueError):
            strictest_common_actions([])


class RenvoiTests(TestCase):
    def test_forbidden_applies_own_law(self):
        outcome = route_renvoi(RenvoiMode.FORBIDDEN, "CN", {"CN": "FR"})
        self.assertEqual(outcome.terminal, "CN")
        self.assertFalse(outcome.circular)

    def test_one_step_follows_single_remission(self):
        outcome = route_renvoi(RenvoiMode.ONE_STEP, "CN", {"CN": "FR"})
        self.assertEqual(outcome.terminal, "FR")
        self.assertEqual(outcome.visited, ("CN", "FR"))

    def test_traverse_stops_without_reference(self):
        outcome = route_renvoi(RenvoiMode.TRAVERSE, "CN", {"CN": "FR"})
        self.assertEqual(outcome.terminal, "FR")

    def test_traverse_detects_cycle(self):
        outcome = route_renvoi(
            RenvoiMode.TRAVERSE, "CN", {"CN": "FR", "FR": "DE", "DE": "CN"}
        )
        self.assertTrue(outcome.circular)
        self.assertIsNone(outcome.terminal)
        self.assertEqual(outcome.visited, ("CN", "FR", "DE"))


class OverrideTests(TestCase):
    def test_scope_restricted_replacement(self):
        old = (("sale", "ucc"), ("lease", "common"), ("secure", "ucc9"))
        new = apply_override(
            frozenset({"sale"}), old, ("sale", "ucc-2026")
        )
        self.assertIn(("sale", "ucc-2026"), new)
        self.assertIn(("lease", "common"), new)
        self.assertIn(("secure", "ucc9"), new)
        self.assertEqual(len(new), 3)

    def test_outside_scope_untouched_verbatim(self):
        old = (("a", "1"),)
        new = apply_override(frozenset({"other"}), old, ("a", "2"))
        self.assertEqual(new, (("a", "1"), ("a", "2")))
