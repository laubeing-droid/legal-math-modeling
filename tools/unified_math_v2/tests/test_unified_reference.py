"""Synthetic mathematical checks only; never evidence of legal/empirical truth."""
import itertools
import unittest
from fractions import Fraction as Q

from reference.unified_reference import (
    BinaryBN, BinaryNode, SearchResult, bic_regret, brier, demo,
    dirichlet_predictive, dung_member, evsi, exact_simple_interest,
    expected_outcome_bounds, model_envelope, partial_posterior_bounds,
    powerset, scan, settlement_point, verify_partition,
)


def example(prior=Q(3, 5)):
    return BinaryBN((BinaryNode("A", (), {(): prior}),
                     BinaryNode("E", ("A",), {(False,): Q(1, 5), (True,): Q(4, 5)})))


class SolutionTests(unittest.TestCase):
    def test_complete_equality(self):
        result = scan(tuple(range(12)), lambda x: x % 3 == 0)
        self.assertTrue(result.complete)
        self.assertEqual(result.found, frozenset({0, 3, 6, 9}))
        self.assertTrue(verify_partition(tuple(range(12)), result, lambda x: x in {0, 3, 6, 9}))

    def test_partial_empty_is_not_no_solution(self):
        result = scan((1, 2, 3), lambda x: x == 3, budget=1)
        self.assertEqual(result.found, frozenset())
        self.assertFalse(result.complete)
        self.assertEqual(result.pending, frozenset({2, 3}))

    def test_unknown_stays_pending(self):
        result = scan((1, 2), lambda x: None if x == 1 else True)
        self.assertEqual(result.pending, frozenset({1}))
        self.assertNotIn(1, result.rejected)
        self.assertFalse(result.complete)

    def test_forged_complete_rejected(self):
        bad = SearchResult(frozenset({2}), frozenset({1}), frozenset(), True)
        self.assertFalse(verify_partition((1, 2, 3), bad, lambda x: x == 2))

    def test_duplicate_carrier_rejected(self):
        with self.assertRaises(ValueError):
            scan((1, 1), lambda _: True)

    def test_mislabeled_member_rejected(self):
        bad = SearchResult(frozenset({1}), frozenset({2}), frozenset(), True)
        self.assertFalse(verify_partition((1, 2), bad, lambda x: x == 2))

    def test_powerset_complete(self):
        family = powerset(("a", "b", "c"))
        self.assertEqual(len(set(family)), 8)
        self.assertIn(frozenset(), family)
        self.assertIn(frozenset({"a", "b", "c"}), family)

    def test_prefix_maximal_is_not_preferred(self):
        self.assertFalse(dung_member("preferred", ("a", "b"), frozenset(), frozenset({"a"})))
        self.assertTrue(dung_member("preferred", ("a", "b"), frozenset(), frozenset({"a", "b"})))

    def test_stable_attack_direction(self):
        edges = frozenset({("a", "b")})
        self.assertTrue(dung_member("stable", ("a", "b"), edges, frozenset({"a"})))
        self.assertFalse(dung_member("stable", ("a", "b"), edges, frozenset({"b"})))

    def test_no_stable_extension_for_three_cycle(self):
        args = ("a", "b", "c")
        edges = frozenset({("a", "b"), ("b", "c"), ("c", "a")})
        result = scan(powerset(args), lambda s: dung_member("stable", args, edges, s))
        self.assertTrue(result.complete)
        self.assertFalse(result.found)

    def test_singleton_empty_extension_distinct(self):
        for profile in ("grounded", "stable", "preferred", "complete"):
            result = scan(powerset(()), lambda s: dung_member(profile, (), frozenset(), s))
            self.assertEqual(result.found, frozenset({frozenset()}))
            self.assertNotEqual(result.found, frozenset())

    def test_all_three_node_graphs_structural_invariants(self):
        args = ("a", "b", "c")
        edge_domain = tuple(itertools.product(args, repeat=2))
        family = powerset(args)
        for edges in powerset(edge_domain):
            results = {}
            for profile in ("grounded", "preferred", "complete", "stable"):
                full = scan(family, lambda s: dung_member(profile, args, edges, s))
                partial = scan(family, lambda s: dung_member(profile, args, edges, s), budget=3)
                self.assertTrue(partial.found <= full.found)
                self.assertTrue(full.complete)
                for s in full.found:
                    self.assertFalse(any(a in s and b in s for a, b in edges))
                results[profile] = full.found
            self.assertEqual(len(results["grounded"]), 1)
            self.assertTrue(results["grounded"] <= results["complete"])
            self.assertTrue(results["preferred"] <= results["complete"])
            self.assertTrue(results["stable"] <= results["preferred"])


class ProbabilityTests(unittest.TestCase):
    def test_joint_normalized(self):
        values = example().joint().values()
        self.assertEqual(sum(values), 1)
        self.assertTrue(all(p >= 0 for p in values))

    def test_posterior_exact_fraction(self):
        self.assertEqual(example().posterior({"A": True}, {"E": True}), Q(6, 7))

    def test_elimination_equals_enumeration(self):
        model = BinaryBN((
            BinaryNode("A", (), {(): Q(2, 5)}),
            BinaryNode("B", ("A",), {(False,): Q(1, 3), (True,): Q(3, 4)}),
            BinaryNode("C", ("A", "B"), {
                (False, False): Q(1, 9), (False, True): Q(2, 7),
                (True, False): Q(3, 5), (True, True): Q(9, 10)}),
        ))
        names = ("A", "B", "C")
        for keys in powerset(names):
            keys = tuple(sorted(keys))
            for values in itertools.product((False, True), repeat=len(keys)):
                evidence = dict(zip(keys, values))
                self.assertEqual(model.mass_by_elimination(evidence), model.mass_by_enumeration(evidence))
                for name in names:
                    self.assertEqual(model.posterior({name: True}, evidence),
                                     model.posterior({name: True}, evidence, elimination=True))

    def test_zero_evidence_undefined(self):
        model = BinaryBN((BinaryNode("A", (), {(): Q(0)}),))
        with self.assertRaises(ValueError):
            model.posterior({"A": True}, {"A": True})

    def test_copied_evidence_does_not_double_count(self):
        model = BinaryBN(example().nodes + (
            BinaryNode("copy", ("E",), {(False,): Q(0), (True,): Q(1)}),))
        self.assertEqual(model.posterior({"A": True}, {"E": True, "copy": True}), Q(6, 7))
        self.assertNotEqual(Q(6, 7), Q(24, 25))  # Wrong independent-copy update.

    def test_bad_topology(self):
        with self.assertRaises(ValueError):
            BinaryBN((BinaryNode("E", ("A",), {(False,): Q(1, 5), (True,): Q(4, 5)}),))

    def test_incomplete_cpt(self):
        with self.assertRaises(ValueError):
            BinaryNode("E", ("A",), {(False,): Q(1, 5)})

    def test_float_probability_rejected(self):
        with self.assertRaises(TypeError):
            BinaryNode("A", (), {(): 0.6})

    def test_dirichlet_predictive_normalized(self):
        values = dirichlet_predictive((1, 1), (3, 1))
        self.assertEqual(values, (Q(2, 3), Q(1, 3)))
        self.assertEqual(sum(values), 1)

    def test_model_envelope(self):
        self.assertEqual(model_envelope((example(Q(2, 5)), example()), {"A": True}, {"E": True}),
                         (Q(8, 11), Q(6, 7)))

    def test_incompatible_model_not_dropped(self):
        zero = BinaryBN((BinaryNode("A", (), {(): Q(0)}),
                         BinaryNode("E", (), {(): Q(0)})))
        with self.assertRaises(ValueError):
            model_envelope((example(), zero), {"A": True}, {"E": True})

    def test_partial_mass_enclosure(self):
        a, b, r = Q(1, 5), Q(1, 10), Q(7, 10)
        low, high = partial_posterior_bounds(a, b, r)
        for i in range(9):
            for j in range(9 - i):
                x, y = r * i / 8, r * j / 8
                actual = (a + x) / (a + b + x + y)
                self.assertLessEqual(low, actual)
                self.assertLessEqual(actual, high)

    def test_no_positive_evidence_witness(self):
        with self.assertRaises(ValueError):
            partial_posterior_bounds(Q(0), Q(0), Q(1))


class AmountAndGameTests(unittest.TestCase):
    def test_partial_extrema_are_inner(self):
        complete, found = {10, 20, 40}, {20}
        self.assertLess(min(complete), min(found))
        self.assertLess(max(found), max(complete))
        self.assertNotIn(30, complete)  # interval membership does not prove feasibility.

    def test_multivalued_expectation_bounds(self):
        weights = {"w1": Q(1, 2), "w2": Q(1, 2)}
        values = {"w1": (10, 20), "w2": (20, 40)}
        self.assertEqual(expected_outcome_bounds(weights, values), (Q(15), Q(30)))

    def test_positive_mass_without_outcome_not_deleted(self):
        with self.assertRaises(ValueError):
            expected_outcome_bounds({"w1": Q(1, 2), "w2": Q(1, 2)}, {"w1": (10,)})

    def test_exact_segment_interest(self):
        self.assertEqual(exact_simple_interest(((1000, Q(1, 10), Q(1, 2)),
                                                (500, Q(1, 10), Q(1, 2)))), Q(75))

    def test_settlement_point_individually_rational(self):
        point = settlement_point(100, 200, Q(2, 5))
        self.assertEqual(point, 140)
        self.assertTrue(100 <= point <= 200)

    def test_empty_settlement_interval(self):
        with self.assertRaises(ValueError):
            settlement_point(200, 100, Q(1, 2))

    def _mechanism(self, constant=False):
        types, outcomes = (("low", "high"),), ("zero", "one")
        prior = {("low",): Q(1, 2), ("high",): Q(1, 2)}
        mechanism = {("low",): {"zero": Q(1), "one": Q(0)},
                     ("high",): {"zero": Q(1 if constant else 0), "one": Q(0 if constant else 1)}}
        utility = {(0, t, o): Q(o == "one") for t in types[0] for o in outcomes}
        return types, outcomes, prior, mechanism, utility

    def test_constant_mechanism_bic(self):
        self.assertEqual(bic_regret(*self._mechanism(constant=True)), 0)

    def test_profitable_misreport_detected(self):
        self.assertEqual(bic_regret(*self._mechanism()), 1)

    def test_zero_probability_type_rejected(self):
        values = list(self._mechanism())
        values[2] = {("low",): Q(1), ("high",): Q(0)}
        with self.assertRaises(ValueError):
            bic_regret(*values)

    def test_positive_information_value(self):
        joint = {("signal0", "y0"): Q(1, 2), ("signal1", "y1"): Q(1, 2)}
        utilities = {"a0": {"y0": 100, "y1": 0}, "a1": {"y0": 0, "y1": 100}}
        self.assertEqual(evsi(joint, utilities), 50)
        self.assertEqual(evsi(joint, utilities, cost=10), 40)

    def test_single_action_information_value_zero(self):
        self.assertEqual(evsi({("z0", "y0"): Q(1, 2), ("z1", "y1"): Q(1, 2)},
                              {"a": {"y0": 10, "y1": 20}}), 0)

    def test_brier(self):
        self.assertEqual(brier((Q(1, 2), Q(1, 4)), (1, 0)), Q(5, 32))

    def test_demo_label_and_exact_output(self):
        result = demo()
        self.assertEqual(result["expected_amount_yuan"], "3125000/7")
        self.assertEqual(result["lean_status"], "CI_NOT_RUN")
        self.assertEqual(result["status"], "SYNTHETIC_MATHEMATICAL_REFERENCE")


if __name__ == "__main__":
    unittest.main()
