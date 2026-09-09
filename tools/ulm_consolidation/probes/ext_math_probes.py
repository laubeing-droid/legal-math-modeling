"""Small mathematical audit probes, not tests of LMM/JC production code.

Run: python math_probes.py
Python standard library only. Fractions avoid rounding in the finite examples.
An example passing is NOT a Lean theorem or a proof about all inputs.
"""
from __future__ import annotations

from fractions import Fraction as F
from itertools import combinations, product
from pathlib import Path
import json
import unittest


def powerset(items):
    items = tuple(items)
    return [frozenset(c) for n in range(len(items) + 1) for c in combinations(items, n)]


def stable_sets(nodes, edges):
    edges = set(edges)
    return frozenset(
        s for s in powerset(nodes)
        if not any(a in s and b in s for a, b in edges)
        and all(any((b, a) in edges for b in s) for a in set(nodes) - s)
    )


class MathematicalReviewProbes(unittest.TestCase):
    def test_01_projection_preimage_not_point_embedding(self):
        world = set(product([0, 1], [0, 100]))
        probability_constraint, money_constraint = {1}, {100}
        correct = {w for w in world if w[0] in probability_constraint and w[1] in money_constraint}
        point_image_p = {(p, 0) for p in probability_constraint}
        point_image_m = {(0, m) for m in money_constraint}
        wrong = point_image_p & point_image_m
        self.assertEqual(correct, {(1, 100)})
        self.assertEqual(wrong, set())

    def test_02_relation_cannot_be_recovered_from_marginal_intervals(self):
        grid = [F(i, 4) for i in range(5)]
        box = set(product(grid, grid))
        relation = {w for w in box if sum(w) == 1}
        self.assertEqual({x for x, _ in relation}, set(grid))
        self.assertEqual({y for _, y in relation}, set(grid))
        self.assertEqual({x+y for x, y in relation}, {F(1)})
        self.assertEqual(min(x+y for x,y in box), 0)
        self.assertEqual(max(x+y for x,y in box), 2)

    def test_03_upper_bound_can_be_tight_without_attainment(self):
        contains = lambda x: F(0) <= x < F(1)
        self.assertFalse(contains(F(1)))
        # General algebraic witness: x=1-min(epsilon/2,1/2).
        for eps in [F(1, 10000), F(1, 3), F(1), F(3)]:
            x = 1 - min(eps/2, F(1, 2))
            self.assertTrue(contains(x))
            self.assertGreater(x, 1-eps)
        # This probe samples the witness construction; the universal proof is in the report.

    def test_04_nonconvex_problem_has_exact_outer_certificate(self):
        objective = lambda x: (x*x - 1)**2
        # f(0)>[f(-1)+f(1)]/2: not convex on [-2,2].
        self.assertGreater(objective(F(0)), (objective(F(-1))+objective(F(1)))/2)
        # Sum-of-squares identity is the global lower-bound certificate; +/-1 attain it.
        for i in range(-40, 41):
            x = F(i, 20)
            self.assertEqual(objective(x), x**4 - 2*x*x + 1)
            self.assertGreaterEqual(objective(x), 0)
        self.assertEqual(objective(F(1)), 0)
        self.assertEqual(objective(F(-1)), 0)

    def test_05_two_defeasible_opposites_do_not_refute_extension_consistency(self):
        nodes = ('a', 'not-a')
        extensions = stable_sets(nodes, [('a', 'not-a'), ('not-a', 'a')])
        self.assertEqual(extensions, frozenset({frozenset({'a'}), frozenset({'not-a'})}))
        self.assertTrue(all(not {'a', 'not-a'} <= e for e in extensions))
        # The union of alternatives is inconsistent, not either extension.
        self.assertEqual(set().union(*extensions), {'a', 'not-a'})

    def test_06_minimal_supports_can_overlap_probabilistically(self):
        probability = sum(
            (F(1, 8) for x,y,z in product([False, True], repeat=3) if (x and y) or (x and z)),
            F(0),
        )
        each_path = F(1, 4)
        incorrect_independence = 1 - (1-each_path)**2
        self.assertEqual(probability, F(3, 8))
        self.assertEqual(incorrect_independence, F(7, 16))
        supports = [frozenset({'x','y'}), frozenset({'x','z'})]
        self.assertTrue(all(not a < b for a in supports for b in supports))
        self.assertTrue(bool(supports[0] & supports[1]))

    def test_07_boolean_idempotence_is_not_probability_addition(self):
        p = F(1, 2)
        self.assertNotEqual(p, p+p)
        self.assertNotEqual(p, p*p)
        # Evaluating an idempotent event algebra is not a homomorphism to (+,*) probabilities.
        self.assertEqual(True or True, True)
        self.assertEqual(True and True, True)

    def test_08_normative_intersection_can_lose_predictive_coverage(self):
        pred, norm = {'A','B'}, {'A'}
        real_outcome = 'B'
        self.assertIn(real_outcome, pred)
        self.assertEqual(pred & norm, {'A'})  # Not the empty set in this example.
        self.assertNotIn(real_outcome, pred & norm)

    def test_09_coverage_union_bound_requires_no_independence(self):
        universe = frozenset(range(4))
        p = lambda event: F(len(event), len(universe))
        for c in powerset(universe):
            for s in powerset(universe):
                alpha, beta = 1-p(c), 1-p(s)
                self.assertGreaterEqual(p(c & s), max(F(0), 1-alpha-beta))

    def test_10_supermartingale_example_allows_changing_means(self):
        means = [F(1,10), F(2,5), F(1,5), F(1,2)]
        threshold, stake = F(1,2), F(1,2)
        expected_product = F(0)
        for outcome in product([0,1], repeat=len(means)):
            probability, evalue = F(1), F(1)
            for p, loss in zip(means, outcome):
                probability *= p if loss else 1-p
                factor = 1 + stake*(loss-threshold)
                self.assertGreaterEqual(factor, 0)
                evalue *= factor
            expected_product += probability*evalue
        self.assertEqual(expected_product, F(323,500))
        self.assertLessEqual(expected_product, 1)

    def test_11_rectangularization_may_be_strictly_conservative(self):
        theta = (0,1)
        fixed_parameter_worst = min(t + (1-t) for t in theta)
        rectangular_worst = min(theta) + min(1-t for t in theta)
        self.assertEqual(fixed_parameter_worst, 1)
        self.assertEqual(rectangular_worst, 0)
        self.assertLessEqual(rectangular_worst, fixed_parameter_worst)

    def test_12_joint_inner_witness_needs_shared_constraint(self):
        first, second = {0,1}, {0,1}
        cartesian = set(product(first, second))
        valid = {w for w in cartesian if w[0]+w[1] == 1}
        self.assertFalse(cartesian <= valid)
        self.assertEqual(valid, {(0,1),(1,0)})


if __name__ == '__main__':
    suite = unittest.defaultTestLoader.loadTestsFromTestCase(MathematicalReviewProbes)
    result = unittest.TextTestRunner(verbosity=2).run(suite)
    report = {
        'purpose': 'Mathematical counterexample probes only; no production audit or Lean evidence',
        'tests_run': result.testsRun,
        'failures': len(result.failures), 'errors': len(result.errors),
        'skipped': len(result.skipped), 'successful': result.wasSuccessful(),
        'lean_run': False, 'github_ci_run': False, 'repository_modified': False,
    }
    Path(__file__).with_name('probe_results.json').write_text(
        json.dumps(report, ensure_ascii=False, indent=2)+'\n', encoding='utf-8'
    )
    raise SystemExit(0 if result.wasSuccessful() else 1)
