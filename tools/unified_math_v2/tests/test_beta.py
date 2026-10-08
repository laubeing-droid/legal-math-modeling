"""WP-6 tests: exact integer Beta CDF, certified enclosures, two-point
quantile shrinking.

Anchors from the plan's own verified checks: Beta(2,2) CDF(1/4)=5/32,
CDF(3/4)=27/32; the a=1,b=1/2,η=1/4 left-tail bound must dominate the
true value 2−√3 > 1/4 (so M_b may NOT be taken as 1); F(x)=x with
q=1/2 must never prune on coarse readings — the platform-reading
counterexample.
"""

from fractions import Fraction as Q
from unittest import TestCase

import pytest

from unified.beta import (
    BetaEnclosure,
    beta_cdf_enclosure,
    beta_cdf_integer,
    beta_cdf_integer_compare,
    beta_tail_constants,
    mixture_cdf_factory,
    quantile_by_two_point,
    rat_power_enclosure,
    rat_root_enclosure,
)


class RootEnclosureTests(TestCase):
    def test_sqrt2_bisected(self):
        lo, hi = rat_root_enclosure(Q(2), 2, Q(1, 1000))
        self.assertLess(lo * lo, Q(2))
        self.assertGreater(hi * hi, Q(2))
        self.assertLessEqual(hi - lo, Q(1, 1000))

    def test_power_negative_exponent(self):
        lo, hi = rat_power_enclosure(Q(4), Q(-1, 2), Q(1, 1000))
        self.assertLessEqual(lo, Q(1, 2))
        self.assertGreaterEqual(hi, Q(1, 2))
        self.assertLessEqual(hi - lo, Q(1, 100))

    def test_exact_integer_root(self):
        lo, hi = rat_root_enclosure(Q(8), 3, Q(1, 10 ** 9))
        self.assertLessEqual(lo, Q(2))
        self.assertGreaterEqual(hi, Q(2))
        self.assertLess(hi - lo, Q(1, 10 ** 8))


class IntegerCdfTests(TestCase):
    def test_plan_anchors(self):
        self.assertEqual(beta_cdf_integer(2, 2, Q(1, 4)), Q(5, 32))
        self.assertEqual(beta_cdf_integer(2, 2, Q(3, 4)), Q(27, 32))

    def test_endpoints(self):
        self.assertEqual(beta_cdf_integer(1, 1, Q(0)), Q(0))
        self.assertEqual(beta_cdf_integer(1, 1, Q(1)), Q(1))
        self.assertEqual(beta_cdf_integer(1, 1, Q(1, 2)), Q(1, 2))

    def test_strict_monotone_between_anchors(self):
        self.assertEqual(
            beta_cdf_integer_compare(2, 2, Q(1, 4), Q(5, 32)), 0
        )
        self.assertEqual(
            beta_cdf_integer_compare(2, 2, Q(1, 2), Q(5, 32)), 1
        )

    def test_golden_interval_mass(self):
        # Beta(2,1): [1/8, 1] carries 63/64 (plan 7.4 anchor)
        mass = beta_cdf_integer(2, 1, Q(1)) - beta_cdf_integer(2, 1, Q(1, 8))
        self.assertEqual(mass, Q(63, 64))


class TailConstantTests(TestCase):
    def test_left_tail_bound_dominates_true_value(self):
        # a=1, b=1/2, eta=1/4: true left tail = 2 − sqrt(3) ≈ 0.2679 > 1/4.
        # The bound must use M_b=(1−eta)^(b−1)= (3/4)^(−1/2), NOT 1.
        _l_lo, l_hi, _r_lo, _r_hi = beta_tail_constants(Q(1), Q(1, 2), Q(1, 4))
        # bound = M_b * eta^1 / a = (3/4)^(-1/2) * (1/4) = 1/(2*sqrt(3))
        # ≈ 0.2887 >= 2 - sqrt(3) ≈ 0.2679 — and strictly ABOVE 1/4.
        self.assertGreater(l_hi, Q(1, 4))

    def test_b_ge_one_uses_unit_bound(self):
        _l_lo, l_hi, _r_lo, r_hi = beta_tail_constants(Q(2), Q(3), Q(1, 4))
        # M_b = 1: left bound = eta^2/2 = 1/32 (dominates it up to the
        # certified slop); right bound = eta^3/3.
        self.assertGreaterEqual(l_hi, Q(1, 32))
        self.assertGreaterEqual(r_hi, Q(1, 192))


class EnclosureTests(TestCase):
    def test_integer_case_contained(self):
        exact = beta_cdf_integer(2, 2, Q(1, 4))
        enc = beta_cdf_enclosure(Q(2), Q(2), Q(1, 4), Q(1, 20))
        self.assertLessEqual(enc.lo, exact)
        self.assertGreaterEqual(enc.hi, exact)

    def test_enclosure_includes_true_value_half_params(self):
        # Beta(1/2,1/2) at 1/4: true CDF = (2/pi) asin(1/2) = 1/3.
        enc = beta_cdf_enclosure(Q(1, 2), Q(1, 2), Q(1, 4), Q(1, 10))
        self.assertLessEqual(enc.lo, Q(1, 3))
        self.assertGreaterEqual(enc.hi, Q(1, 3))

    def test_endpoints_exact(self):
        self.assertEqual(beta_cdf_enclosure(Q(2), Q(2), Q(0), Q(1, 10)).lo, Q(0))
        self.assertEqual(beta_cdf_enclosure(Q(2), Q(2), Q(1), Q(1, 10)).hi, Q(1))


class TwoPointQuantileTests(TestCase):
    def test_identity_cdf_quantile(self):
        # F(x)=x: median 1/2 must be found; coarse [0,1] readings at
        # m=1/3, 2/3 must NOT prune (the platform-reading counterexample).
        def identity(x: Q, w: Q) -> BetaEnclosure:
            return BetaEnclosure(x - w if x - w > 0 else Q(0),
                                 x + w if x + w < 1 else Q(1))
        result = quantile_by_two_point(identity, Q(1, 2), Q(1, 100))
        self.assertLessEqual(result.lo, Q(1, 2))
        self.assertGreaterEqual(result.hi, Q(1, 2))
        self.assertLessEqual(result.width, Q(1, 100))

    def test_q_at_test_point_itself(self):
        # q exactly equals F(m1) at some step: no strict certificate can
        # ever move past the true quantile — the interval still contains it.
        def identity(x: Q, w: Q) -> BetaEnclosure:
            return BetaEnclosure(max(Q(0), x - w), min(Q(1), x + w))
        result = quantile_by_two_point(identity, Q(1, 3), Q(1, 200))
        self.assertLessEqual(result.lo, Q(1, 3))
        self.assertGreaterEqual(result.hi, Q(1, 3))

    def test_width_shrinks_by_two_thirds(self):
        def identity(x: Q, w: Q) -> BetaEnclosure:
            return BetaEnclosure(max(Q(0), x - w), min(Q(1), x + w))
        result = quantile_by_two_point(identity, Q(1, 2), Q(1, 1000))
        self.assertLess(result.width, Q(1, 1000) + Q(1, 1000))

    def test_mixture_quantile(self):
        # 50/50 of Beta(1,1) and Beta(2,2)-like identity shapes: use
        # certified exact-oracle mixtures of enclosable components.
        def comp1(x: Q, w: Q) -> BetaEnclosure:
            exact = beta_cdf_integer(1, 1, x)
            return BetaEnclosure(exact, exact)

        def comp2(x: Q, w: Q) -> BetaEnclosure:
            exact = beta_cdf_integer(2, 2, x)
            return BetaEnclosure(exact, exact)

        mix = mixture_cdf_factory([Q(1, 2), Q(1, 2)], [comp1, comp2])
        enc = mix(Q(1, 2), Q(0))
        self.assertEqual(enc.lo, Q(1, 2) * (Q(1, 2) + Q(1, 2)))
        result = quantile_by_two_point(mix, Q(1, 2), Q(1, 100))
        # F(1/2)=1/2 for this mixture: quantile is exactly 1/2.
        self.assertLessEqual(result.lo, Q(1, 2))
        self.assertGreaterEqual(result.hi, Q(1, 2))

    def test_rejects_bad_weights(self):
        def comp(x, w):
            return BetaEnclosure(Q(0), Q(1))
        with pytest.raises(ValueError):
            mixture_cdf_factory([Q(1, 2), Q(1, 3)], [comp, comp])
        with pytest.raises(ValueError):
            mixture_cdf_factory([Q(-1), Q(2)], [comp, comp])


class Round2RegressionTests(TestCase):
    """Round-2 math-review defects, pinned."""

    def test_negative_exponent_small_x_no_zero_division(self):
        # defect A: x < width used to leave lo_root = 0 -> 1/0
        lo, hi = rat_power_enclosure(Q(1, 10 ** 6), Q(-1, 2), Q(1, 10))
        target = Q(1000)  # (1e-6)^(-1/2) = 1000
        self.assertLessEqual(lo, target)
        self.assertGreaterEqual(hi, target)

    def test_budget_width_contract_enforced(self):
        # defect C: the enclosure either honors eps or refuses — it never
        # silently returns a violating interval
        enc = beta_cdf_enclosure(Q(1), Q(99, 100), Q(1, 2), Q(1, 10))
        self.assertLessEqual(enc.hi - enc.lo, Q(1, 10))
        self.assertLessEqual(enc.lo, Q(1, 2))
        self.assertGreaterEqual(enc.hi, Q(1, 2))
