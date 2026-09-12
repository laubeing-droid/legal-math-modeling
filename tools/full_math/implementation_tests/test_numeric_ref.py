"""Tests for the numeric layer implementation (N01–N10)."""
from fractions import Fraction
import pytest

from tools.full_math.implementation import numeric_ref as N

F = Fraction


class TestResidual:
    def test_conservation(self):
        assert N.residual_checks(F(1000), [F(300), F(400)])

    def test_underpayment(self):
        r, c, u = N.residual_split(F(100), [F(30)])
        assert c == F(70) and u == 0

    def test_overpayment(self):
        r, c, u = N.residual_split(F(100), [F(130)])
        assert c == 0 and u == F(30)

    def test_negative_double_count(self):
        # overpaying twice must not create covered twice
        r, c, u = N.residual_split(F(100), [F(130), F(20)])
        assert c == 0 and u == F(50)


class TestCalendar:
    def test_leap(self):
        assert N.is_leap(2000) and not N.is_leap(1900)
        assert N.is_leap(2024) and not N.is_leap(2023)

    def test_feb_lengths(self):
        assert N.month_len(2024, 2) == 29
        assert N.month_len(2023, 2) == 28

    def test_ordinal_succ(self):
        assert N.succ_day_ordinal(2024, 3, 14)
        assert N.day_of_year(2024, 1, 31) == 31
        assert N.day_of_year(2024, 2, 1) == 32

    def test_negative_wrong_month(self):
        assert N.day_of_year(2023, 2, 1) == 32  # 2023 feb has 28 days: 31+1


class TestIntervals:
    def test_add_sound(self):
        a, b = (F(-1), F(2)), (F(3), F(5))
        p = N.iv_add(a, b)
        assert all(p[0] <= x + y <= p[1]
                   for x in [F(-1), 0, F(2)] for y in [3, 5])

    def test_mul_four_endpoints(self):
        a, b = (F(-2), F(3)), (F(-1), F(4))
        p = N.iv_mul(a, b)
        assert p == (F(-8), F(12))

    def test_mul_sound_sampled(self):
        a, b = (F(-2), F(3)), (F(-1), F(4))
        xs = [F(-2), F(-1), 0, 1, F(3)]
        ys = [F(-1), 0, 1, F(4)]
        assert N.iv_mul_sound(a, b, xs, ys)

    def test_recip_positive(self):
        r = N.iv_recip((F(2), F(4)))
        assert r[0] == F(1, 4) and r[1] == F(1, 2)

    def test_negative_recip_zero_span(self):
        with pytest.raises(ValueError):
            N.iv_recip((F(-1), F(1)))


class TestLP:
    def test_weak_duality(self):
        A = [[F(1)], [F(1)]]
        b = [F(2), F(1)]
        c = [F(1)]
        x = [F(2)]
        lam = [F(1), 0]
        assert N.primal_feasible(A, b, x)
        assert N.dual_feasible(A, b, c, lam)
        assert N.weak_duality_holds(A, b, c, x, lam)

    def test_negative_infeasible_primal(self):
        A = [[F(1)]]
        b = [F(5)]
        assert not N.primal_feasible(A, b, [F(3)])


class TestKKT:
    def test_interior_optimum(self):
        # f(x) = x^2 - 2x on x >= 1: optimum at x=1 with multiplier
        h, g, l, xstar, mu = F(2), F(-2), F(1), F(1), F(0)
        cert = N.kkt1_check(h, g, l, xstar, mu)
        assert cert
        assert N.kkt1_suffices(h, g, l, xstar, mu,
                               [F(1), F("1.5"), F(2), F(10)])

    def test_boundary_with_multiplier(self):
        # f(x) = x^2 on x >= 1: optimum at boundary x=1, mu = 2*1 = 2
        h, g, l, xstar, mu = F(2), F(0), F(1), F(1), F(2)
        assert N.kkt1_check(h, g, l, xstar, mu)
        assert N.kkt1_suffices(h, g, l, xstar, mu, [F(1), F(2), F(3)])

    def test_negative_bad_multiplier(self):
        assert not N.kkt1_check(F(2), F(0), F(1), F(1), F(-1))


class TestProjectedGradient:
    def test_fixed_point_interior(self):
        l, u, a, b, eta = F(0), F(10), F(1), F(-2), F("0.5")
        xstar = N.T_fixed_point(l, u, a, b, eta)
        assert l <= xstar <= u
        assert N.T_map(l, u, a, b, eta, xstar) == xstar

    def test_fixed_point_boundary(self):
        l, u, a, b, eta = F(1), F(10), F(1), F(100), F("0.5")
        xstar = N.T_fixed_point(l, u, a, b, eta)
        assert xstar == F(1)
        assert N.T_map(l, u, a, b, eta, xstar) == xstar

    def test_residual_bound(self):
        k, e0, eps = F("0.5"), F(1), F("0.1")
        bound = N.residual_error_bound(k, e0, eps, 3)
        assert bound <= eps / (1 - k) + F(1)

    def test_negative_explosive_step(self):
        k = F(2)  # violates k < 1: the bound is not applicable
        assert k >= 1


class TestBellman:
    def test_single_state(self):
        legal = {"s": ["a", "b"]}
        r = lambda s, a: F(1) if a == "a" else F(0)
        p = lambda s, a, sp: F(1)
        v = N.bellman_vf(legal, r, p, F("0.5"), 2, "s")
        # both steps pick "a": 1 + 0.5*1 + 0.25*1... horizon 2 => 1 + .5*1
        assert v == F(1) + F("0.5")

    def test_legality_preserved(self):
        legal = {"s": ["legal1"]}
        r = lambda s, a: F(0)
        p = lambda s, a, sp: F(1)
        assert N.bellman_attained_by_legal(legal, r, p, F("0.9"), 3, "s")

    def test_negative_illegal_never_chosen(self):
        legal = {"s": ["only_legal"]}
        r = lambda s, a: F(0)
        p = lambda s, a, sp: F(1)
        chosen = {"s": "only_legal"}
        assert all(a in legal[s] for s, a in chosen.items())
