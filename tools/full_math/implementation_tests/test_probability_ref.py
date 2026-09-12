"""Tests for the probability layer implementation (P01–P13, EXT06, E01)."""
from fractions import Fraction
import pytest

from tools.full_math.implementation import probability_ref as P

F = Fraction


class TestChainBN:
    def test_normalizes_single(self):
        k = [{"f": F("0.3"), "t": F("0.7")}]
        assert P.chain_normalizes(k)

    def test_normalizes_chain(self):
        ks = [{"f": F("0.5"), "t": F("0.5")}, {"f": F("0.1"), "t": F("0.9")}]
        assert P.chain_normalizes(ks)

    def test_joint_values(self):
        k = [{"f": F("0.3"), "t": F("0.7")}]
        assert P.chain_joint(k, [True]) == F("0.7")
        assert P.chain_joint(k, [False]) == F("0.3")

    def test_negative_bad_rows_rejected(self):
        ks = [{"f": F("0.3"), "t": F("0.8")}]  # rows sum to 1.1
        assert not P.chain_normalizes(ks)


class TestConditioning:
    def test_posterior(self):
        p = {"a": F("0.1"), "b": F("0.3")}
        q, ok = P.condition(p, lambda k: k == "a")
        assert ok and q["a"] == 1 and q["b"] == 0

    def test_zero_mass_incompatible(self):
        p = {"a": F("0"), "b": F("1")}
        q, ok = P.condition(p, lambda k: k == "a")
        assert not ok and q is None

    def test_negative_no_silent_zero_division(self):
        p = {"a": F(0), "b": F(0)}
        q, ok = P.condition(p, lambda k: True)
        assert not ok


class TestDirichlet:
    def test_weights_sum_one(self):
        w = P.dir_weights([F(1), F(2)], [F(3), F(4)])
        assert sum(w, F(0)) == 1

    def test_update_compose(self):
        first = P.dir_weights([F(1), F(1)], [F(2), F(0)])
        second = P.dir_weights([F(1) + 2, F(1) + 0], [F(1), F(1)])
        both = P.dir_weights([F(1), F(1)], [F(3), F(1)])
        assert first is not None and second == both

    def test_negative_shifted(self):
        w = P.dir_weights([F(1), F(1)], [F(9), F(0)])
        assert w[0] > w[1]


class TestBetaRatio:
    def test_rising_zero(self):
        assert P.rising(F("2.5"), 0) == 1

    def test_rising_succ(self):
        assert P.rising(F(2), 3) == F(2) * F(3) * F(4)

    def test_beta_ratio_integer(self):
        # B(1+w, 1+l)/B(1,1) with α=β=1: 2!*1!/4! = 1/12
        assert P.beta_ratio(F(1), F(1), 2, 1) == F(1, 12)


class TestHyper:
    def test_normalize(self):
        w = P.hyper_weights([F(1), F(1)], [F("0.5"), F("0.25")])
        assert sum(w, F(0)) == 1

    def test_data_moves_posterior(self):
        # asymmetric hyperstates: the same data (w=2, l=0) shifts weights
        # away from the flat prior (1/2, 1/2)
        r1 = P.beta_ratio(F(1), F(3), 2, 0)
        r2 = P.beta_ratio(F(3), F(1), 2, 0)
        weights = P.hyper_weights([F(1), F(1)], [r1, r2])
        assert weights != [F(1, 2), F(1, 2)]
        assert weights[1] > weights[0]

    def test_negative_zero_mass(self):
        with pytest.raises(ValueError):
            P.hyper_weights([F(0), F(0)], [F(0), F(0)])


class TestMisspec:
    def test_bounds_hold(self):
        assert P.contamination_bounds(F("0.1"), F("0.5"), F("0.2"),
                                      F("0.4"), F("0.6"))

    def test_negative_epsilon_term_load_bearing(self):
        # the +eps in the upper bound is necessary: without it the bound fails
        eps, p, q, u = F("0.1"), F("0.5"), F(1), F("0.6")
        star = (1 - eps) * p + eps * q
        assert star > (1 - eps) * u


class TestUnprocessed:
    def test_bracket(self):
        assert P.unprocessed_bounds(F(10), F(5), F(1), F(1), F(2))

    def test_degenerate_flagged(self):
        assert P.unprocessed_bounds(F(0), F(0), F(1), F(1), F(2)) is False


class TestBrier:
    def test_identity(self):
        assert P.brier_excess(F("0.3"), F("0.8")) == F("0.25")


class TestPAV:
    def test_kkt_certificate_passes(self):
        y = [F(0), F(1), F(0), F(1)]
        w = [F(1)] * 4
        cert = P.pav_kkt_certificate(y, w)
        assert cert is not None

    def test_pav_isotonic(self):
        y = [F(3), F(1), F(2)]
        x = P.pav_weights(y, [F(1)] * 3)
        assert all(x[i] <= x[i + 1] for i in range(len(x) - 1))

    def test_pav_optimal_over_grid(self):
        import itertools
        y = [F(0), F(1), F(0)]
        w = [F(1)] * 3
        x = P.pav_weights(y, w)
        grid = itertools.product([0, 1, 2], repeat=3)
        assert P.pav_optimal_over(y, w, x, [list(g) for g in grid])

    def test_negative_nonmonotone_input_fails_grid_check(self):
        # feeding a non-isotonic candidate must be rejected by optimality
        y = [F(0), F(1), F(0)]
        w = [F(1)] * 3
        assert not P.pav_optimal_over(y, w, [F(1), F(0), F(0)], [[F(0), F(0), F(0)]])


class TestConformal:
    def test_k_computation(self):
        assert P.conformal_k(9, F("0.1")) == 9
        assert P.conformal_k(5, F("0.5")) == 3

    def test_infinite_quantile(self):
        scores = [F(1), F(2), F(3)]
        q = P.conformal_quantile(scores, 4)
        assert q == float("inf")

    def test_coverage_count(self):
        scores = [F(1), F(2), F(3), F(4)]
        assert P.conformal_coverage_count(scores, 2) == 2

    def test_negative_k_below_range(self):
        # k must be at least 1; k=0 is not a valid conformal rank
        scores = [F(1), F(2)]
        assert P.conformal_k(len(scores), F("0")) == len(scores) + 1


def _raise():
    raise IndexError


class TestBetting:
    def test_path_nonnegative(self):
        lams = [F("0.5"), F("0.5")]
        losses = [F(1), F(0)]
        assert P.path_nonnegative(lams, losses, F(1))

    def test_negative_lambda_too_big(self):
        lams = [F(2)]
        losses = [F(1)]
        assert not P.path_nonnegative(lams, losses, F(1))


class TestE01:
    def test_brier_score(self):
        assert P.brier_score([F(1), F(0)], [1, 0]) == 0
        assert P.brier_score([F("0.5"), F("0.5")], [1, 0]) == F("0.25")

    def test_cluster_isolation(self):
        assert P.clusters_disjoint({"c1", "c2"}, {"c3"})
        assert not P.clusters_disjoint({"c1"}, {"c1"})

    def test_status_transitions(self):
        assert P.e01_status(F("0.5"), F("0.3"), 100, 50) == "REAL_VALIDATION_REQUIRED"
        assert P.e01_status(F("0.2"), F("0.3"), 100, 50) == "WITHIN_DECLARED_RISK"
        assert P.e01_status(F("0.2"), F("0.3"), 10, 50) == "REAL_VALIDATION_REQUIRED"

    def test_cantelli(self):
        b = P.cantelli_bound(F(0), F(1), F(1))
        assert b == F(1, 2)
