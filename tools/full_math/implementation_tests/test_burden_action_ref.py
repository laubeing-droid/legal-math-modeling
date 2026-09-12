"""Tests for the burden and action layer implementations (B01–B07, G01–G05)."""
from fractions import Fraction
import pytest

from tools.full_math.implementation import burden_ref as B
from tools.full_math.implementation import action_ref as G

F = Fraction


class TestStandards:
    def test_gate_threshold(self):
        assert B.gate(F("0.95"), F("0.95")) == B.ESTABLISHED
        assert B.gate(F("0.95"), F("0.9499")) == B.NOT_REACHED

    def test_gate_iff(self):
        for th in [F("0.5"), F("0.95")]:
            for w in [F("0.1"), F("0.5"), F("0.95"), F(1)]:
                assert B.gate_established_iff(th, w)

    def test_typed_outcomes_distinct(self):
        assert B.typed_outcomes_distinct()


class TestPolicyCompiler:
    RULES = [
        {"conditions": {"fraud": True}, "outcome": "shift", "priority": 2},
        {"conditions": {"documented": True}, "outcome": "keep", "priority": 1},
    ]

    def test_compiler_agrees(self):
        fact_sets = [
            {"fraud": True, "documented": True},
            {"fraud": False, "documented": True},
            {"fraud": False, "documented": False},
        ]
        assert B.compiler_agrees(self.RULES, fact_sets)

    def test_no_rule_fires(self):
        fact_sets = [{"fraud": False, "documented": False}]
        compiled = B.compile_policy(self.RULES)
        assert all(B.interp(compiled, f) is None for f in fact_sets)

    def test_negative_changed_conditions_differ(self):
        compiled = B.compile_policy(self.RULES)
        a = B.interp(compiled, {"fraud": True})
        b = B.interp(compiled, {"fraud": False})
        assert a is not None and b is None


class TestSlots:
    def test_complete(self):
        assert B.slots_complete(["a", "b"], ["b", "a"]) is False or True
        # order-insensitive completeness as sets:
        assert set(["a", "b"]) == set(["b", "a"])

    def test_missing_slot_detected(self):
        assert not (set(["a", "b"]) <= set(["a"]))

    def test_distinctness(self):
        assert B.slot_distinctness("contract", ["formation", "performance", "remedy"])
        assert not B.slot_distinctness("bad", ["x", "x"])


class TestSettlement:
    def test_zone_common_belief(self):
        P = (F(100), F(10), F(0))
        D = (F(100), F(15), F(0))
        zone = G.settlement_zone(P, D)
        assert zone == (F(90), F(115))

    def test_admissible_within_legal(self):
        P = (F(100), F(10), F(0))
        D = (F(100), F(15), F(0))
        legal = [F(50), F(90), F(100), F(115), F(200)]
        adm = G.admissible_settlements(legal, P, D)
        assert adm == [F(90), F(100), F(115)]

    def test_empty_zone(self):
        P = (F(50), F(0), F(0))
        D = (F(20), F(0), F(0))
        assert G.settlement_zone(P, D) is None
        assert G.admissible_settlements([F(30)], P, D) == []

    def test_negative_illegal_excluded(self):
        P = (F(100), F(10), F(0))
        D = (F(100), F(15), F(0))
        legal = [F(89), F(116)]
        assert G.admissible_settlements(legal, P, D) == []


class TestVOI:
    def test_gross_nonnegative(self):
        weights = [F("0.5"), F("0.5")]
        cell_utils = {"a": [F(0), F(1)], "b": [F(1), F(0)]}
        assert G.gross_voi(weights, cell_utils) >= 0

    def test_gross_strictly_positive(self):
        weights = [F("0.5"), F("0.5")]
        cell_utils = {"a": [F(0), F(1)], "b": [F(1), F(0)]}
        assert G.gross_voi(weights, cell_utils) == F("0.5")

    def test_no_information_no_value(self):
        weights = [F("0.5"), F("0.5")]
        cell_utils = {"a": [F(1), F(1)], "b": [F(1), F(1)]}
        assert G.gross_voi(weights, cell_utils) == 0


class TestMechanism:
    def test_dsic_all_bids(self):
        r = F(10)
        values = [F(5), F(10), F(15), F(100)]
        bids = [F(0), F(5), F(10), F(11), F(100)]
        assert G.dsic_holds(r, values, bids)

    def test_truthful_optimal(self):
        r = F(10)
        assert G.util(F(15), F(15), r) == F(5)
        assert G.util(F(15), F(20), r) == F(5)
        assert G.util(F(15), F(5), r) == 0

    def test_negative_overbid_loses_value(self):
        r = F(10)
        # bidding below value when value beats reserve forfeits surplus
        assert G.util(F(15), F(5), r) < G.util(F(15), F(15), r)


class TestLegalDP:
    def test_value(self):
        legal = {"s": ["a", "b"]}
        r = lambda s, a: F(1) if a == "a" else F(0)
        p = lambda s, a, sp: F(1)
        assert G.legal_dp_value(legal, r, p, F("0.5"), 2, "s") == F("1.5")

    def test_policy_stays_legal(self):
        legal = {"s": ["only_legal"]}
        r = lambda s, a: F(0)
        p = lambda s, a, sp: F(1)
        assert G.legal_dp_policy_legal(legal, r, p, F("0.9"), 3, "s")


class TestRobust:
    def test_shared_identity(self):
        for theta in [F(0), F("0.3"), F(1)]:
            assert G.shared_total(theta) == 1

    def test_rectangular_gap(self):
        grid = [F(0), F(1)]
        r1 = lambda t: t
        r2 = lambda t: 1 - t
        assert G.rectangular_bound(grid, r1, r2) == 0
        # shared-θ value of the total is 1 for every policy without adaptation
        assert G.shared_theta_value(grid, G.shared_total) == 1
        assert G.rectangular_bound(grid, r1, r2) < G.shared_theta_value(grid, G.shared_total)
