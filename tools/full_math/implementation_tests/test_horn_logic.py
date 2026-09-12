"""Tests for the Horn/rule layer implementation (F04/F05/F14)."""
from fractions import Fraction
import pytest

from tools.full_math.implementation import horn_logic as H


class TestDerivDeps:
    def test_origin_deps(self):
        t = {"kind": "origin", "assume": "A"}
        assert H.deriv_deps(t) == ["A"]

    def test_step2_union(self):
        t = {"kind": "step2", "rule": "r",
             "left": {"kind": "origin", "assume": "A"},
             "right": {"kind": "origin", "assume": "B"},
             "conc": "C"}
        assert sorted(H.deriv_deps(t)) == ["A", "B"]

    def test_deep_tree(self):
        t = {"kind": "step1", "rule": "r",
             "child": {"kind": "step2", "rule": "r2",
                       "left": {"kind": "origin", "assume": "X"},
                       "right": {"kind": "origin", "assume": "Y"},
                       "conc": "c2"},
             "conc": "c1"}
        assert sorted(H.deriv_deps(t)) == ["X", "Y"]

    def test_negative_missing_dep(self):
        # a tree that never mentions Z must not gain Z by transformation
        t = {"kind": "origin", "assume": "A"}
        assert "Z" not in H.deriv_deps(t)

    def test_invalidated_by_retired(self):
        t = {"kind": "origin", "assume": "A"}
        assert H.invalidated({"A"}, t) is True
        assert H.invalidated({"B"}, t) is False


class TestHornClosure:
    def test_chain_closure(self):
        rules = [(frozenset({"a"}), "b"), (frozenset({"b"}), "c")]
        assert H.horn_closure(rules, frozenset({"a"})) == frozenset({"a", "b", "c"})

    def test_no_firing_without_facts(self):
        rules = [(frozenset({"a"}), "b")]
        assert H.horn_closure(rules, frozenset()) == frozenset()

    def test_cycle_stabilizes(self):
        rules = [(frozenset({"a"}), "b"), (frozenset({"b"}), "a")]
        assert H.horn_closure(rules, frozenset({"a"})) == frozenset({"a", "b"})

    def test_leastness_holds(self):
        rules = [(frozenset({"a"}), "b"), (frozenset({"b", "c"}), "d")]
        assert H.horn_least_check(rules, frozenset({"a", "c"})) is True

    def test_negative_not_prefixed(self):
        # a non-closed candidate fails the pre-fixed check
        rules = [(frozenset({"a"}), "b")]
        assert H.horn_is_prefixed(rules, frozenset({"a"}), frozenset({"a"})) is False

    def test_add_only_equals_full_recompute(self):
        r_old = [(frozenset({"a"}), "b")]
        r_new = r_old + [(frozenset({"b"}), "c")]
        got = H.add_only_reuse(r_old, r_new, frozenset({"a"}), frozenset())
        assert got == H.full_recompute(r_new, frozenset({"a"}))

    def test_withdrawal_recompute_differs(self):
        rules = [(frozenset({"a"}), "b")]
        before = H.horn_closure(rules, frozenset({"a"}))
        after = H.withdrawal_recompute(rules, frozenset({"a"}), "a")
        assert before != after and after == frozenset()

    def test_negative_add_only_shrunk_rules_rejected(self):
        r_old = [(frozenset({"a"}), "b")]
        r_new = []
        with pytest.raises(ValueError):
            H.add_only_reuse(r_old, r_new, frozenset({"a"}), frozenset())
