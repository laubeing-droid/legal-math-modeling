"""Tests for the argumentation layer implementation (F06–F13)."""
from fractions import Fraction
from itertools import combinations
import pytest

from tools.full_math.implementation import argumentation_ref as A


class TestGenerate:
    def test_sound_depth0(self):
        assert A.generate_sound_check(["a"], [], 0)

    def test_sound_chain(self):
        rules = [{"premises": ["a"], "head": "b"}]
        assert A.generate_sound_check(["a"], rules, 3)

    def test_complete_chain(self):
        rules = [{"premises": ["a"], "head": "b"}]
        assert A.generate_complete_check(["a"], rules, 2)

    def test_rootless_generates_nothing(self):
        rules = [{"premises": ["a"], "head": "b"}, {"premises": ["b"], "head": "a"}]
        assert A.generate([], rules, 3) == []

    def test_rooted_alternates(self):
        rules = [{"premises": ["a"], "head": "b"}, {"premises": ["b"], "head": "a"}]
        d3 = A.generate(["a"], rules, 3)
        assert any(A.arg_height(t) == 3 for t in d3)

    def test_negative_misaligned_children(self):
        # a hand-built misaligned tree fails wellformedness
        bad = ("node", {"premises": ["x"], "head": "b"}, [("leaf", "a")])
        assert not A.wellformed({"a"}, bad)


class TestAttack:
    def test_rebut_leaf(self):
        con = lambda x, y: x == "p" and y == "q"
        rc = lambda r: "contra-" + r["head"]
        a = ("leaf", "p")
        b = ("leaf", "q")
        assert A.edge_impl(con, rc, a, b)

    def test_undermine_child(self):
        con = lambda x, y: (x, y) == ("p", "c")
        rc = lambda r: "contra-" + r["head"]
        a = ("leaf", "p")
        child = ("leaf", "c")
        b = ("node", {"premises": ["c"], "head": "d"}, [child])
        assert A.edge_impl(con, rc, a, b)

    def test_lift_deep(self):
        con = lambda x, y: (x, y) == ("p", "leaf-target")
        rc = lambda r: "contra-" + r["head"]
        a = ("leaf", "p")
        deep = ("leaf", "leaf-target")
        mid = ("node", {"premises": ["leaf-target"], "head": "m"}, [deep])
        b = ("node", {"premises": ["m"], "head": "top"}, [mid])
        assert A.edge_impl(con, rc, a, b)

    def test_pending_preserved(self):
        edges = [(("leaf", "p"), ("leaf", "q")), (("leaf", "r"), ("leaf", "s"))]
        policy = lambda x, y: None if y[1] == "q" else True
        pending = A.pending_edges(edges, policy)
        assert len(pending) == 1 and pending[0][1][1] == "q"


class TestProfiles:
    UNIVERSE = [0, 1, 2]

    @staticmethod
    def ring():
        return lambda x, y: (x + 1) % 3 == y

    def test_ring_conflict_free_empty(self):
        assert A.conflict_free(self.ring(), frozenset())

    def test_ring_no_stable(self):
        assert A.three_ring_stable_exists() is False

    def test_ring_empty_admissible_singles_not(self):
        # in the odd cycle, the empty set is admissible but no singleton
        # defends itself (its attacker is not counter-attacked)
        assert A.admissible(self.ring(), frozenset(), self.UNIVERSE)
        for k in range(3):
            assert not A.admissible(self.ring(), frozenset({k}), self.UNIVERSE)

    def test_selfattack_grounded_empty(self):
        assert A.self_attack_grounded_empty()

    def test_grounded_fixpoint(self):
        attack = lambda x, y: (x + 1) % 3 == y
        G = A.grounded(attack, self.UNIVERSE)
        assert A.char_f(attack, G, self.UNIVERSE) == G

    def test_complete_contains_grounded(self):
        attack = lambda x, y: (x + 1) % 3 == y
        G = A.grounded(attack, self.UNIVERSE)
        assert A.admissible(attack, G, self.UNIVERSE)
        assert A.char_f(attack, G, self.UNIVERSE) <= G

    def test_preferred_exists(self):
        assert A.preferred_exists(self.ring(), self.UNIVERSE) is not None

    def test_negative_non_cf_rejected(self):
        attack = self.ring()
        assert not A.conflict_free(attack, frozenset({0, 1}))


class TestQueryAggregation:
    def test_no_extensions_differs_from_empty_family(self):
        assert A.eval_universal(("noExtensions",)) != A.eval_universal(("extensions", []))

    def test_incomplete_unknown(self):
        assert A.eval_universal(("incomplete",)) == "unknown"
