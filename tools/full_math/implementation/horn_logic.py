"""Reference algorithms for the Horn/rule layer (F04/F05/F14).

Independent semantics plus executable checkers mirroring the Lean contracts:
derivation dependency sets, Horn closure iteration with stabilization and
leastness checks, and incremental add-only reuse vs full recompute.
"""
from __future__ import annotations
from fractions import Fraction
from typing import Dict, FrozenSet, List, Set, Tuple

Rule = Tuple[FrozenSet[str], str]


def deriv_deps(tree) -> List[str]:
    """Dependency set of a derivation tree ('origin'/'step' nodes)."""
    if tree["kind"] == "origin":
        return [tree["assume"]]
    if tree["kind"] == "step1":
        return deriv_deps(tree["child"])
    if tree["kind"] == "step2":
        return deriv_deps(tree["left"]) + deriv_deps(tree["right"])
    raise ValueError("unknown node kind: %r" % (tree.get("kind"),))


def deriv_subtrees(tree) -> List[dict]:
    if tree["kind"] == "origin":
        return [tree]
    if tree["kind"] == "step1":
        return [tree] + deriv_subtrees(tree["child"])
    if tree["kind"] == "step2":
        return [tree] + deriv_subtrees(tree["left"]) + deriv_subtrees(tree["right"])
    raise ValueError("unknown node kind")


def invalidated(retired: Set[str], tree) -> bool:
    return any(a in retired for a in deriv_deps(tree))


def horn_step(rules: List[Rule], facts: FrozenSet[str], current: FrozenSet[str]) -> FrozenSet[str]:
    heads = {head for (premises, head) in rules if premises <= current}
    return facts | current | heads


def horn_closure(rules: List[Rule], facts: FrozenSet[str]) -> FrozenSet[str]:
    """Least closure by iteration to stabilization (bounded by carrier size)."""
    atoms: Set[str] = set(facts)
    for premises, head in rules:
        atoms |= set(premises)
        atoms.add(head)
    current: FrozenSet[str] = frozenset()
    for _ in range(len(atoms) + 1):
        nxt = horn_step(rules, facts, current)
        if nxt == current:
            return current
        current = nxt
    raise AssertionError("closure did not stabilize within carrier bound")


def horn_is_prefixed(rules: List[Rule], facts: FrozenSet[str], candidate: FrozenSet[str]) -> bool:
    return horn_step(rules, facts, candidate) <= candidate


def horn_least_check(rules: List[Rule], facts: FrozenSet[str]) -> bool:
    """The closure is a pre-fixed point and is contained in every pre-fixed point
    that we can generate from subsets of the carrier (independent check)."""
    closure = horn_closure(rules, facts)
    if not horn_is_prefixed(rules, facts, closure):
        return False
    atoms: Set[str] = set(facts)
    for premises, head in rules:
        atoms |= set(premises)
        atoms.add(head)
    # every pre-fixed point of the full carrier lattice that contains facts
    from itertools import combinations
    for k in range(len(atoms) + 1):
        for extra in combinations(sorted(atoms), k):
            p = frozenset(set(facts) | set(extra))
            if horn_is_prefixed(rules, facts, p) and not closure <= p:
                return False
    return True


def add_only_reuse(rules_old: List[Rule], rules_new: List[Rule],
                   facts: FrozenSet[str], delta: FrozenSet[str]) -> FrozenSet[str]:
    if not set(rules_old) <= set(rules_new):
        raise ValueError("add-only precondition violated: rules shrank")
    return horn_closure(rules_new, horn_closure(rules_old, facts) | delta)


def full_recompute(rules: List[Rule], facts: FrozenSet[str]) -> FrozenSet[str]:
    return horn_closure(rules, facts)


def withdrawal_recompute(rules: List[Rule], facts: FrozenSet[str],
                         removed: str) -> FrozenSet[str]:
    return horn_closure(rules, facts - {removed})
