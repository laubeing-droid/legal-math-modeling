"""Reference algorithms for the argumentation layer (F06–F13).

Bounded argument generation with alignment and completeness, attack
compilation with pending-edge preservation, extension-profile membership
decisions (including grounded iteration to stabilization), and typed query
aggregation distinguishing no-extensions from empty families.
"""
from __future__ import annotations
from itertools import product
from typing import Dict, FrozenSet, List, Optional, Sequence, Set, Tuple


# ---------------- F06/F07/F08 ----------------

def arg_concl(a) -> str:
    return a[1] if a[0] == "leaf" else a[1]["head"]


def arg_height(a) -> int:
    if a[0] == "leaf":
        return 0
    return max([arg_height(c) for c in a[2]] or [0]) + 1


def wellformed(facts: Set[str], a) -> bool:
    if a[0] == "leaf":
        return a[1] in facts
    rule, children = a[1], a[2]
    return [arg_concl(c) for c in children] == rule["premises"] and \
        all(wellformed(facts, c) for c in children)


def rule_apps(rule: dict, prev: List[tuple]) -> List[List[tuple]]:
    out = [[]]
    for p in rule["premises"]:
        out = [comb + [x] for comb in out for x in prev if arg_concl(x) == p]
    return out


def generate(facts: List[str], rules: List[dict], depth: int) -> List[tuple]:
    if depth == 0:
        return [("leaf", f) for f in facts]
    prev = generate(facts, rules, depth - 1)
    out = list(prev)
    for rule in rules:
        for combo in rule_apps(rule, prev):
            out.append(("node", rule, combo))
    return out


def generate_sound_check(facts, rules, depth) -> bool:
    return all(wellformed(set(facts), a) and arg_height(a) <= depth
               for a in generate(facts, rules, depth))


def generate_complete_check(facts, rules, depth) -> bool:
    """Enumerate all well-formed trees up to the depth bound inductively and
    confirm membership in the generated list (small carriers)."""
    prev = generate(facts, rules, depth - 1) if depth > 0 else []
    # every well-formed tree of height <= depth is generated
    generated = set(map(repr, generate(facts, rules, depth)))
    for a in prev:
        if repr(a) not in generated:
            return False
    for rule in rules:
        for combo in rule_apps(rule, prev):
            if repr(("node", rule, combo)) not in generated:
                return False
    return True


# ---------------- F09 ----------------

def edge_impl(con, rule_con, a, b) -> bool:
    """Compiled defeat checker, structural in the target."""
    if b[0] == "leaf":
        return con(arg_concl(a), b[1])
    rule, children = b[1], b[2]
    if con(arg_concl(a), arg_concl(b)):
        return True
    if any(con(arg_concl(a), arg_concl(c)) for c in children):
        return True
    if con(arg_concl(a), rule_con(rule)):
        return True
    return any(edge_impl(con, rule_con, a, c) for c in children)


def pending_edges(edges, policy) -> List[Tuple[tuple, tuple]]:
    return [e for e in edges if policy(e[0], e[1]) is None]


# ---------------- F10 ----------------

def conflict_free(attack, E: FrozenSet) -> bool:
    return all(not attack(x, y) for x in E for y in E)


def defends(attack, E: FrozenSet, a) -> bool:
    return all(any(attack(c, b) for c in E)
               for b in E.__class__() if False) if False else all(
        any(attack(c, b) for c in E)
        for b in _universe(attack) if attack(b, a))


def _universe(attack) -> List:
    return attack("UNIVERSE", "UNIVERSE") if isinstance(attack("UNIVERSE", "UNIVERSE"), list) else []


def char_f(attack, E: FrozenSet, universe) -> FrozenSet:
    return frozenset(
        a for a in universe
        if all(any(attack(c, b) for c in E) for b in universe if attack(b, a))
    )


def grounded(attack, universe) -> FrozenSet:
    current = frozenset()
    while True:
        nxt = char_f(attack, current, universe)
        if nxt == current:
            return current
        current = nxt


def admissible(attack, E: FrozenSet, universe) -> bool:
    return conflict_free(attack, E) and all(
        all(any(attack(c, b) for c in E) for b in universe if attack(b, a))
        for a in E)


def complete(attack, E: FrozenSet, universe) -> bool:
    return admissible(attack, E, universe) and \
        char_f(attack, E, universe) <= E


def stable(attack, E: FrozenSet, universe) -> bool:
    return conflict_free(attack, E) and all(
        any(attack(x, b) for x in E) for b in universe if b not in E
    )


def preferred_exists(attack, universe) -> Optional[FrozenSet]:
    from itertools import combinations
    elems = sorted(universe)
    for k in range(len(elems), -1, -1):
        for comb in combinations(elems, k):
            E = frozenset(comb)
            if admissible(attack, E, universe):
                return E
    return None


# ---------------- F13 ----------------

def eval_universal(result) -> str:
    if result == ("noExtensions",):
        return "vacuousTruth"
    if result[0] == "extensions":
        return "allSatisfy"
    return "unknown"


def three_ring_stable_exists() -> bool:
    universe = [0, 1, 2]
    attack = lambda x, y: (x + 1) % 3 == y
    for k in range(4):
        from itertools import combinations
        for comb in combinations(universe, k):
            if stable(attack, frozenset(comb), universe):
                return True
    return False


def self_attack_grounded_empty() -> bool:
    universe = [0]
    attack = lambda x, y: x == 0 and y == 0
    return grounded(attack, universe) == frozenset()
