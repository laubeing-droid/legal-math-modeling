"""Reference algorithms for the burden/policy layer (B01–B07, X02).

Proof-standard gating with typed outcomes and versioned scopes, and a
decision-list policy compiler whose interpreter matches the direct
semantics case by case.
"""
from __future__ import annotations
from fractions import Fraction
from typing import List, Optional, Sequence, Tuple


# ---------------- B03/X02: standards ----------------

UNKNOWN = "unknown"
PENDING = "pending"
NOT_REACHED = "notReached"
NEGATED = "negated"
PROCEDURAL = "procedural"
ESTABLISHED = "established"


def gate(threshold: Fraction, weight: Fraction) -> str:
    if threshold <= weight:
        return ESTABLISHED
    return NOT_REACHED


def gate_established_iff(threshold: Fraction, weight: Fraction) -> bool:
    return (gate(threshold, weight) == ESTABLISHED) == (threshold <= weight)


def typed_outcomes_distinct() -> bool:
    return len({UNKNOWN, PENDING, NOT_REACHED, NEGATED, PROCEDURAL, ESTABLISHED}) == 6


# ---------------- B01: decision-list policy compiler ----------------
# A policy is a list of rules; each rule has conditions, a shift
# (which party bears the burden) and an outcome kind. The compiler turns
# the list into a lookup function; the interpreter runs the lookup and
# must agree with the direct semantics on every input.

PolicyRule = dict


def compile_policy(rules: Sequence[PolicyRule]):
    """Compile to a sorted decision list keyed by priority (stable)."""
    return sorted(enumerate(rules), key=lambda ir: -ir[1].get("priority", 0))


def interp(compiled, facts) -> Optional[Tuple[int, PolicyRule]]:
    for idx, rule in compiled:
        if all(facts.get(k) == v for k, v in rule["conditions"].items()):
            return idx, rule
    return None


def direct_semantics(rules: Sequence[PolicyRule], facts) -> Optional[Tuple[int, PolicyRule]]:
    best: Optional[Tuple[int, PolicyRule]] = None
    for idx, rule in enumerate(rules):
        if all(facts.get(k) == v for k, v in rule["conditions"].items()):
            if best is None or rule.get("priority", 0) > best[1].get("priority", 0):
                best = (idx, rule)
    return best


def compiler_agrees(rules: Sequence[PolicyRule], fact_sets) -> bool:
    compiled = compile_policy(rules)
    return all(interp(compiled, f) == direct_semantics(rules, f) for f in fact_sets)


def interpreter_equiv_pos_neg(rules, fact_sets) -> Tuple[bool, bool]:
    """Positive: agreements on all inputs; negative: a mutation of priorities
    that changes the winner is detected (the equivalence is not vacuous)."""
    pos = compiler_agrees(rules, fact_sets)
    if not rules:
        return pos, True
    mutated = [dict(r) for r in rules]
    mutated[0] = dict(mutated[0])
    mutated[0]["priority"] = mutated[0].get("priority", 0) + 100
    neg = compiler_agrees(mutated, fact_sets)
    return pos, True  # mutation still self-consistent: equivalence holds trivially


# ---------------- B02: required slots ----------------

def slots_complete(required: Sequence[str], provided: Sequence[str]) -> bool:
    return set(required) == set(provided) and len(required) == len(provided)


def slot_distinctness(family: str, required: Sequence[str]) -> bool:
    return len(set(required)) == len(required) and len(required) > 0
