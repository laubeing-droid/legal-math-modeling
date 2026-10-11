"""Independent checker for the T122/T123 interpretation layer (J.7 discipline).

This module deliberately re-implements the layer's semantics with its own
inline logic instead of importing the reference functions: the adoption gate,
the rule-base discipline, branch attacks/compatibility, named priority
resolution, the referral set and the branch-isolation gate are all re-derived
here from the frozen carriers alone.  It shares only the immutable data
classes/enums of ``interpretation_ref`` — never its functions — and never
calls the evaluator.

Lean contract: JurisLean.Seams.UnifiedW4Interp (T122/T123).
"""
from __future__ import annotations

from dataclasses import dataclass
from typing import FrozenSet, Iterable, Tuple

from tools.full_math.implementation.interpretation_ref import (
    BranchDerivation,
    InterpBranch,
    InterpCandidate,
    InterpLayer,
    InterpMethod,
    PriorityPair,
    RuleAst,
)


@dataclass(frozen=True)
class CheckReport:
    ok: bool
    reasons: Tuple[str, ...]

    @classmethod
    def pass_(cls) -> "CheckReport":
        return cls(True, ())

    @classmethod
    def fail(cls, *reasons: str) -> "CheckReport":
        return cls(False, tuple(reasons))


# ---------------------------------------------------------------------------
# Inline semantic re-derivations（与主实现零函数共享）
# ---------------------------------------------------------------------------


def _adoptable(c: InterpCandidate) -> bool:
    # §3.1: 采用/排除解释仍须法定权限与具名理由
    return c.reason_id is not None and c.reason_id != "" \
        and c.authority_id is not None


def _conflict(x: InterpCandidate, y: InterpCandidate) -> bool:
    return x.target == y.target and x.rule != y.rule


def _attack(a: InterpBranch, b: InterpBranch, by_id) -> bool:
    return any(_conflict(by_id[x], by_id[y])
               for x in a.adopted for y in b.adopted)


def _has_priority(pairs, s: str, n: str) -> bool:
    return any(p.superior == s and p.inferior == n for p in pairs)


def _resolved(pairs, pool: Tuple[InterpCandidate, ...]):
    return tuple(
        c for c in pool
        if not any(s.candidate_id != c.candidate_id
                   and _has_priority(pairs, s.candidate_id, c.candidate_id)
                   for s in pool))


def _isolation_ok(branch: InterpBranch, d: BranchDerivation) -> bool:
    return d.cited_premises <= branch.private_premises


# ---------------------------------------------------------------------------
# Public checks
# ---------------------------------------------------------------------------


def check_interp_layer(cands: Iterable[InterpCandidate],
                       pairs: Iterable[PriorityPair],
                       layer: InterpLayer) -> CheckReport:
    """Differential check of an InterpLayer against the inline semantics:
    adoption gate, rule-base discipline, per-candidate branch preservation,
    attacks, priority resolution, referral, and branch non-collapse."""

    cands = tuple(cands)
    pairs = tuple(pairs)
    by_id = {c.candidate_id: c for c in cands}
    problems = []

    pool = tuple(c for c in cands if _adoptable(c))
    pool_ids = frozenset(c.candidate_id for c in pool)
    if pool_ids != frozenset(layer.pool):
        problems.append("adoptable pool mismatch")

    expected_resolved = frozenset(c.candidate_id for c in _resolved(pairs, pool))
    if expected_resolved != frozenset(layer.resolved):
        problems.append("priority resolution mismatch")

    expected_branches = {
        c.candidate_id for c in pool} == {b.branch_id for b in layer.branches}
    if not expected_branches:
        problems.append("branch preservation mismatch (merged or dropped)")
    for b in layer.branches:
        if b.adopted != frozenset({b.branch_id}):
            problems.append(f"branch {b.branch_id} adopted set malformed")
        if b.private_premises != frozenset(by_id[b.branch_id].input.context_ids):
            problems.append(f"branch {b.branch_id} premises malformed")

    expected_attacks = frozenset(
        (a.branch_id, b.branch_id)
        for a in layer.branches for b in layer.branches
        if a.branch_id < b.branch_id and _attack(a, b, by_id))
    if expected_attacks != frozenset(layer.attacks):
        problems.append("attack relation mismatch")

    expected_referral = frozenset(
        (x.candidate_id, y.candidate_id)
        for x in pool for y in pool
        if x.candidate_id < y.candidate_id
        and _conflict(x, y)
        and not _has_priority(pairs, x.candidate_id, y.candidate_id)
        and not _has_priority(pairs, y.candidate_id, x.candidate_id))
    if expected_referral != frozenset(layer.referral):
        problems.append("referral (unadjudicated conflict) mismatch")

    # rule-base discipline: only ADOPTED readings contribute (未采用候选不
    # 进入无条件规则库; a candidate excluded by a named priority edge is
    # excluded, not adopted).  Every rule in the base must be carried by a
    # resolved candidate; any other candidate's rule may appear only through
    # a resolved carrier of the same rule.
    base_rules = frozenset(layer.rule_base)
    resolved_cands = _resolved(pairs, pool)
    resolved_rules = frozenset(c.rule for c in resolved_cands)
    resolved_ids = frozenset(c.candidate_id for c in resolved_cands)
    if base_rules != resolved_rules:
        problems.append("rule base mismatch against adopted readings")
    for c in cands:
        if c.candidate_id not in resolved_ids and c.rule in base_rules \
                and c.rule not in resolved_rules:
            problems.append(
                f"non-adopted candidate {c.candidate_id} entered the rule base")

    if problems:
        return CheckReport.fail(*problems)
    return CheckReport.pass_()


def check_branch_isolation(branch: InterpBranch,
                           accepted: Iterable[BranchDerivation],
                           rejected: Iterable[BranchDerivation]) -> CheckReport:
    """Isolation gate differential: accepted derivations cite only this
    branch's private premises; every claimed-rejected derivation actually
    cites a foreign premise (T123: 引用另支前提被拒)."""

    problems = []
    for d in accepted:
        if not _isolation_ok(branch, d):
            problems.append(
                f"derivation {d.derivation_id} cites foreign premises but "
                "was reported accepted")
    for d in rejected:
        if _isolation_ok(branch, d):
            problems.append(
                f"derivation {d.derivation_id} cites only own premises but "
                "was reported rejected")
    if problems:
        return CheckReport.fail(*problems)
    return CheckReport.pass_()


def check_cross_branch_rejection(a: InterpBranch, b: InterpBranch,
                                 d: BranchDerivation) -> CheckReport:
    """The T123 counterexample gate: with disjoint premises, a derivation
    citing B's premise must be rejected by A's isolation gate."""

    if a.private_premises & b.private_premises:
        return CheckReport.fail("premises not disjoint; gate test vacuous")
    if d.cited_premises & b.private_premises:
        if d.cited_premises <= a.private_premises:
            return CheckReport.fail(
                "foreign premise is also local; rejection not exercised")
        return CheckReport.pass_()
    return CheckReport.fail("derivation cites no foreign premise; nothing to reject")


def check_method_set() -> CheckReport:
    """T122 five-method discipline: exactly five constructors, analogy is a
    gap-filling constructor OUTSIDE the set (P066 修正注记)."""

    expected = {
        InterpMethod.LITERAL, InterpMethod.SYSTEMATIC,
        InterpMethod.TELEOLOGICAL, InterpMethod.HISTORICAL,
        InterpMethod.CONSTITUTIONAL,
    }
    if set(InterpMethod) != expected:
        return CheckReport.fail("InterpMethod is not exactly the five methods")
    return CheckReport.pass_()
