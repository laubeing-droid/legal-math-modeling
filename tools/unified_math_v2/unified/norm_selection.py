"""Norm selection over named exclusion graphs (plan §3.1–§3.2, L02, U03).

Given the candidate set C of norms that passed authority/version/scope/
time checks, and the exclusion relation D produced by named conflict
rules, a profile is *stable* on S ⊆ C exactly when

    (∀ a b ∈ S, ¬D(a, b))  ∧  (∀ n ∈ C \\ S, ∃ s ∈ S, D(s, n)).

The second conjunct quantifies over ALL non-adopted candidates, not only
those involved in a conflict: an isolated candidate with no excluder must
be adopted in every solution, so the global-maximal screening is not the
algorithm (A beats B, B beats C, A and C compatible keeps {A, C}).

Same-rank conflicts the law lets the chooser decide enter D as
bidirectional edges (both directions), preserving both legal choices.
Same-rank conflicts the law routes to referral enter ``escalation_pairs``:
they ban co-adoption without creating exclusion edges, which typically
empties the family and yields an ESCALATE result instead of a fabricated
choice.  Exclusion cycles may have no solution at all; that is reported
as NORM_CONFLICT, never folded into input well-formedness.
"""

from __future__ import annotations

from dataclasses import dataclass
from enum import Enum
from itertools import combinations
from typing import FrozenSet, Iterable, Optional, Tuple

MAX_CANDIDATES = 20  # 2^20 subsets; larger profiles fail closed, not silently


@dataclass(frozen=True)
class NormCandidate:
    """One applicable-norm candidate: identity plus the validity window it
    passed.  Pre-invalidated norms never reach this type (§3.1)."""

    norm_id: str
    jurisdiction: str
    from_day: Optional[int] = None
    to_day: Optional[int] = None


class SelectionStatus(str, Enum):
    RESOLVED = "RESOLVED"            # nonempty family of stable selections
    ESCALATE = "ESCALATE"            # referral paths required by law
    NORM_CONFLICT = "NORM_CONFLICT"  # no stable selection exists
    EMPTY_CANDIDATES = "EMPTY_CANDIDATES"


@dataclass(frozen=True)
class NormSelectionResult:
    status: SelectionStatus
    selections: Tuple[FrozenSet[str], ...]
    refer_pairs: Tuple[FrozenSet[str], ...] = ()

    def __post_init__(self) -> None:
        for s in self.selections:
            if type(s) is not frozenset:
                raise ValueError("selections are frozensets of norm ids")
        if self.status is SelectionStatus.RESOLVED and not self.selections:
            raise ValueError("RESOLVED requires at least one selection")
        if self.status is SelectionStatus.ESCALATE and not self.refer_pairs:
            raise ValueError("ESCALATE requires the pairs to refer")


def _is_stable(
    subset: FrozenSet[str],
    candidates: FrozenSet[str],
    exclusions: FrozenSet[Tuple[str, str]],
    escalation_pairs: FrozenSet[FrozenSet[str]],
) -> bool:
    # A selection is a SUBSET of the candidates (Lean's first conjunct).
    if not subset <= candidates:
        return False
    # Internal freedom: no exclusion edge — including self-loops — inside S.
    for a in subset:
        for b in subset:
            if (a, b) in exclusions:
                return False
    # Escalation pairs ban co-adoption without creating exclusion edges.
    for pair in escalation_pairs:
        if pair <= subset:
            return False
    # Coverage: EVERY non-adopted candidate is excluded by an adopted one.
    for n in candidates - subset:
        if not any((s, n) in exclusions for s in subset):
            return False
    return True


def enumerate_stable_selections(
    candidates: Iterable[NormCandidate],
    exclusions: FrozenSet[Tuple[str, str]],
    escalation_pairs: FrozenSet[FrozenSet[str]] = frozenset(),
) -> NormSelectionResult:
    """Enumerate ALL stable selections S ⊆ C of the exclusion profile."""

    cand_ids = frozenset(c.norm_id for c in candidates)
    if not cand_ids:
        return NormSelectionResult(SelectionStatus.EMPTY_CANDIDATES, ())
    if len(cand_ids) > MAX_CANDIDATES:
        raise ValueError(
            f"exclusion profile with {len(cand_ids)} candidates exceeds the "
            f"exhaustive-enumeration budget ({MAX_CANDIDATES}); split by "
            "issue/aspect/period instance instead of widening the domain"
        )
    for a, b in exclusions:
        if a not in cand_ids or b not in cand_ids:
            raise ValueError(f"exclusion edge outside candidate set: {(a, b)}")
    for pair in escalation_pairs:
        if not pair <= cand_ids:
            raise ValueError(f"escalation pair outside candidate set: {set(pair)}")

    ordered = tuple(sorted(cand_ids))
    found: Tuple[FrozenSet[str], ...] = tuple(
        frozenset(combo)
        for k in range(len(ordered) + 1)
        for combo in combinations(ordered, k)
        if _is_stable(frozenset(combo), cand_ids, exclusions, escalation_pairs)
    )
    if found:
        return NormSelectionResult(SelectionStatus.RESOLVED, found)
    if escalation_pairs:
        return NormSelectionResult(
            SelectionStatus.ESCALATE, (), tuple(sorted(escalation_pairs))
        )
    return NormSelectionResult(SelectionStatus.NORM_CONFLICT, ())


# ---------------------------------------------------------------------------
# §3.2 helpers: strictest-common compliance join, renvoi routing, override
# ---------------------------------------------------------------------------


def strictest_common_actions(action_sets: Iterable[FrozenSet[str]]) -> Tuple[FrozenSet[str], bool]:
    """Parallel-compliance intersection.  Under reverse inclusion
    (“stricter” = smaller allowed set) the intersection is the least upper
    bound: A∩B ⊆ A, B and any C ⊆ A, B satisfies C ⊆ A∩B.  An empty
    intersection means joint compliance is infeasible — reported via the
    flag, never as one side's invalidity."""

    sets = tuple(action_sets)
    if not sets:
        raise ValueError("at least one jurisdiction's allowed set required")
    result = frozenset(set.intersection(*(set(s) for s in sets)))
    return result, len(result) == 0


class RenvoiMode(str, Enum):
    FORBIDDEN = "FORBIDDEN"        # target law applied directly, no re-routing
    ONE_STEP = "ONE_STEP"          # one remission to the referenced law
    TRAVERSE = "TRAVERSE"          # walk the jurisdiction graph with a visited set


@dataclass(frozen=True)
class RenvoiOutcome:
    mode: RenvoiMode
    terminal: Optional[str]
    visited: Tuple[str, ...]
    circular: bool

    def __post_init__(self) -> None:
        if self.mode is RenvoiMode.FORBIDDEN and self.terminal is None:
            raise ValueError("FORBIDDEN routing still names the target law")
        if self.circular and self.terminal is not None:
            raise ValueError("a circular route has no terminal law")


def route_renvoi(
    mode: RenvoiMode,
    start: str,
    references: dict = frozenset(),  # (jurisdiction -> referenced jurisdiction)
) -> RenvoiOutcome:
    """Renvoi routing under one of the three declared modes.

    FORBIDDEN returns the start jurisdiction's own law.  ONE_STEP follows
    a single remission.  TRAVERSE walks the reference graph keeping a
    visit record; an unresolved cycle is a named routing dispute, not an
    infinite loop."""

    if mode is RenvoiMode.FORBIDDEN:
        return RenvoiOutcome(mode, start, (start,), False)
    if mode is RenvoiMode.ONE_STEP:
        nxt = references.get(start)
        if nxt is None:
            return RenvoiOutcome(mode, start, (start,), False)
        return RenvoiOutcome(mode, nxt, (start, nxt), False)
    # TRAVERSE
    visited = [start]
    current = start
    while True:
        nxt = references.get(current)
        if nxt is None:
            return RenvoiOutcome(mode, current, tuple(visited), False)
        if nxt in visited:
            return RenvoiOutcome(mode, None, tuple(visited), True)
        visited.append(nxt)
        current = nxt


def apply_override(
    scope: FrozenSet[str],
    old_rules: Tuple[Tuple[str, str], ...],
    new_rule: Tuple[str, str],
) -> Tuple[Tuple[str, str], ...]:
    """override(n, S, n') replaces only rule instances inside the declared
    scope S; instances outside the scope are preserved verbatim, so a
    consumer that does not read S's derivation tree can still reuse the
    untouched part as-is."""

    replaced = frozenset(scope)
    kept = tuple(rule for rule in old_rules if rule[0] not in replaced)
    return kept + (new_rule,)
