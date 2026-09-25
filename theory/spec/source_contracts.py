#!/usr/bin/env python3
"""L1 source-layer concept contracts (P-014..P-024 minus verified anchors).

Source typology with admission-grade distinction (P-014), hierarchy routing
with incomparability left UNKNOWN rather than guessed (P-015), version
transition clauses (P-018), graded precedent binding (P-019), jurisdiction
routing (P-020), one-hop renvoi termination (P-021), scoped public-policy
override (P-022), joint applicable-law selection (P-023), and cause-of-action
routing (P-024). Every lookup fails closed: unknown kinds and missing data
return UNKNOWN, never a fabricated source decision.
"""

from __future__ import annotations

from dataclasses import dataclass
from enum import Enum
from typing import Dict, FrozenSet, Optional, Tuple


class SourceKind(str, Enum):
    """P-014 A1: source typology; admission grade travels with the kind."""

    STATUTE = "STATUTE"
    JUDICIAL_INTERPRETATION = "JUDICIAL_INTERPRETATION"
    GUIDING_CASE = "GUIDING_CASE"
    GAZETTE_CASE = "GAZETTE_CASE"
    CUSTOM = "CUSTOM"
    DOCTRINE = "DOCTRINE"
    SOFT_LAW = "SOFT_LAW"

    @property
    def admission_grade(self) -> str:
        binding = {
            SourceKind.STATUTE,
            SourceKind.JUDICIAL_INTERPRETATION,
        }
        if self in binding:
            return "BINDING"
        if self in (SourceKind.GUIDING_CASE,):
            return "SHALL_REFER"
        return "REFERENCE_ONLY"


def classify_source(raw: str) -> SourceKind:
    """Unknown source strings are rejected, not coerced (P-014 fail-closed)."""

    try:
        return SourceKind(raw.strip().upper())
    except ValueError as exc:
        raise ValueError(f"UNKNOWN_SOURCE_KIND:{raw!r}") from exc


class HierarchyRank(str, Enum):
    """P-015 A2: hierarchy ranks; order is the rank ladder."""

    CONSTITUTION = "CONSTITUTION"
    STATUTE = "STATUTE"
    INTERPRETATION = "INTERPRETATION"
    ADMINISTRATIVE_REGULATION = "ADMINISTRATIVE_REGULATION"
    LOCAL_REGULATION = "LOCAL_REGULATION"
    DEPARTMENTAL_RULE = "DEPARTMENTAL_RULE"


_RANK_ORDER: Dict[HierarchyRank, int] = {
    HierarchyRank.CONSTITUTION: 6,
    HierarchyRank.STATUTE: 5,
    HierarchyRank.INTERPRETATION: 4,
    HierarchyRank.ADMINISTRATIVE_REGULATION: 3,
    HierarchyRank.LOCAL_REGULATION: 2,
    HierarchyRank.DEPARTMENTAL_RULE: 1,
}


@dataclass(frozen=True)
class NormProvision:
    """A provision carrying its rank, enactment day, and specialty flag."""

    provision_id: str
    rank: HierarchyRank
    enacted_day: int
    special: bool = False


def resolve_conflict(
    a: NormProvision, b: NormProvision
) -> Optional[str]:
    """P-015: lex superior / lex posterior / lex specialis routing.

    Higher rank wins outright. Within one rank: newer beats older, except
    older-special versus newer-general, which is incomparable without an
    adjudication rule and returns None (= UNKNOWN), never a guess.
    """

    if a.rank != b.rank:
        return a.provision_id if _RANK_ORDER[a.rank] > _RANK_ORDER[b.rank] else b.provision_id
    if a.enacted_day != b.enacted_day:
        newer, older = (
            (a, b) if a.enacted_day > b.enacted_day else (b, a)
        )
        if older.special and not newer.special:
            return None  # 新的一般 vs 旧的特别：不裁决，UNKNOWN
        return newer.provision_id
    if a.special != b.special:
        return a.provision_id if a.special else b.provision_id
    return None  # 同位同日同性质：需要进一步规则


@dataclass(frozen=True)
class TransitionClause:
    """P-018 A5: a version-transition clause with its trigger fact."""

    from_version: str
    to_version: str
    trigger_fact: str


def apply_transition(
    current_version: str, clause: TransitionClause, facts: FrozenSet[str]
) -> str:
    """Transitions fire only on their trigger fact; otherwise version holds."""

    if current_version != clause.from_version:
        return current_version
    return clause.to_version if clause.trigger_fact in facts else current_version


class PrecedentBinding(str, Enum):
    """P-019 A6: graded binding of precedent."""

    SHALL_REFER = "SHALL_REFER"      # 指导性案例：应当参照
    MAY_REFERENCE = "MAY_REFERENCE"  # 其他案例：可参考


def binding_effect(level: PrecedentBinding, distinguishing_reason: bool) -> str:
    """A shall-refer duty is discharged only by a recorded distinguishing
    reason; may-reference precedent never binds."""

    if level is PrecedentBinding.MAY_REFERENCE:
        return "NON_BINDING"
    return "DISTINGUISHED" if distinguishing_reason else "SHOULD_FOLLOW"


class JurisdictionRuleKind(str, Enum):
    """P-020 A59: jurisdiction routing rule kinds."""

    LEVEL = "LEVEL"
    TERRITORIAL = "TERRITORIAL"
    SPECIALIZED = "SPECIALIZED"
    FOREIGN_RELATED = "FOREIGN_RELATED"


@dataclass(frozen=True)
class JurisdictionRule:
    kind: JurisdictionRuleKind
    court: str


def route_jurisdiction(
    rules: Tuple[JurisdictionRule, ...], applicable_kinds: FrozenSet[JurisdictionRuleKind]
) -> Optional[str]:
    """First applicable rule wins in fixed precedence; no rule → UNKNOWN."""

    precedence = (
        JurisdictionRuleKind.SPECIALIZED,
        JurisdictionRuleKind.LEVEL,
        JurisdictionRuleKind.TERRITORIAL,
        JurisdictionRuleKind.FOREIGN_RELATED,
    )
    for kind in precedence:
        if kind in applicable_kinds:
            for rule in rules:
                if rule.kind is kind:
                    return rule.court
    return None


class RenvoiMode(str, Enum):
    """P-021 A61: renvoi modes with one-hop termination."""

    NONE = "NONE"
    FIRST_RENVOI = "FIRST_RENVOI"
    SECOND_RENVOI = "SECOND_RENVOI"


def renvoi_resolves(forum_law: str, foreign_law: str, foreign_points_back: bool) -> str:
    """One-hop rule: foreign law pointing back applies the forum's own
    substantive law and the chain terminates; no further hops exist."""

    if not foreign_points_back:
        return foreign_law
    return forum_law


@dataclass(frozen=True)
class PublicPolicyOverride:
    """P-022 A62: scoped override of a foreign rule on public-policy grounds."""

    overridden_rule: str
    ground: str


def apply_override(
    rules: FrozenSet[str], override: PublicPolicyOverride
) -> FrozenSet[str]:
    """Only the named rule is displaced; unaffected rules survive intact."""

    return rules - {override.overridden_rule}


@dataclass(frozen=True)
class ApplicableLawSelection:
    """P-023 A63: applicable law = jurisdiction x version joint selection."""

    jurisdiction: str
    version: str


def select_applicable_law(jurisdiction: Optional[str], version: Optional[str]) -> str:
    """Both axes must be present; either missing is UNKNOWN, not defaulted."""

    if not jurisdiction or not version:
        return "UNKNOWN"
    return f"{jurisdiction}::{version}"


@dataclass(frozen=True)
class CauseOfActionRoute:
    """P-024 B24: cause of action -> procedure -> applicable-law route row."""

    cause: str
    procedure: str
    applicable_law: str


def route_cause_of_action(
    routes: Tuple[CauseOfActionRoute, ...], cause: str
) -> Optional[Tuple[str, str]]:
    table = {r.cause: (r.procedure, r.applicable_law) for r in routes}
    return table.get(cause)
