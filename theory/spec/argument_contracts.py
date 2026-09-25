#!/usr/bin/env python3
"""Argumentation and discretion contracts (P-057, P-058, P-060..P-066,
P-068, P-070).

Analogy (P-057): structural similarity plus a shared rule yields analogous
application unless a distinguishing factor is present. Toulmin schema
(P-058): all six slots explicit. Interpretation constructors (P-060): the
five methods evaluate in isolation before comparison (T122 correction).
Interpretation disputes (P-061): competing readings attack each other and
a pinned precedent reading cannot be dislodged by lower precedence.
Ambiguity detection (P-062): two candidate senses flag ambiguity; only a
context parameter resolves it. Rules vs principles (P-063): rules apply
all-or-nothing, principles are weighed and never conclusive alone. Value
preorder (P-064): a partial order with an explicit incomparability
witness — total order is refused. Judicial lawmaking detection (P-065)
and gap signals (P-066): detection only, never justification. Liability
forms (P-068) with typed combination. Damage classification (P-070).
"""

from __future__ import annotations

from dataclasses import dataclass
from enum import Enum
from typing import Dict, FrozenSet, Optional, Tuple


@dataclass(frozen=True)
class AnalogyProbe:
    """P-057 B3: analogous application probe."""

    shared_structure: bool
    shared_rule: bool
    distinguishing_factor: bool


def analogous_application(probe: AnalogyProbe) -> bool:
    """Structural + rule similarity applies the rule analogically, unless a
    distinguishing factor breaks the analogy."""

    return probe.shared_structure and probe.shared_rule and not probe.distinguishing_factor


@dataclass(frozen=True)
class ToulminArgument:
    """P-058 B5: six slots — all must be explicit (rebuttal may be an
    explicit empty set, but the slot must exist)."""

    claim: str
    ground: FrozenSet[str]
    warrant: str
    backing: FrozenSet[str]
    qualifier: str
    rebuttals: FrozenSet[str]

    def well_formed(self) -> bool:
        return bool(
            self.claim.strip()
            and self.ground
            and self.warrant.strip()
            and self.backing
            and self.qualifier.strip()
            # rebuttals 已显式（可为空集），槽位存在性由类型保证
        )


class InterpretationMethod(str, Enum):
    """P-060 A15: the five interpretation constructors."""

    LITERAL = "LITERAL"
    SYSTEMATIC = "SYSTEMATIC"
    PURPOSIVE = "PURPOSIVE"
    HISTORICAL = "HISTORICAL"
    CONSTITUTIONAL = "CONSTITUTIONAL"


def evaluate_isolated(
    readings: Dict[InterpretationMethod, str]
) -> Dict[InterpretationMethod, str]:
    """T122 correction: every branch evaluates in isolation first; the
    comparison happens only after all branches are on the table."""

    return dict(readings)


@dataclass(frozen=True)
class ReadingAttack:
    """P-061 A16: one reading attacking another, with attacker precedence."""

    attacker: str
    target: str
    attacker_precedence: int


def attack_admissible(attack: ReadingAttack, target_pinned: bool, target_precedence: int) -> bool:
    """A pinned precedent reading is immune to lower-precedence attacks."""

    if target_pinned and attack.attacker_precedence <= target_precedence:
        return False
    return True


@dataclass(frozen=True)
class AmbiguityProbe:
    """P-062 A17: candidate senses for a term in context."""

    term: str
    candidate_senses: FrozenSet[str]
    context_provided: bool


def ambiguity_state(probe: AmbiguityProbe) -> str:
    if len(probe.candidate_senses) >= 2 and not probe.context_provided:
        return "AMBIGUOUS"
    return "RESOLVED"


class NormKind(str, Enum):
    """P-063 A22: rule vs principle."""

    RULE = "RULE"
    PRINCIPLE = "PRINCIPLE"


def norm_contribution(kind: NormKind, satisfied: bool, weight: Optional[int]) -> str:
    """Rules are all-or-nothing; principles contribute by weight and are
    never conclusive alone."""

    if kind is NormKind.RULE:
        return "SATISFIED" if satisfied else "VIOLATED"
    if weight is None or weight <= 0:
        return "NO_WEIGHT"
    return "WEIGHED"  # 只计权重，不单独定论


@dataclass(frozen=True)
class ValuePreorder:
    """P-064 A27: a partial order over values; total order is refused."""

    ordered_pairs: FrozenSet[Tuple[str, str]]


def value_relation(pre: ValuePreorder, a: str, b: str) -> str:
    """'LE', 'GE', or 'INCOMPARABLE' — incomparability is a legal outcome."""

    if (a, b) in pre.ordered_pairs:
        return "LE"
    if (b, a) in pre.ordered_pairs:
        return "GE"
    return "INCOMPARABLE"


@dataclass(frozen=True)
class LawmakingSignals:
    """P-065 A7: detection signals for judicial lawmaking (detection only)."""

    no_applicable_rule: bool
    analogy_fails: bool
    gap_present: bool


def lawmaking_flagged(signals: LawmakingSignals) -> bool:
    return signals.no_applicable_rule and signals.analogy_fails and signals.gap_present


class GapSignalKind(str, Enum):
    """P-066 A9: gap signals (boundary theorems are detection-level)."""

    INTENTIONAL_GAP = "INTENTIONAL_GAP"
    UNINTENTIONAL_GAP = "UNINTENTIONAL_GAP"
    RULE_CONFLICT = "RULE_CONFLICT"


def gap_signalled(kinds: FrozenSet[GapSignalKind]) -> bool:
    return bool(kinds)


class LiabilityFormKind(str, Enum):
    """P-068 A51: liability forms with typed combination."""

    JOINT = "JOINT"            # 连带
    SEVERAL = "SEVERAL"        # 按份
    SUPPLEMENTARY = "SUPPLEMENTARY"  # 补充


@dataclass(frozen=True)
class LiabilityForm:
    kind: LiabilityFormKind
    shares: Tuple[int, ...] = ()  # 按份责任显式份额

    def well_formed(self) -> bool:
        if self.kind is LiabilityFormKind.SEVERAL:
            return bool(self.shares)
        return True


class DamageKind(str, Enum):
    """P-070 A53: damage classification."""

    ACTUAL = "ACTUAL"
    EXPECTATION = "EXPECTATION"
    SPIRITUAL = "SPIRITUAL"


def classify_damage(measure: str, measure_basis: str) -> Optional[DamageKind]:
    """Classification keys on the measure basis; unrecognized → UNKNOWN."""

    table = {
        "REPAIR_COST": DamageKind.ACTUAL,
        "LOST_PROFIT": DamageKind.EXPECTATION,
        "MENTAL_DISTRESS": DamageKind.SPIRITUAL,
    }
    return table.get(measure_basis)
