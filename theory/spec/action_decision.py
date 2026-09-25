#!/usr/bin/env python3
"""AC-01..AC-04: action and decision contracts (dual-track sentencing,
negotiation, game structure, deviation references).

AC-01 keeps the normative line (deterministic rule-table execution) strictly
separate from the empirical line (certified interval); the Guizhou 23x23
table is SYNTHETIC and says so. AC-02 pins ZOPA existence and monotone
concession ladders (an engineering definition, not a legal rule). AC-03
labels its equilibrium semantics honestly: a conflict-free filter over
attack edges, never "Nash". AC-04 adds the three-reference frame and
stratified tendency priors as explicit inputs that never overwrite the
structural facts.
"""

from __future__ import annotations

from dataclasses import dataclass
from enum import Enum
from typing import FrozenSet, Optional, Sequence, Tuple

from theory.spec.approximation_contract import ApproximationCertificate


# --- AC-01: dual-track sentencing ---


class SentencingTrack(str, Enum):
    NORMATIVE = "NORMATIVE"
    EMPIRICAL = "EMPIRICAL"


SYNTHETIC_TABLE_MARKER = "SYNTHETIC"


@dataclass(frozen=True)
class SyntheticRuleTable:
    """A rule table whose provenance is synthetic, always self-labelled."""

    rows: int
    columns: int
    marker: str
    values: Tuple[Tuple[object, ...], ...]

    def __post_init__(self) -> None:
        if self.marker != SYNTHETIC_TABLE_MARKER:
            raise ValueError("rule table in this contract is synthetic, marker is mandatory")
        if len(self.values) != self.rows or any(
            len(r) != self.columns for r in self.values
        ):
            raise ValueError("rule table shape mismatch")


@dataclass(frozen=True)
class NormativeSentencingResult:
    months: int
    track: SentencingTrack = SentencingTrack.NORMATIVE


@dataclass(frozen=True)
class EmpiricalSentencingResult:
    low: float
    high: float
    certificate: ApproximationCertificate
    track: SentencingTrack = SentencingTrack.EMPIRICAL

    def __post_init__(self) -> None:
        if self.low > self.high:
            raise ValueError("empirical interval reversed")


def synthetic_guizhou_23x23() -> SyntheticRuleTable:
    """Deterministic synthetic 23x23 table (base months). NOT Guizhou law."""

    values = tuple(
        tuple(6 + ((i * 23 + j) % 30) for j in range(23)) for i in range(23)
    )
    return SyntheticRuleTable(
        rows=23, columns=23, marker=SYNTHETIC_TABLE_MARKER, values=values
    )


def run_normative_line(
    table: SyntheticRuleTable, row_index: int, column_index: int
) -> NormativeSentencingResult:
    """Normative line = deterministic rule-table execution, nothing more."""

    if not (0 <= row_index < table.rows and 0 <= column_index < table.columns):
        raise IndexError("rule-table coordinates out of range")
    months = table.values[row_index][column_index]
    if type(months) is not int or months < 0:
        raise ValueError("rule table must carry non-negative integer months")
    return NormativeSentencingResult(months=months)


def build_empirical_line(
    *,
    low: float,
    high: float,
    certificate: ApproximationCertificate,
) -> EmpiricalSentencingResult:
    """Empirical line = certified interval; never a single-point normative
    conclusion."""

    return EmpiricalSentencingResult(low=low, high=high, certificate=certificate)


# --- AC-02: BATNA / ZOPA / concession ladder ---


@dataclass(frozen=True)
class NegotiationPosition:
    reservation_value: float
    batna_value: float


@dataclass(frozen=True)
class ZOPAResult:
    exists: bool
    lower: float
    upper: float


def determine_zopa(*, seller_min: float, buyer_max: float) -> ZOPAResult:
    """ZOPA exists iff the reservation intervals overlap."""

    return ZOPAResult(
        exists=seller_min <= buyer_max,
        lower=seller_min,
        upper=buyer_max,
    )


def validate_concession_ladder(concessions: Tuple[float, ...]) -> bool:
    """Engineering definition: each subsequent concession is no larger than
    the previous one (monotone non-increasing concession sizes)."""

    if not concessions or any(c < 0 for c in concessions):
        return False
    return all(
        concessions[i + 1] <= concessions[i] for i in range(len(concessions) - 1)
    )


# --- AC-03: explicit game structure with argumentation linkage ---


class EquilibriumSemantics(str, Enum):
    """Honest labeling: this contract filters conflict-free profiles over
    attack edges; it is NOT a Nash equilibrium solver."""

    CONFLICT_FREE_FILTER = "CONFLICT_FREE_FILTER"


@dataclass(frozen=True)
class StrategyProfile:
    choices: Tuple[str, ...]


@dataclass(frozen=True)
class AttackEdge:
    attacker: str
    target: str


@dataclass(frozen=True)
class EquilibriumResult:
    profiles: Tuple[StrategyProfile, ...]
    accepted_arguments: FrozenSet[str]
    semantics: EquilibriumSemantics = EquilibriumSemantics.CONFLICT_FREE_FILTER


def solve_equilibrium_contract(
    *,
    profiles: Sequence[StrategyProfile],
    attacks: FrozenSet[AttackEdge],
) -> EquilibriumResult:
    """Conflict-free filter: profiles survive when none of their choice
    arguments is attacked; accepted arguments are those no attacker reaches.

    The semantics label travels with the result so the argumentation-layer
    source is never silently renamed into game-theoretic vocabulary.
    """

    attacked = {edge.target for edge in attacks}
    surviving = tuple(
        profile for profile in profiles if not any(c in attacked for c in profile.choices)
    )
    all_arguments = {c for profile in profiles for c in profile.choices}
    accepted = frozenset(
        arg for arg in all_arguments if arg not in attacked
    )
    return EquilibriumResult(profiles=surviving, accepted_arguments=accepted)


# --- AC-04: deviation references and stratified tendency priors ---


class ReferenceFrame(str, Enum):
    SELF = "SELF"
    PEERS = "PEERS"
    SUPERIOR = "SUPERIOR"


@dataclass(frozen=True)
class TendencyKey:
    court: Optional[str]
    judge: Optional[str]
    region: Optional[str]
    period: str

    def __post_init__(self) -> None:
        if not self.period.strip():
            raise ValueError("tendency stratification requires a period")


@dataclass(frozen=True)
class DeviationVector:
    self_reference: float
    peer_reference: float
    superior_reference: float

    def __post_init__(self) -> None:
        for name, value in (
            ("self_reference", self.self_reference),
            ("peer_reference", self.peer_reference),
            ("superior_reference", self.superior_reference),
        ):
            if value < 0:
                raise ValueError(f"{name} deviation must be non-negative")


@dataclass(frozen=True)
class TendencyPrior:
    key: TendencyKey
    value: float
    weight: float

    def __post_init__(self) -> None:
        if not 0.0 <= self.weight < 1.0:
            raise ValueError("prior weight must be in [0, 1): a prior never fully overwrites the structural fact")


def apply_tendency_prior(
    *, structural_value: float, prior: TendencyPrior
) -> float:
    """Blend the designated tendency into a structural value as a prior;
    the structural fact is never fully overwritten (weight < 1)."""

    return structural_value * (1.0 - prior.weight) + prior.value * prior.weight
