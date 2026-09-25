#!/usr/bin/env python3
"""Negotiation, strategy, and judicial-pressure contracts (P-073, P-074,
P-078..P-087, P-089).

Dual-track sentencing parameters (P-073): responsibility and prevention
tracks are recorded separately and merge only at an explicit declaration
step. Legality assessment (P-074): legal/illegal/violation with an
explicit boundary. Mediation (P-078) and settlement decision (P-079):
expected values and information value as explicit inputs. Plea leniency
(P-080): the five-step process as gated stages. Negotiation ethics
(P-081): a constraint set whose violation voids the tactic. Suit strategy
(P-082) and evidence strategy (P-083): typed choice spaces with
feasibility and EVPI ordering. Appeal decision (P-084): reversal
probability times cost-benefit, explicit. Fee pricing (P-085) and
contingency risk-sharing (P-086). Same-case obligation (P-087): a
shall-follow duty discharged only by a recorded distinguishing reason.
Retrieval duty (P-089): the search report requirement.
"""

from __future__ import annotations

from dataclasses import dataclass
from decimal import Decimal
from enum import Enum
from typing import FrozenSet, Optional, Tuple


@dataclass(frozen=True)
class DualTrackParams:
    """P-073 D3: responsibility and prevention tracks, separately recorded."""

    responsibility_band: Tuple[int, int]
    prevention_band: Tuple[int, int]

    def merged_declaration(self) -> Tuple[int, int]:
        """Tracks merge only here, at the explicit declaration step: the
        floor is the stronger lower bound of the two tracks and the ceiling
        never falls below the floor."""

        lo = max(self.responsibility_band[0], self.prevention_band[0])
        hi = max(self.responsibility_band[1], self.prevention_band[1], lo)
        return (lo, hi)


class LegalityVerdict(str, Enum):
    """P-074 D4: three-way legality assessment."""

    LEGAL = "LEGAL"
    ILLEGAL = "ILLEGAL"
    VIOLATION = "VIOLATION"


def assess_legality(prohibited: bool, unlawful: Optional[bool]) -> LegalityVerdict:
    """Illegal beats violation beats legal; an unknown unlawfulness keeps
    the verdict at violation (not illegal)."""

    if prohibited:
        return LegalityVerdict.ILLEGAL
    if unlawful is None:
        return LegalityVerdict.VIOLATION
    return LegalityVerdict.VIOLATION if unlawful else LegalityVerdict.LEGAL


@dataclass(frozen=True)
class MediationInputs:
    """P-078 D9: neutral evaluation + bargaining inputs."""

    neutral_assessment_low: float
    neutral_assessment_high: float
    plaintiff_reservation: float
    defendant_reservation: float

    def zone(self) -> Optional[Tuple[float, float]]:
        lo = max(self.neutral_assessment_low, self.plaintiff_reservation)
        hi = min(self.neutral_assessment_high, self.defendant_reservation)
        return (lo, hi) if lo <= hi else None


@dataclass(frozen=True)
class SettlementDecision:
    """P-079 D10: EV-based settlement comparison, inputs explicit."""

    ev_settle: float
    ev_litigate: float
    risk_premium: float

    def accept_settlement(self) -> bool:
        return self.ev_settle >= self.ev_litigate - self.risk_premium


PLEA_STAGES = (
    "VOLUNTARINESS",
    "FACT_ADMISSION",
    "SENTENCE_PROPOSAL",
    "COURT_REVIEW",
    "VERDICT",
)


def plea_stage_advance(completed: Tuple[str, ...]) -> Optional[str]:
    """P-080 D11: stages run in fixed order; skipping is impossible."""

    if len(completed) > len(PLEA_STAGES):
        return None
    if any(a != b for a, b in zip(completed, PLEA_STAGES)):
        return None
    if len(completed) == len(PLEA_STAGES):
        return None  # 流程已完成
    return PLEA_STAGES[len(completed)]


class EthicsConstraint(str, Enum):
    """P-081 D12: the negotiation ethics constraint set."""

    NO_FRAUD = "NO_FRAUD"
    NO_COERCION = "NO_COERCION"
    PROFESSIONAL_BOUNDARY = "PROFESSIONAL_BOUNDARY"


def tactic_permitted(
    constraints: FrozenSet[EthicsConstraint], violated: FrozenSet[EthicsConstraint]
) -> bool:
    """Any violated constraint voids the tactic outright."""

    return not (violated & constraints)


@dataclass(frozen=True)
class SuitStrategy:
    """P-082 D13: typed choice with feasibility gates."""

    timing: str
    cause_of_action: str
    jurisdiction_court: str
    preservation_needed: bool
    preservation_ground: bool

    def feasible(self) -> bool:
        """Preservation without a ground makes the whole strategy
        infeasible (fail-closed), regardless of other slots."""

        return not (self.preservation_needed and not self.preservation_ground)


@dataclass(frozen=True)
class EvidenceItemEVPI:
    """P-083 D14: an evidence item with its information value."""

    item_id: str
    evpi: float


def acquisition_order(items: Tuple[EvidenceItemEVPI, ...]) -> Tuple[str, ...]:
    """EVPI descending; ties keep insertion order (deterministic)."""

    indexed = sorted(enumerate(items), key=lambda p: (-p[1].evpi, p[0]))
    return tuple(items_i.item_id for _, items_i in indexed)


@dataclass(frozen=True)
class AppealDecision:
    """P-084 D15: reversal probability times cost-benefit, explicit."""

    reversal_probability: float
    gain_if_reversed: float
    appeal_cost: float

    def appeal_worthwhile(self) -> bool:
        if not 0.0 <= self.reversal_probability <= 1.0:
            raise ValueError("reversal probability out of range")
        return self.reversal_probability * self.gain_if_reversed > self.appeal_cost


class FeeMode(str, Enum):
    """P-085 D16: fee modes with mandatory disclosure."""

    HOURLY = "HOURLY"
    CONTINGENCY = "CONTINGENCY"
    HYBRID = "HYBRID"


def fee_quote(mode: FeeMode, disclosed: bool) -> Optional[str]:
    """An undisclosed fee mode cannot quote (fail-closed)."""

    if not disclosed:
        return None
    return f"QUOTE::{mode.value}"


@dataclass(frozen=True)
class ContingencyTerms:
    """P-086 D17: win-rate x fee-rate risk sharing with a cap."""

    win_rate: float
    fee_rate: float
    cap: float

    def expected_fee(self, base: Decimal) -> Decimal:
        rate = Decimal(str(self.win_rate))
        return min(rate * self.fee_rate * base, self.cap)


@dataclass(frozen=True)
class SameCaseObligation:
    """P-087 D18: shall-follow duty for a guiding case."""

    guiding_case_id: str
    distinguishing_reason_recorded: bool

    def discharge(self) -> str:
        if self.distinguishing_reason_recorded:
            return "DISTINGUISHED_WITH_REASON"
        return "SHOULD_FOLLOW"


@dataclass(frozen=True)
class RetrievalDutyRecord:
    """P-089 D20: the search-report filing requirement."""

    search_performed: bool
    report_filed: bool

    def compliant(self) -> bool:
        return self.search_performed and self.report_filed
