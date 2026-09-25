#!/usr/bin/env python3
"""Computation contracts (P-096..P-103, P-114, P-117).

Segmented interest (P-096): accrual over explicit segments, the whole
equals the sum of parts. Payment allocation (P-097): ordered allocation
with conservation and remainder carried. Penalty reduction (P-098):
excessive penalties reduce to an explicit benchmark band. Tax brackets
(P-099): progressive table execution. Damage computation (P-100): a
per-item formula registry. Enforcement computation (P-102): delay
interest plus preservation guarantee. Smart-contract semantics (P-103):
consent-locked state transitions. Logic-probability bridge (P-114):
deduction entails probability one, and probability one never fabricates
a deduction — the bridge is one-way. Text similarity (P-117): output is
capped at candidate grade and never asserts structural equivalence.
"""

from __future__ import annotations

from dataclasses import dataclass
from decimal import Decimal
from enum import Enum
from typing import Dict, FrozenSet, Optional, Tuple

D = Decimal


@dataclass(frozen=True)
class InterestSegment:
    """P-096 B12: one segment with its day span and rate."""

    from_day: int
    to_day: int
    rate: D

    @property
    def days(self) -> int:
        return self.to_day - self.from_day


def segmented_interest(principal: D, segments: Tuple[InterestSegment, ...]) -> D:
    """Whole-period interest = sum of segment interests (refinement)."""

    return sum((principal * s.rate * D(s.days) for s in segments), D(0))


@dataclass(frozen=True)
class DebtItem:
    debt_id: str
    amount: D
    order: int


def allocate_payment(
    payment: D, debts: Tuple[DebtItem, ...]
) -> Tuple[Dict[str, D], D]:
    """P-097 B15: order-based allocation; total allocated never exceeds the
    payment; the remainder is carried, never invented."""

    remaining = payment
    allocation: Dict[str, D] = {}
    for debt in sorted(debts, key=lambda d: d.order):
        if remaining <= 0:
            allocation[debt.debt_id] = D(0)
            continue
        applied = min(remaining, debt.amount)
        allocation[debt.debt_id] = applied
        remaining -= applied
    return allocation, remaining


def reduce_penalty(amount: D, benchmark: Tuple[D, D], excessive: bool) -> D:
    """P-098 B13: an excessive penalty reduces into the benchmark band;
    a non-excessive one is untouched."""

    if not excessive:
        return amount
    lo, hi = benchmark
    if amount < lo:
        return lo
    if amount > hi:
        return hi
    return amount


@dataclass(frozen=True)
class TaxBracket:
    """P-099 B16: one progressive bracket."""

    up_to: Optional[int]  # None = top bracket
    rate: D


def progressive_tax(taxable: int, brackets: Tuple[TaxBracket, ...]) -> D:
    """Progressive table execution: each bracket taxes only its slice."""

    tax = D(0)
    lower = 0
    for bracket in brackets:
        upper = bracket.up_to if bracket.up_to is not None else taxable
        if taxable <= lower:
            break
        slice_ = min(taxable, upper) - lower
        if slice_ > 0:
            tax += D(slice_) * bracket.rate
        lower = upper
    return tax


def compute_damage_item(formula_id: str, registry: Dict[str, D], amounts: Dict[str, D]) -> Optional[D]:
    """P-100 B17: per-item formula registry lookup; unknown item → UNKNOWN."""

    formula = registry.get(formula_id)
    if formula is None:
        return None
    return formula * amounts.get("base", D(0))


def delay_interest(principal: D, daily_rate: D, days: int) -> D:
    """P-102 B20: enforcement delay interest (deterministic days)."""

    if days < 0:
        raise ValueError("days cannot be negative")
    return principal * daily_rate * D(days)


class ContractState(str, Enum):
    """P-103 B22: consent-locked control flow."""

    DRAFT = "DRAFT"
    LOCKED = "LOCKED"
    EXECUTED = "EXECUTED"
    TERMINATED = "TERMINATED"


_LEGAL_TRANSITIONS = {
    (ContractState.DRAFT, ContractState.LOCKED),
    (ContractState.LOCKED, ContractState.EXECUTED),
    (ContractState.LOCKED, ContractState.TERMINATED),
    (ContractState.EXECUTED, ContractState.TERMINATED),
}


def transition_contract_state(current: ContractState, target: ContractState, consent_recorded: bool) -> ContractState:
    """Only listed transitions with recorded consent move the state."""

    if (current, target) not in _LEGAL_TRANSITIONS:
        return current
    if not consent_recorded:
        return current
    return target


def deduction_implies_probability_one() -> str:
    """P-114 B10: the bridge runs one way — a deduction forces probability
    one; probability one alone fabricates no deduction."""

    return "DEDUCTION=>P1;P1=~>DEDUCTION"


@dataclass(frozen=True)
class SimilarityToolOutput:
    """P-117 B32: text-similarity tool output, capped at candidate grade."""

    score: float
    asserted_structural_equivalence: bool = False

    def grade(self) -> str:
        """Similarity never upgrades to structure; the flag, if ever set,
        marks the output invalid rather than promoted."""

        if self.asserted_structural_equivalence:
            return "INVALID_OVERREACH"
        return "CANDIDATE_ONLY"
