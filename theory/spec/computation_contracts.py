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

from dataclasses import dataclass, field
from decimal import Decimal
from enum import Enum
from fractions import Fraction
from typing import Dict, FrozenSet, Optional, Sequence, Tuple

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
    amount: D | Fraction
    order: int


def allocate_payment(
    payment: D | Fraction, debts: Tuple[DebtItem, ...]
) -> Tuple[Dict[str, D | Fraction], D | Fraction]:
    """P-097 B15: order-based allocation; total allocated never exceeds the
    payment; the remainder is carried, never invented."""

    remaining = payment
    allocation: Dict[str, D | Fraction] = {}
    for debt in sorted(debts, key=lambda d: d.order):
        if remaining <= 0:
            allocation[debt.debt_id] = D(0)
            continue
        applied = min(remaining, debt.amount)
        allocation[debt.debt_id] = applied
        remaining -= applied
    return allocation, remaining


@dataclass(frozen=True)
class TypedDebt:
    """An amount in one declared unit, with the parties and obligation identified."""

    debt_id: str
    kind: str
    amount: Fraction
    debtor: str
    creditor: str
    obligation: str
    is_due: bool = False
    due_day: Optional[int] = None
    security: Optional[Fraction] = None  # None is unknown; zero is unsecured.
    burden: Optional[Fraction] = None


@dataclass(frozen=True)
class Appropriation:
    basis: str
    order: Tuple[str, ...] = ()
    burden_basis: str = ""
    due_day_basis: str = ""


@dataclass(frozen=True)
class AllocationResult:
    allowed: bool
    reason: str
    allocation: Dict[str, Fraction] = field(default_factory=dict)
    residual: Dict[str, Fraction] = field(default_factory=dict)
    remainder: Fraction = Fraction(0)


def allocate_grounded(
    payment: Fraction, debts: Sequence[TypedDebt], basis: Appropriation
) -> AllocationResult:
    """P-097: derive ordering before consuming the existing ordered allocator.

    Absorbed from the uncommitted 2026-10-15 appropriation candidate. The
    560(2) cascade uses declared security/burden/date comparisons; 561 uses
    costs, interest, principal within one identified obligation. Amounts use
    exact rational shares: rounding to currency units is not inferred here.
    Statutory source: Civil Code 560/561, https://enipc.court.gov.cn/zh-cn/news/view-371.html
    """

    payment = Fraction(payment)
    amounts = {d.debt_id: Fraction(d.amount) for d in debts}
    zero = {d.debt_id: Fraction(0) for d in debts}

    def refused(reason: str) -> AllocationResult:
        return AllocationResult(False, reason, zero, amounts, payment)

    if basis.basis not in {"party_agreement", "debtor_designation", "statute_560_2", "statute_561"}:
        return refused("NO_BASIS" if basis.basis == "none" else "UNKNOWN_BASIS")
    if not debts:
        return refused("EMPTY_ROSTER")
    if len(amounts) != len(debts) or any(not d.debt_id for d in debts):
        return refused("DUPLICATE_OR_EMPTY_DEBT_ID")
    if payment < 0 or any(amount < 0 for amount in amounts.values()):
        return refused("NEGATIVE_AMOUNT")
    if any(d.security is not None and d.security < 0 for d in debts):
        return refused("NEGATIVE_SECURITY")
    if any(not d.debtor or not d.creditor or not d.obligation for d in debts):
        return refused("PARTIES_OR_OBLIGATION_MISSING")
    if len({(d.debtor, d.creditor) for d in debts}) != 1:
        return refused("PARTIES_MISMATCH")
    kinds = {d.kind for d in debts}
    if "" in kinds:
        return refused("KIND_MISSING")
    if basis.basis in {"debtor_designation", "statute_560_2"} and len(kinds) != 1:
        return refused("KIND_PRECONDITION_FAILED")

    if basis.basis in {"party_agreement", "debtor_designation", "statute_561"}:
        if basis.basis == "statute_561":
            rank = {"cost_of_realisation": 0, "interest": 1, "principal": 2}
            if not kinds <= rank.keys() or len({d.obligation for d in debts}) != 1:
                return refused("OBLIGATION_OR_KIND_MISMATCH")
            if len(kinds) != len(debts):
                return refused("UNRESOLVED_SAME_RANK")
            ordered = sorted(debts, key=lambda d: rank[d.kind])
        else:
            if len(basis.order) != len(debts) or set(basis.order) != set(amounts):
                return refused("ORDER_NOT_A_PERMUTATION")
            by_id = {d.debt_id: d for d in debts}
            ordered = [by_id[key] for key in basis.order]
        allocated, remaining = allocate_payment(
            payment, tuple(DebtItem(d.debt_id, amounts[d.debt_id], i) for i, d in enumerate(ordered))
        )
        allocation = {key: Fraction(value) for key, value in allocated.items()}
    else:
        allocation = dict(zero)
        remaining = payment
        total_due = sum(amounts.values(), Fraction(0))
        if total_due <= payment:
            return AllocationResult(True, basis.basis, amounts, zero, payment - total_due)
        roster = [d for d in debts if amounts[d.debt_id] > 0]
        while remaining > 0 and roster:
            pool = [d for d in roster if d.is_due] or roster
            if len(pool) > 1:
                if any(d.security is None for d in pool):
                    return refused("SECURITY_UNKNOWN")
                least = min(d.security for d in pool)
                pool = [d for d in pool if d.security == least]
            if len(pool) > 1:
                if not basis.burden_basis.strip() or any(d.burden is None for d in pool):
                    return refused("BURDEN_BASIS_MISSING")
                heaviest = max(d.burden for d in pool)
                pool = [d for d in pool if d.burden == heaviest]
            if len(pool) > 1:
                if not basis.due_day_basis.strip() or any(d.due_day is None for d in pool):
                    return refused("DUE_DAY_MISSING")
                earliest = min(d.due_day for d in pool)
                pool = [d for d in pool if d.due_day == earliest]
            total = sum((amounts[d.debt_id] for d in pool), Fraction(0))
            applied = min(remaining, total)
            for debt in pool:
                allocation[debt.debt_id] = applied * amounts[debt.debt_id] / total
            remaining -= applied
            paid_group = {d.debt_id for d in pool}
            roster = [d for d in roster if d.debt_id not in paid_group]
    return AllocationResult(
        True, basis.basis, allocation,
        {key: amount - allocation[key] for key, amount in amounts.items()}, Fraction(remaining),
    )


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
