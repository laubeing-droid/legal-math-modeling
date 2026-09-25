#!/usr/bin/env python3
"""ON-01..ON-10: concept-level ontology contracts.

ON-01 lands the Hohfeld eight-concept algebra (opposites and correlatives
are standard tables; both maps are involutions and never map a concept to
itself). ON-02..ON-10 are deliberately minimal machine contracts: the
subsumption operator (completeness = a contract-level iff, not a claim of
legal completeness), the claim-basis chain reusing subsumption, rebuttable
presumptions, explicit admission/fiction rewrites, context parameters with
penumbra intervals, characterization requiring an explicit context,
judgment effect keyed on subject-matter identity, event/action fact typing,
and parameterized attribution principles. No China-specific periods, grades,
or doctrinal rules are invented here.
"""

from __future__ import annotations

from dataclasses import dataclass
from enum import Enum
from typing import Dict, FrozenSet, Optional, Tuple


# --- ON-01: Hohfeld algebra ---


class HohfeldConcept(str, Enum):
    CLAIM_RIGHT = "CLAIM_RIGHT"
    DUTY = "DUTY"
    PRIVILEGE = "PRIVILEGE"
    NO_RIGHT = "NO_RIGHT"
    POWER = "POWER"
    LIABILITY = "LIABILITY"
    IMMUNITY = "IMMUNITY"
    DISABILITY = "DISABILITY"


OPPOSITE: Dict[HohfeldConcept, HohfeldConcept] = {
    HohfeldConcept.CLAIM_RIGHT: HohfeldConcept.NO_RIGHT,
    HohfeldConcept.NO_RIGHT: HohfeldConcept.CLAIM_RIGHT,
    HohfeldConcept.PRIVILEGE: HohfeldConcept.DUTY,
    HohfeldConcept.DUTY: HohfeldConcept.PRIVILEGE,
    HohfeldConcept.POWER: HohfeldConcept.DISABILITY,
    HohfeldConcept.DISABILITY: HohfeldConcept.POWER,
    HohfeldConcept.IMMUNITY: HohfeldConcept.LIABILITY,
    HohfeldConcept.LIABILITY: HohfeldConcept.IMMUNITY,
}

CORRELATIVE: Dict[HohfeldConcept, HohfeldConcept] = {
    HohfeldConcept.CLAIM_RIGHT: HohfeldConcept.DUTY,
    HohfeldConcept.DUTY: HohfeldConcept.CLAIM_RIGHT,
    HohfeldConcept.PRIVILEGE: HohfeldConcept.NO_RIGHT,
    HohfeldConcept.NO_RIGHT: HohfeldConcept.PRIVILEGE,
    HohfeldConcept.POWER: HohfeldConcept.LIABILITY,
    HohfeldConcept.LIABILITY: HohfeldConcept.POWER,
    HohfeldConcept.IMMUNITY: HohfeldConcept.DISABILITY,
    HohfeldConcept.DISABILITY: HohfeldConcept.IMMUNITY,
}


# --- ON-02: subsumption ---


@dataclass(frozen=True)
class SubsumptionSpec:
    required_elements: FrozenSet[str]


@dataclass(frozen=True)
class SubsumptionResult:
    satisfied: FrozenSet[str]
    missing: FrozenSet[str]

    @property
    def complete(self) -> bool:
        return not self.missing


def subsume(*, facts: FrozenSet[str], spec: SubsumptionSpec) -> SubsumptionResult:
    """Contract-level completeness: complete iff every required element is
    among the facts. Not a claim about legal subsumption at large."""

    satisfied = frozenset(facts & spec.required_elements)
    missing = frozenset(spec.required_elements - facts)
    return SubsumptionResult(satisfied=satisfied, missing=missing)


# --- ON-03: claim-basis chain ---


@dataclass(frozen=True)
class ClaimBasisNode:
    key: str
    required_elements: FrozenSet[str]


@dataclass(frozen=True)
class ClaimBasisChain:
    nodes: Tuple[ClaimBasisNode, ...]


def evaluate_claim_basis_chain(
    *, facts: FrozenSet[str], chain: ClaimBasisChain
) -> Tuple[SubsumptionResult, ...]:
    """Each node reuses ON-02 subsumption; the chain never reimplements it."""

    return tuple(
        subsume(facts=facts, spec=SubsumptionSpec(node.required_elements))
        for node in chain.nodes
    )


# --- ON-04: rebuttable presumption ---


@dataclass(frozen=True)
class RebuttablePresumption:
    trigger: str
    presumed_fact: str
    rebuttal_fact: str


@dataclass(frozen=True)
class PresumptionResult:
    presumed: bool
    rebutted: bool
    shifted_fact: Optional[str]


def apply_rebuttable_presumption(
    *, facts: FrozenSet[str], rule: RebuttablePresumption
) -> PresumptionResult:
    """Trigger absent -> not started; trigger present + rebuttal absent ->
    presumed; rebuttal present -> rebutted. Missing evidence is never
    counted as a successful rebuttal."""

    if rule.trigger not in facts:
        return PresumptionResult(presumed=False, rebutted=False, shifted_fact=None)
    if rule.rebuttal_fact in facts:
        return PresumptionResult(presumed=False, rebutted=True, shifted_fact=None)
    return PresumptionResult(
        presumed=True, rebutted=False, shifted_fact=rule.presumed_fact
    )


# --- ON-05: admission and fiction rewrites ---


class RewriteKind(str, Enum):
    ADMISSION = "ADMISSION"
    SERVICE_FICTION = "SERVICE_FICTION"
    DEATH_FICTION = "DEATH_FICTION"


@dataclass(frozen=True)
class RewriteRule:
    kind: RewriteKind
    source_fact: str
    rewritten_fact: str


def rewrite_fact(*, facts: FrozenSet[str], rule: RewriteRule) -> FrozenSet[str]:
    """Explicit rewrite: the source fact is replaced by the rewritten fact;
    nothing else about the fact set changes."""

    if rule.source_fact not in facts:
        return facts
    return (facts - {rule.source_fact}) | {rule.rewritten_fact}


# --- ON-06: context parameters for indeterminate concepts ---


@dataclass(frozen=True)
class ContextInterval:
    lower: float
    upper: float

    def __post_init__(self) -> None:
        if self.lower > self.upper:
            raise ValueError("invalid interval")


@dataclass(frozen=True)
class ContextParameter:
    context_key: str
    penumbra: ContextInterval

    def __post_init__(self) -> None:
        if not self.context_key.strip():
            raise ValueError("context key required")


# --- ON-07: characterization ---


@dataclass(frozen=True)
class Characterization:
    source_id: str
    type_key: str
    context: ContextParameter


def characterize(
    *, source_id: str, type_key: str, context: ContextParameter
) -> Characterization:
    """No characterization without an explicit context parameter."""

    return Characterization(source_id=source_id, type_key=type_key, context=context)


# --- ON-08: judgment effect ---


@dataclass(frozen=True)
class SubjectMatter:
    identity: str


@dataclass(frozen=True)
class JudgmentEffect:
    res_judicata: bool
    enforceable: bool
    same_subject_matter: bool


def judgment_effect(
    *,
    former: SubjectMatter,
    latter: SubjectMatter,
    enforceable: bool,
) -> JudgmentEffect:
    """Machine condition on subject-matter identity only; not an exhaustive
    theory of res judicata."""

    same = former.identity == latter.identity
    return JudgmentEffect(
        res_judicata=same, enforceable=enforceable, same_subject_matter=same
    )


# --- ON-09: legal fact typing ---


class LegalFactType(str, Enum):
    EVENT = "EVENT"
    ACTION = "ACTION"


@dataclass(frozen=True)
class TypedLegalFact:
    fact_id: str
    fact_type: LegalFactType


# --- ON-10: attribution principles ---


class AttributionPrinciple(str, Enum):
    FAULT = "FAULT"
    NO_FAULT = "NO_FAULT"
    EQUITY = "EQUITY"


@dataclass(frozen=True)
class FaultGrade:
    level: int

    def __post_init__(self) -> None:
        if self.level < 0:
            raise ValueError("fault level must be non-negative")


@dataclass(frozen=True)
class AttributionParameters:
    principle: AttributionPrinciple
    fault_grade: Optional[FaultGrade]

    def __post_init__(self) -> None:
        if self.principle is AttributionPrinciple.EQUITY and self.fault_grade is not None:
            raise ValueError("EQUITY must not masquerade as a fault grade")
