#!/usr/bin/env python3
"""Proof and claim-structure contracts (P-029, P-034, P-035, P-038, P-042,
P-047, P-048, P-049, P-050, P-051, P-052).

Binding duality (P-029): secondary duties attach to primary violations.
Anspruch (P-034): a claim exists exactly when its basis chain is complete;
an unknown basis is UNKNOWN. Agency trichotomy (P-035): agency binds the
principal, representation binds within scope, impersonation binds nobody
absent ratification. Competition relation (P-038): interest, relation and
loss all required. Weight grading (P-042): the weakest factor caps the
grade. But-for (P-047): both directions of the counterfactual required;
one-sided evidence is UNKNOWN. Exemption (P-048) and exclusion (P-050):
each requires its own complete grounds. Filing deadline (P-049): late
evidence barred unless a good-cause extension is present. Free-evaluation
boundary (P-051): a positive record of what formalization cannot decide.
Element-fact-evidence mapping (P-052): every element needs its trace.
"""

from __future__ import annotations

from dataclasses import dataclass
from enum import Enum
from typing import Dict, FrozenSet, Optional, Tuple


class BindingKind(str, Enum):
    """P-029 A26: primary vs secondary norms."""

    PRIMARY = "PRIMARY"
    SECONDARY = "SECONDARY"


@dataclass(frozen=True)
class NormBinding:
    kind: BindingKind
    norm_id: str
    attaches_to: Optional[str] = None  # secondary norm -> primary norm id


def secondary_attaches(violated_primary: Optional[str], n: NormBinding) -> bool:
    """A secondary duty exists only attached to a violated primary norm."""

    return n.kind is BindingKind.SECONDARY and n.attaches_to == violated_primary and violated_primary is not None


@dataclass(frozen=True)
class AnspruchBasis:
    """P-034 A32: one claim basis with its required elements."""

    basis_id: str
    required_elements: FrozenSet[str]


def claim_available(
    bases: Tuple[AnspruchBasis, ...], basis_id: str, satisfied: FrozenSet[str]
) -> Optional[bool]:
    """True iff the named basis's elements are all satisfied; a basis the
    registry does not know is None (UNKNOWN), never a guess."""

    basis = next((b for b in bases if b.basis_id == basis_id), None)
    if basis is None:
        return None
    return basis.required_elements <= satisfied


class AgencyKind(str, Enum):
    """P-035 A33: agency / representation / impersonation."""

    AGENCY = "AGENCY"
    REPRESENTATION = "REPRESENTATION"
    IMPERSONATION = "IMPERSONATION"


def effect_attribution(kind: AgencyKind, within_scope: bool, ratified: bool) -> str:
    """Who is bound: principal (agency), scope-bound (representation),
    nobody without ratification (impersonation)."""

    if kind is AgencyKind.AGENCY:
        return "PRINCIPAL"
    if kind is AgencyKind.REPRESENTATION:
        return "PRINCIPAL_IF_IN_SCOPE" if within_scope else "NONE"
    return "PRINCIPAL" if ratified else "NONE"


@dataclass(frozen=True)
class CompetitionRelation:
    """P-038 A36: interest, relation, loss — all three or nothing."""

    competitive_interest: bool
    competitive_relation: bool
    competitive_loss: bool

    @property
    def established(self) -> bool:
        return self.competitive_interest and self.competitive_relation and self.competitive_loss


@dataclass(frozen=True)
class EvidenceWeight:
    """P-042 A40: reliability/integrity/authenticity cap the grade."""

    reliability: int
    integrity: int
    authenticity: int

    @property
    def grade(self) -> int:
        """The weakest factor caps the whole (white/grey/black banding)."""

        return min(self.reliability, self.integrity, self.authenticity)


@dataclass(frozen=True)
class ButForCase:
    """P-047 A45: one counterfactual probe."""

    occurred_outcome: Optional[bool]      # fact occurred -> outcome?
    non_occurred_outcome: Optional[bool]  # fact absent -> outcome?


def but_for_test(case: ButForCase) -> Optional[bool]:
    """Cause iff occurred->outcome AND non-occurrence->no outcome; any
    missing direction is UNKNOWN."""

    if case.occurred_outcome is None or case.non_occurred_outcome is None:
        return None
    return case.occurred_outcome is True and case.non_occurred_outcome is False


@dataclass(frozen=True)
class ExemptionGround:
    """P-048 A46: an exemption with its own required elements."""

    ground_id: str
    required_elements: FrozenSet[str]


def exempts(ground: ExemptionGround, satisfied: FrozenSet[str]) -> bool:
    return ground.required_elements <= satisfied


class ExclusionKind(str, Enum):
    """P-050 A48: illegality kinds that trigger exclusion."""

    ILLEGALLY_OBTAINED = "ILLEGALLY_OBTAINED"
    VIOLATES_PROCEDURE = "VIOLATES_PROCEDURE"
    UNVERIFIABLE_CHAIN = "UNVERIFIABLE_CHAIN"


def excluded(kinds: FrozenSet[ExclusionKind]) -> bool:
    """Any listed illegality excludes; the list is closed."""

    return bool(kinds)


@dataclass(frozen=True)
class FilingWindow:
    """P-049 A47: deadline with an explicit good-cause extension flag."""

    deadline_day: int
    extended_for_good_cause: bool = False


def evidence_admissible_on_time(filed_day: int, window: FilingWindow) -> bool:
    if filed_day <= window.deadline_day:
        return True
    return window.extended_for_good_cause


@dataclass(frozen=True)
class FreeEvaluationBoundary:
    """P-051 A49: the positive record of the formalization boundary.

    The kernel supplies admissible inputs and their provenance; the judge's
    evaluation act itself is outside the kernel and is recorded as such —
    this contract is the boundary statement, not a decision procedure.
    """

    supplied_inputs: FrozenSet[str]
    judge_evaluation_outside_kernel: bool = True

    def boundary_statement(self) -> str:
        assert self.judge_evaluation_outside_kernel
        return "KERNEL_SUPPLIES_INPUTS_ONLY;EVALUATION_ACT_OUTSIDE_KERNEL=UNKNOWN"


@dataclass(frozen=True)
class ElementTrace:
    """P-052 B8: element -> facts -> evidence traceability."""

    element: str
    facts: FrozenSet[str]
    evidence: FrozenSet[str]


def mapping_complete(
    required_elements: FrozenSet[str], traces: Tuple[ElementTrace, ...]
) -> bool:
    """Complete iff every required element has a non-empty fact AND
    evidence trace."""

    covered = {t.element for t in traces if t.facts and t.evidence}
    return required_elements <= covered
