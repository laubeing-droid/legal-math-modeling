#!/usr/bin/env python3
"""Kernel object carriers for object definition v3 (TY-01..TY-04).

These frozen records mirror the minimal structures declared in
`JurisLean/LegalModelV2.lean`: Relation (clause 1, shared constraints),
LegalPower (clause 5, three non-implying modalities), Event / EventHistory
(clauses 4 and 6, the time-structure carrier H), and Jurisdiction (the
jurisdiction axis J of the condition group). Python records carry
serializable contracts only; Lean-definition authority stays with the
registry file. Selector semantics (Eval, ApplicableNorm resolution) are
EV-pool targets and are deliberately not implemented here.
"""

from __future__ import annotations

from dataclasses import dataclass
from enum import Enum
from typing import Tuple


class SharedConstraintKind(str, Enum):
    """Constraints a relation whole may carry (object definition v3 clause 1)."""

    SAME_LOSS = "SAME_LOSS"
    COMPETING_EXCLUSIVE = "COMPETING_EXCLUSIVE"
    JOINT_REDUCTION = "JOINT_REDUCTION"


class JurisdictionRoute(str, Enum):
    """Jurisdiction routing axis (TY-04)."""

    MAINLAND = "MAINLAND"
    HONG_KONG = "HONG_KONG"
    UNITED_STATES = "UNITED_STATES"
    OTHER = "OTHER"


@dataclass(frozen=True)
class SharedConstraint:
    """One shared constraint linking several relations of the whole."""

    kind: SharedConstraintKind
    memberRelations: Tuple[str, ...]
    subjectRef: str = ""

    def __post_init__(self) -> None:
        if not self.memberRelations:
            raise ValueError("SharedConstraint needs at least one member relation")
        if self.kind is SharedConstraintKind.SAME_LOSS and not self.subjectRef:
            raise ValueError("SAME_LOSS constraint must name the shared loss")


@dataclass(frozen=True)
class Relation:
    """TY-01: a legal relation; shared constraints ride on the whole."""

    relationId: str
    parties: Tuple[str, ...]
    kind: str
    sharedConstraints: Tuple[SharedConstraint, ...] = ()


@dataclass(frozen=True)
class LegalPower:
    """TY-02: Power / Obligation / Occurred as independent fields.

    Clause 5: no unconditional implication among the three modalities;
    specific norms may still establish conditional derivation elsewhere.
    """

    powerId: str
    powerGranted: bool
    obligationImposed: bool
    occurred: bool


@dataclass(frozen=True)
class Event:
    """TY-03: an event; the member of history H."""

    eventId: str
    atDay: int
    eventType: str


@dataclass(frozen=True)
class EventHistory:
    """TY-03: the event-history time structure H (insertion order preserved)."""

    events: Tuple[Event, ...]


@dataclass(frozen=True)
class Jurisdiction:
    """TY-04: the jurisdiction axis J of the condition group."""

    route: JurisdictionRoute
    code: str = ""

    def __post_init__(self) -> None:
        if self.route is JurisdictionRoute.OTHER and not self.code:
            raise ValueError("Jurisdiction route OTHER must carry an explicit code")


@dataclass(frozen=True)
class ApplicableNormQuery:
    """Signature carrier for A(J, V, q, H, t) (object definition v3 clause 6).

    H and t are both mandatory arguments; neither alone fixes the norm
    version. Resolution semantics are the EV-04 target, not this record.
    """

    jurisdiction: Jurisdiction
    normEnv: str
    question: str
    history: EventHistory
    atDay: int
