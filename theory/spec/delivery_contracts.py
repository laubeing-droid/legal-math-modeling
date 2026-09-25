#!/usr/bin/env python3
"""Delivery, suppression, and workbench contracts (P-105..P-107, P-121,
P-122, P-124..P-132).

Procedural dispositions (P-105) with a validity table. Litigation subject
(P-106) with the recomposition rule. Script assets (P-107): the receipt
only verifies the asset never masquerades as a legal fact. Proposal
admission (P-121): LLM and retrieval outputs enter as candidates through
a gate. Version discipline (P-122) and data-governance disclosure
(P-124). Hallucination blocking (P-125), concept-smuggling defense
(P-126), verbatim citation checking (P-127), technical due-process
mapping (P-128), anonymization boundary (P-129), lifecycle state machine
(P-130), idempotent effect log (P-131), and human gates (P-132).
"""

from __future__ import annotations

from dataclasses import dataclass
from enum import Enum
from typing import Dict, FrozenSet, Optional, Tuple


class ProceduralDisposition(str, Enum):
    """P-105 A58: procedural acts and dispositions."""

    FILE = "FILE"
    ANSWER = "ANSWER"
    CROSS_EXAMINE = "CROSS_EXAMINE"
    DISMISS = "DISMISS"
    SUSPEND = "SUSPEND"
    TERMINATE = "TERMINATE"


_VALID_DISPOSITIONS = {
    (ProceduralDisposition.FILE, ProceduralDisposition.ANSWER),
    (ProceduralDisposition.ANSWER, ProceduralDisposition.CROSS_EXAMINE),
    (ProceduralDisposition.CROSS_EXAMINE, ProceduralDisposition.DISMISS),
    (ProceduralDisposition.CROSS_EXAMINE, ProceduralDisposition.SUSPEND),
    (ProceduralDisposition.SUSPEND, ProceduralDisposition.TERMINATE),
}


def disposition_sequence_valid(order: Tuple[ProceduralDisposition, ...]) -> bool:
    return all(pair in _VALID_DISPOSITIONS for pair in zip(order, order[1:]))


@dataclass(frozen=True)
class LitigationSubject:
    """P-106 A60: the claim subject with a recomposition rule."""

    claim_id: str
    cause_of_action: str
    parties: Tuple[str, str]

    def same_subject_as(self, other: "LitigationSubject") -> bool:
        """Same cause, same parties (order-insensitive), same claim line."""

        return (
            self.cause_of_action == other.cause_of_action
            and set(self.parties) == set(other.parties)
        )


@dataclass(frozen=True)
class ScriptAsset:
    """P-107: talking scripts and tone packs are delivery assets; the only
    verification is that they never masquerade as legal facts."""

    asset_id: str
    contains_legal_fact_assertions: bool

    def receipt_verdict(self) -> str:
        return "REJECTED_MASQUERADE" if self.contains_legal_fact_assertions else "DELIVERY_ASSET_OK"


@dataclass(frozen=True)
class Proposal:
    """P-121 C4: an LLM/retrieval proposal — always a candidate."""

    proposal_id: str
    source: str  # "LLM" | "RETRIEVAL" | ...
    admitted: bool = False

    def grade(self) -> str:
        return "ADMITTED_CANDIDATE" if self.admitted else "CANDIDATE_ONLY"


def admit_proposal(gate_passed: bool, proposal: Proposal) -> Proposal:
    from dataclasses import replace

    if not gate_passed:
        return proposal
    return replace(proposal, admitted=True)


@dataclass(frozen=True)
class VersionDiscipline:
    """P-122 C7: source/model/data versions bound together."""

    source_version: str
    model_version: str
    data_version: str

    def bound(self) -> str:
        return f"{self.source_version}|{self.model_version}|{self.data_version}"


@dataclass(frozen=True)
class DisclosureRecord:
    """P-124 C12: corpus version plus deletion disclosure."""

    corpus_version: str
    deletions_disclosed: bool

    def compliant(self) -> bool:
        return self.deletions_disclosed


@dataclass(frozen=True)
class CitationCheck:
    """P-127 C3: verbatim citation verification against a snapshot."""

    cited_text: str
    snapshot_text: str

    def verbatim_hit(self) -> bool:
        return self.cited_text in self.snapshot_text


class HallucinationPattern(str, Enum):
    """P-125 C1: fabricated-artifact patterns that get blocked."""

    FABRICATED_DOCKET = "FABRICATED_DOCKET"
    FABRICATED_STATUTE = "FABRICATED_STATUTE"
    FABRICATED_FACT = "FABRICATED_FACT"


def block_hallucination(detected: FrozenSet[HallucinationPattern]) -> bool:
    """Any detected fabricated artifact blocks the output."""

    return bool(detected)


@dataclass(frozen=True)
class ConceptUse:
    """P-126 C2: a concept used in an analysis, with its home jurisdiction."""

    concept_id: str
    home_jurisdiction: str
    adapted: bool


def smuggling_blocked(use: ConceptUse, analysis_jurisdiction: str) -> bool:
    """Using a foreign-jurisdiction concept without adaptation is blocked."""

    if use.home_jurisdiction == analysis_jurisdiction:
        return False
    return not use.adapted


class DueProcessElement(str, Enum):
    """P-128 C14: technical due-process elements mapped to checks."""

    NOTICE = "NOTICE"
    OPPORTUNITY_TO_BE_HEARD = "OPPORTUNITY_TO_BE_HEARD"
    REASONS_RECORDED = "REASONS_RECORDED"


DUE_PROCESS_MAP: Dict[DueProcessElement, str] = {
    DueProcessElement.NOTICE: "system_check:notice_delivered",
    DueProcessElement.OPPORTUNITY_TO_BE_HEARD: "system_check:hearing_stage_present",
    DueProcessElement.REASONS_RECORDED: "system_check:reason_log_attached",
}


def due_process_satisfied(present: FrozenSet[DueProcessElement]) -> bool:
    return set(DUE_PROCESS_MAP) <= set(present)


@dataclass(frozen=True)
class AnonymizationBoundary:
    """P-129 C8: anonymization plus re-identification protection."""

    anonymized: bool
    reidentification_tested: bool

    def within_boundary(self) -> bool:
        return self.anonymized and self.reidentification_tested


class LifecycleState(str, Enum):
    """P-130 C9: case lifecycle state machine."""

    INTAKE = "INTAKE"
    ACTIVE = "ACTIVE"
    SUSPENDED = "SUSPENDED"
    CLOSED = "CLOSED"
    ARCHIVED = "ARCHIVED"


_LIFECYCLE_EDGES = {
    (LifecycleState.INTAKE, LifecycleState.ACTIVE),
    (LifecycleState.ACTIVE, LifecycleState.SUSPENDED),
    (LifecycleState.SUSPENDED, LifecycleState.ACTIVE),
    (LifecycleState.ACTIVE, LifecycleState.CLOSED),
    (LifecycleState.CLOSED, LifecycleState.ARCHIVED),
}


def lifecycle_transition_valid(current: LifecycleState, target: LifecycleState) -> bool:
    return (current, target) in _LIFECYCLE_EDGES


def effect_log_apply(
    log: Dict[str, str], command_id: str, effect: str
) -> Dict[str, str]:
    """P-131 C10: idempotent effect log — the same command twice applies once."""

    if command_id in log:
        return log
    return {**log, command_id: effect}


class HumanGate(str, Enum):
    """P-132 C11: human-in-the-loop gates."""

    LAWYER_APPROVAL = "LAWYER_APPROVAL"
    SIGNATURE = "SIGNATURE"
    FINAL_REVIEW = "FINAL_REVIEW"


def action_requires_gate(action: str, gate: HumanGate) -> bool:
    """The gated-action table: listed actions never bypass their gate."""

    table = {
        "FILE_DOCUMENT": HumanGate.SIGNATURE,
        "ISSUE_OPINION": HumanGate.LAWYER_APPROVAL,
        "SUBMIT_OUTPUT": HumanGate.FINAL_REVIEW,
    }
    return table.get(action) is gate
