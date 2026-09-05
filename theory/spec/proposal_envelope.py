#!/usr/bin/env python3
"""P01/P05 proposal envelope reference semantics.

LLM/Agent proposals stay at UNTRUSTED_PROPOSAL; they cannot issue fact
attestations, certificates, or decision statuses. Consensus, confidence,
model identity, and repeated runs never escalate authority. False
accept/false reject records are kept as model-behavior counterexamples;
they never enter theorem premises or formal inputs.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Any, Iterable, List, Mapping, Tuple

from .receipt_authority import AUTHORITY_ORDER, can_issue

PROPOSAL_ORIGINS = frozenset({"LLM", "AGENT", "HUMAN_DRAFT"})

ENFORCED_LEVEL = {
    "LLM": "UNTRUSTED_PROPOSAL",
    "AGENT": "UNTRUSTED_PROPOSAL",
    "HUMAN_DRAFT": "SOURCE_BOUND_CANDIDATE",
}


@dataclass(frozen=True)
class ProposalReport:
    accepted_as_formal_input: bool
    allowed_artifacts: Tuple[str, ...]
    error_codes: Tuple[str, ...]


def check_proposal_envelope(proposal: Mapping[str, Any]) -> ProposalReport:
    """Verify a proposal envelope; proposals never become formal inputs."""

    errors: List[str] = []
    origin = proposal.get("origin")
    if origin not in PROPOSAL_ORIGINS:
        errors.append("UNKNOWN_PROPOSAL_ORIGIN")

    if proposal.get("self_approved") is True:
        errors.append("SELF_APPROVAL_NOT_ESCALATION")
    if proposal.get("prompt_injected") is True:
        errors.append("PROMPT_INJECTION_QUARANTINED")
    if proposal.get("claimed_level") not in (None, "UNTRUSTED_PROPOSAL"):
        if origin in ("LLM", "AGENT"):
            errors.append("PROPOSAL_LEVEL_INFLATION")

    allowed = tuple(
        artifact
        for artifact in ("PROPOSAL", "SOURCE_BINDING", "FACT_ATTESTATION", "CERTIFICATE", "DECISION_STATUS")
        if origin is not None and can_issue(ENFORCED_LEVEL.get(origin, "UNTRUSTED_PROPOSAL"), artifact)
    )

    deduplicated = list(dict.fromkeys(errors))
    return ProposalReport(
        accepted_as_formal_input=False,
        allowed_artifacts=allowed,
        error_codes=tuple(deduplicated),
    )


def consensus_authority(proposals: Iterable[Mapping[str, Any]]) -> str:
    """Consensus over proposals never escalates beyond the max proposal level."""

    levels = []
    for proposal in proposals:
        origin = proposal.get("origin")
        levels.append(ENFORCED_LEVEL.get(origin, "UNTRUSTED_PROPOSAL"))
    if not levels:
        return "UNTRUSTED_PROPOSAL"
    return AUTHORITY_ORDER[max(AUTHORITY_ORDER.index(level) for level in levels)]


def record_behavior_counterexample(
    registry: List[dict], *, case_id: str, kind: str, detail: str
) -> List[dict]:
    """Append a false-accept/false-reject counterexample (never a premise)."""

    if kind not in ("FALSE_ACCEPT", "FALSE_REJECT"):
        raise ValueError(f"Unknown counterexample kind: {kind}")
    registry.append({"case_id": case_id, "kind": kind, "detail": detail})
    return registry
