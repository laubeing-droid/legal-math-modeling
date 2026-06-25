#!/usr/bin/env python3
"""Specification-side certificate payloads and an independent checker."""

from __future__ import annotations

from dataclasses import asdict, dataclass
from typing import Any, Dict, Iterable, List, Mapping, Tuple

from .canonical_semantics import CanonicalProofTrace, DecisionStatus


@dataclass(frozen=True)
class CertificatePayload:
    """Portable payload emitted by the reference evaluator."""

    schema_version: str
    trace_id: str
    status: str
    facts: Tuple[str, ...]
    horn_rules_fired: Tuple[str, ...]
    arguments_constructed: Tuple[str, ...]
    attacks_constructed: Tuple[str, ...]
    accepted_argument_ids: Tuple[str, ...]
    fail_closed_reason: str | None


@dataclass(frozen=True)
class CheckerVerdict:
    """Independent verdict over a certificate payload."""

    ok: bool
    errors: Tuple[str, ...]
    warnings: Tuple[str, ...]


def build_certificate_payload(trace: CanonicalProofTrace) -> CertificatePayload:
    """Project a proof trace into a transport-friendly certificate payload."""

    facts: List[str] = []
    horn_rules: List[str] = []
    arguments: List[str] = []
    attacks: List[str] = []
    accepted_ids: List[str] = []

    for step in trace.steps:
        if step.phase == "input" and step.event == "facts_loaded":
            facts = list(step.payload.get("facts", []))
        elif step.phase == "horn" and step.event == "rule_fired":
            horn_rules.append(step.payload["rule_id"])
        elif step.phase == "aaf" and step.event == "argument_constructed":
            arguments.append(step.payload["argument_id"])
        elif step.phase == "aaf" and step.event == "attack_constructed":
            attacks.append(step.payload["attack_id"])
        elif step.phase == "output" and step.event == "decision_status":
            accepted_ids = list(step.payload.get("accepted_argument_ids", []))

    return CertificatePayload(
        schema_version="spec-cert-v1",
        trace_id=trace.trace_id,
        status=trace.status.value,
        facts=tuple(facts),
        horn_rules_fired=tuple(horn_rules),
        arguments_constructed=tuple(arguments),
        attacks_constructed=tuple(attacks),
        accepted_argument_ids=tuple(accepted_ids),
        fail_closed_reason=trace.fail_closed_reason,
    )


def payload_to_dict(payload: CertificatePayload) -> Dict[str, Any]:
    """Expose a stable dict form for downstream JSON serialization."""

    return asdict(payload)


def check_certificate_payload(payload: Mapping[str, Any]) -> CheckerVerdict:
    """Validate the minimum transport and fail-closed constraints."""

    errors: List[str] = []
    warnings: List[str] = []
    required = (
        "schema_version",
        "trace_id",
        "status",
        "facts",
        "horn_rules_fired",
        "arguments_constructed",
        "attacks_constructed",
        "accepted_argument_ids",
        "fail_closed_reason",
    )
    for key in required:
        if key not in payload:
            errors.append(f"Missing required field: {key}")

    status = payload.get("status")
    if status not in {member.value for member in DecisionStatus}:
        errors.append(f"Unknown status value: {status}")

    if status == DecisionStatus.TAINTED.value and not payload.get("fail_closed_reason"):
        errors.append("TAINTED payloads must provide fail_closed_reason.")

    if status in {DecisionStatus.PROVED.value, DecisionStatus.REFUTED.value}:
        if not payload.get("arguments_constructed"):
            errors.append("Decisive payloads must carry constructed arguments.")

    if payload.get("accepted_argument_ids"):
        accepted = set(payload["accepted_argument_ids"])
        arguments = set(payload.get("arguments_constructed", ()))
        if not accepted.issubset(arguments):
            errors.append("Accepted argument ids are not bounded by constructed arguments.")

    if not payload.get("horn_rules_fired"):
        warnings.append("No Horn rules were fired in this payload.")

    return CheckerVerdict(ok=not errors, errors=tuple(errors), warnings=tuple(warnings))
