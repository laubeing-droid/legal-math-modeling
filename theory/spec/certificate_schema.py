#!/usr/bin/env python3
"""Specification-side certificate payloads and an independent checker.

v1 payload stays a parseable compatibility layer that can never reach
v2 decisive status. `CertificateEnvelopeV2` binds expected/used facts,
expected/discharged obligations, rules, arguments, attacks, accepted
set, source snapshots, rule pack, semantics, non-empty trace, producer
commit, and checker identity. The checker recomputes every claim
independently; producers never submit trusted booleans.
"""

from __future__ import annotations

import hashlib
import json
from dataclasses import asdict, dataclass
from typing import Any, Dict, Iterable, List, Mapping, Optional, Tuple

from .canonical_semantics import CanonicalProofTrace, DecisionStatus

CERTIFICATE_SCHEMA_V2 = "spec-cert-v2"
CERTIFICATE_CHECKER_NAME = "certificate-envelope-checker"
CERTIFICATE_CHECKER_VERSION = "2.0.0"

KNOWN_SEMANTICS: Mapping[str, frozenset[str]] = {
    "grounded": frozenset({"1"}),
    "horn_least_model": frozenset({"1"}),
    "asp_stable_model": frozenset({"1"}),
    "smt_sat": frozenset({"1"}),
}

ALLOWED_EVIDENCE_KINDS = frozenset(
    {
        "FORMAL_BACKEND",
        "LEAN_PROOF",
        "SOLVER_WITNESS",
        "FINITE_MODEL",
        "HUMAN_REVIEW",
    }
)

TAINT_CODES = frozenset(
    {
        "SOURCE_DIGEST_MISMATCH",
        "RULE_PACK_DIGEST_MISMATCH",
        "STALE_SOURCE_SNAPSHOT",
        "CANDIDATE_EVIDENCE",
        "UNVERIFIED_EVIDENCE",
        "DUPLICATE_ID",
    }
)


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
    attack_kinds: Tuple[str, ...]
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
    attack_kinds: List[str] = []

    for step in trace.steps:
        if step.phase == "input" and step.event == "facts_loaded":
            facts = list(step.payload.get("facts", []))
        elif step.phase == "horn" and step.event == "rule_fired":
            horn_rules.append(step.payload["rule_id"])
        elif step.phase == "aaf" and step.event == "argument_constructed":
            arguments.append(step.payload["argument_id"])
        elif step.phase == "aaf" and step.event == "attack_constructed":
            attacks.append(step.payload["attack_id"])
            attack_kinds.append(step.payload["kind"])
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
        attack_kinds=tuple(attack_kinds),
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
        "attack_kinds",
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

    attack_kinds = set(payload.get("attack_kinds", ()))
    if "PRIORITY_DEFEAT" in attack_kinds and not payload.get("attacks_constructed"):
        errors.append("Priority defeat cannot be declared without attack records.")

    if not payload.get("horn_rules_fired"):
        warnings.append("No Horn rules were fired in this payload.")

    return CheckerVerdict(ok=not errors, errors=tuple(errors), warnings=tuple(warnings))


@dataclass(frozen=True)
class EnvelopeVerdict:
    """Independent v2 verdict; producers never self-report these fields."""

    decisive: bool
    status: str
    error_codes: Tuple[str, ...]
    checks: Tuple[str, ...]


def canonical_content_digest(content: Any) -> str:
    """Content digest over canonical JSON; binds content, not authority."""

    encoded = json.dumps(
        content, sort_keys=True, separators=(",", ":"), ensure_ascii=False
    ).encode("utf-8")
    return hashlib.sha256(encoded).hexdigest()


def build_certificate_envelope_v2(
    *,
    certificate_id: str,
    status: str,
    evidence_kind: str,
    evidence_verified: bool,
    expected_fact_ids: Iterable[str],
    used_fact_ids: Iterable[str],
    expected_obligation_ids: Iterable[str],
    discharged_obligation_ids: Iterable[str],
    rule_ids: Iterable[str],
    arguments: Iterable[Mapping[str, Any]],
    attacks: Iterable[Mapping[str, Any]],
    accepted_argument_ids: Iterable[str],
    source_snapshots: Iterable[Mapping[str, Any]],
    rule_pack_content: Mapping[str, Any],
    semantics_id: str,
    semantics_version: str,
    trace_steps: Iterable[Mapping[str, Any]],
    producer_commit: str,
) -> dict:
    """Assemble a content-bound v2 envelope with recomputable digests."""

    snapshots = []
    for snapshot in source_snapshots:
        content = snapshot["content"]
        snapshots.append(
            {
                "snapshot_id": snapshot["snapshot_id"],
                "content": content,
                "content_digest": canonical_content_digest(content),
            }
        )
    return {
        "schema_version": CERTIFICATE_SCHEMA_V2,
        "certificate_id": certificate_id,
        "status": status,
        "evidence": {"kind": evidence_kind, "verified": evidence_verified},
        "expected_fact_ids": list(expected_fact_ids),
        "used_fact_ids": list(used_fact_ids),
        "expected_obligation_ids": list(expected_obligation_ids),
        "discharged_obligation_ids": list(discharged_obligation_ids),
        "rule_ids": list(rule_ids),
        "arguments": [dict(argument) for argument in arguments],
        "attacks": [dict(attack) for attack in attacks],
        "accepted_argument_ids": list(accepted_argument_ids),
        "source_snapshots": snapshots,
        "rule_pack": {
            "content": dict(rule_pack_content),
            "content_digest": canonical_content_digest(rule_pack_content),
        },
        "semantics": {"id": semantics_id, "version": semantics_version},
        "trace": [dict(step) for step in trace_steps],
        "checker": {
            "name": CERTIFICATE_CHECKER_NAME,
            "version": CERTIFICATE_CHECKER_VERSION,
        },
        "producer": {"commit": producer_commit},
    }


def envelope_to_dict(envelope: Mapping[str, Any]) -> dict:
    """Return a stable deep dict form for JSON serialization."""

    return json.loads(json.dumps(dict(envelope), ensure_ascii=False))


def _check_id_sequences(payload: Mapping[str, Any], errors: List[str]) -> None:
    for key in (
        "expected_fact_ids",
        "used_fact_ids",
        "expected_obligation_ids",
        "discharged_obligation_ids",
        "rule_ids",
        "accepted_argument_ids",
    ):
        sequence = payload.get(key, [])
        if len(sequence) != len(set(sequence)):
            errors.append("DUPLICATE_ID")
        if list(sequence) != sorted(sequence):
            errors.append("UNSTABLE_SEQUENCE")


def check_certificate_envelope(
    payload: Mapping[str, Any],
    *,
    expected_source_digests: Optional[Mapping[str, str]] = None,
) -> EnvelopeVerdict:
    """Independently recompute every v2 claim; never trust producer booleans."""

    errors: List[str] = []
    checks: List[str] = []

    schema_version = payload.get("schema_version")
    if schema_version != CERTIFICATE_SCHEMA_V2:
        if schema_version == "spec-cert-v1":
            errors.append("V1_NOT_DECISIVE")
        else:
            errors.append("UNKNOWN_SCHEMA")
        return EnvelopeVerdict(
            decisive=False,
            status=DecisionStatus.UNDECIDED.value,
            error_codes=tuple(errors),
            checks=tuple(checks),
        )

    status = payload.get("status")
    if status not in {member.value for member in DecisionStatus}:
        errors.append("UNKNOWN_STATUS")

    trace = payload.get("trace", [])
    if not trace:
        errors.append("EMPTY_TRACE")

    required_fields = (
        "certificate_id",
        "evidence",
        "expected_fact_ids",
        "used_fact_ids",
        "expected_obligation_ids",
        "discharged_obligation_ids",
        "rule_ids",
        "arguments",
        "attacks",
        "accepted_argument_ids",
        "source_snapshots",
        "rule_pack",
        "semantics",
        "producer",
    )
    if any(field not in payload for field in required_fields):
        errors.append("MALFORMED_ENVELOPE")

    _check_id_sequences(payload, errors)

    expected_facts = set(payload.get("expected_fact_ids", ()))
    used_facts = set(payload.get("used_fact_ids", ()))
    if not expected_facts.issubset(used_facts):
        errors.append("MISSING_REQUIRED_FACT")

    expected_obligations = set(payload.get("expected_obligation_ids", ()))
    discharged = set(payload.get("discharged_obligation_ids", ()))
    if not expected_obligations.issubset(discharged):
        errors.append("MISSING_PROOF_OBLIGATION")

    argument_ids = {argument.get("argument_id") for argument in payload.get("arguments", ())}
    rule_ids = set(payload.get("rule_ids", ()))
    for argument in payload.get("arguments", ()):
        if argument.get("rule_id") not in rule_ids:
            errors.append("UNKNOWN_ARGUMENT_RULE")
        if not set(argument.get("support_fact_ids", ())).issubset(used_facts):
            errors.append("UNKNOWN_SUPPORT_FACT")
    for accepted in payload.get("accepted_argument_ids", ()):
        if accepted not in argument_ids:
            errors.append("UNKNOWN_ACCEPTED_ARGUMENT")

    for snapshot in payload.get("source_snapshots", ()):
        if "content" not in snapshot:
            errors.append("MISSING_SOURCE_CONTENT")
            continue
        recomputed = canonical_content_digest(snapshot["content"])
        if snapshot.get("content_digest") != recomputed:
            errors.append("SOURCE_DIGEST_MISMATCH")
        if expected_source_digests is not None:
            expected_digest = expected_source_digests.get(snapshot.get("snapshot_id"))
            if expected_digest is not None and expected_digest != recomputed:
                errors.append("STALE_SOURCE_SNAPSHOT")

    rule_pack = payload.get("rule_pack", {})
    if "content" not in rule_pack:
        errors.append("MISSING_RULE_PACK_CONTENT")
    elif rule_pack.get("content_digest") != canonical_content_digest(rule_pack["content"]):
        errors.append("RULE_PACK_DIGEST_MISMATCH")

    semantics = payload.get("semantics", {})
    if semantics.get("version") not in KNOWN_SEMANTICS.get(semantics.get("id"), frozenset()):
        errors.append("UNKNOWN_SEMANTICS")

    checker = payload.get("checker", {})
    if (
        checker.get("name") != CERTIFICATE_CHECKER_NAME
        or checker.get("version") != CERTIFICATE_CHECKER_VERSION
    ):
        errors.append("UNKNOWN_CHECKER_VERSION")

    evidence = payload.get("evidence", {})
    if evidence.get("kind") not in ALLOWED_EVIDENCE_KINDS:
        errors.append("CANDIDATE_EVIDENCE")
    elif evidence.get("verified") is not True:
        errors.append("UNVERIFIED_EVIDENCE")

    producer_commit = payload.get("producer", {}).get("commit", "")
    if not (
        isinstance(producer_commit, str)
        and len(producer_commit) == 40
        and all(ch in "0123456789abcdef" for ch in producer_commit)
    ):
        errors.append("MALFORMED_PRODUCER_COMMIT")

    deduplicated = list(dict.fromkeys(errors))
    if deduplicated:
        tainted = any(code in TAINT_CODES for code in deduplicated)
        return EnvelopeVerdict(
            decisive=False,
            status=DecisionStatus.TAINTED.value if tainted else DecisionStatus.UNDECIDED.value,
            error_codes=tuple(deduplicated),
            checks=tuple(checks),
        )

    checks.append("Envelope content binding recomputed independently by the checker.")
    checks.append("Producer self-reported booleans were not consulted.")
    decisive = status in {DecisionStatus.PROVED.value, DecisionStatus.REFUTED.value}
    return EnvelopeVerdict(
        decisive=decisive,
        status=status,
        error_codes=(),
        checks=tuple(checks),
    )
