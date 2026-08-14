#!/usr/bin/env python3
"""Specification-side certificate payloads and an independent checker."""

from __future__ import annotations

from dataclasses import asdict, dataclass
import hashlib
import json
import re
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
    attack_kinds: Tuple[str, ...]
    fail_closed_reason: str | None


@dataclass(frozen=True)
class CheckerVerdict:
    """Independent verdict over a certificate payload."""

    ok: bool
    errors: Tuple[str, ...]
    warnings: Tuple[str, ...]


@dataclass(frozen=True)
class CertificateEnvelopeV2:
    """Content-bound v2 transport envelope."""

    schema_version: str
    certificate_id: str
    status: str
    evidence: Dict[str, Any]
    expected_fact_ids: Tuple[str, ...]
    used_fact_ids: Tuple[str, ...]
    expected_obligation_ids: Tuple[str, ...]
    discharged_obligation_ids: Tuple[str, ...]
    rule_ids: Tuple[str, ...]
    arguments: Tuple[Dict[str, Any], ...]
    attacks: Tuple[Dict[str, Any], ...]
    accepted_argument_ids: Tuple[str, ...]
    source_snapshots: Tuple[Dict[str, Any], ...]
    rule_pack: Dict[str, Any]
    semantics: Dict[str, str]
    trace: Tuple[Dict[str, Any], ...]
    trace_digest: str
    producer_commit: str
    checker: Dict[str, str]
    certificate_digest: str


@dataclass(frozen=True)
class EnvelopeVerdict:
    """Fail-closed v2 verdict with stable machine error codes."""

    decisive: bool
    status: str
    error_codes: Tuple[str, ...]


CHECKER_ID = "lmm-independent-checker"
CHECKER_VERSION = "2"
KNOWN_SEMANTICS = {("grounded", "1")}
KNOWN_DECISIVE_STATUSES = {DecisionStatus.PROVED.value, DecisionStatus.REFUTED.value}
DIGEST_PATTERN = re.compile(r"^[0-9a-f]{64}$")
COMMIT_PATTERN = re.compile(r"^[0-9a-f]{40}$")


def canonical_sha256(value: Any) -> str:
    """Hash the canonical UTF-8 JSON representation of a value."""

    serialized = json.dumps(
        value,
        ensure_ascii=False,
        sort_keys=True,
        separators=(",", ":"),
    ).encode("utf-8")
    return hashlib.sha256(serialized).hexdigest()


def _sorted_dicts(
    records: Iterable[Mapping[str, Any]], key: str
) -> Tuple[Dict[str, Any], ...]:
    normalized = [dict(record) for record in records]
    return tuple(sorted(normalized, key=lambda record: str(record.get(key, ""))))


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
) -> CertificateEnvelopeV2:
    """Build a deterministic v2 envelope; the checker remains a separate operation."""

    normalized_snapshots: list[dict[str, Any]] = []
    for snapshot in source_snapshots:
        content = snapshot.get("content")
        normalized_snapshots.append(
            {
                "snapshot_id": str(snapshot.get("snapshot_id", "")),
                "content": content,
                "content_digest": canonical_sha256(content),
            }
        )
    trace = tuple(dict(step) for step in trace_steps)
    payload: dict[str, Any] = {
        "schema_version": "spec-cert-v2",
        "certificate_id": certificate_id,
        "status": status,
        "evidence": {"kind": evidence_kind, "verified": evidence_verified},
        "expected_fact_ids": tuple(sorted(expected_fact_ids)),
        "used_fact_ids": tuple(sorted(used_fact_ids)),
        "expected_obligation_ids": tuple(sorted(expected_obligation_ids)),
        "discharged_obligation_ids": tuple(sorted(discharged_obligation_ids)),
        "rule_ids": tuple(sorted(rule_ids)),
        "arguments": _sorted_dicts(arguments, "argument_id"),
        "attacks": _sorted_dicts(attacks, "attack_id"),
        "accepted_argument_ids": tuple(sorted(accepted_argument_ids)),
        "source_snapshots": _sorted_dicts(normalized_snapshots, "snapshot_id"),
        "rule_pack": {
            "content": dict(rule_pack_content),
            "content_digest": canonical_sha256(rule_pack_content),
        },
        "semantics": {"id": semantics_id, "version": semantics_version},
        "trace": trace,
        "trace_digest": canonical_sha256(trace),
        "producer_commit": producer_commit,
        "checker": {"id": CHECKER_ID, "version": CHECKER_VERSION},
    }
    payload["certificate_digest"] = canonical_sha256(payload)
    return CertificateEnvelopeV2(**payload)


def envelope_to_dict(envelope: CertificateEnvelopeV2) -> Dict[str, Any]:
    """Return a mutation-friendly JSON object for transport or testing."""

    return json.loads(json.dumps(asdict(envelope), ensure_ascii=False))


def _duplicates(values: Iterable[Any]) -> bool:
    normalized = [str(value) for value in values]
    return len(normalized) != len(set(normalized))


def _is_sorted(values: Iterable[Any]) -> bool:
    normalized = [str(value) for value in values]
    return normalized == sorted(normalized)


def _mapping_records(payload: Mapping[str, Any], key: str) -> list[Mapping[str, Any]]:
    value = payload.get(key, [])
    if not isinstance(value, list):
        return []
    return [record for record in value if isinstance(record, Mapping)]


def check_certificate_envelope(
    payload: Mapping[str, Any],
    *,
    expected_source_digests: Mapping[str, str] | None = None,
) -> EnvelopeVerdict:
    """Recompute v2 acceptance from content; producer booleans are not consulted."""

    schema_version = payload.get("schema_version")
    if schema_version == "spec-cert-v1":
        return EnvelopeVerdict(False, DecisionStatus.TAINTED.value, ("V1_NOT_DECISIVE",))
    if schema_version != "spec-cert-v2":
        return EnvelopeVerdict(False, DecisionStatus.TAINTED.value, ("UNKNOWN_SCHEMA_VERSION",))

    errors: set[str] = set()
    digest_payload = dict(payload)
    certificate_digest = digest_payload.pop("certificate_digest", None)
    if certificate_digest != canonical_sha256(digest_payload):
        errors.add("CERTIFICATE_DIGEST_MISMATCH")

    identifier_fields = (
        "expected_fact_ids",
        "used_fact_ids",
        "expected_obligation_ids",
        "discharged_obligation_ids",
        "rule_ids",
        "accepted_argument_ids",
    )
    for field in identifier_fields:
        values = payload.get(field, [])
        if not isinstance(values, list):
            errors.add("MALFORMED_SEQUENCE")
            continue
        if _duplicates(values):
            errors.add("DUPLICATE_ID")
        if not _is_sorted(values):
            errors.add("UNSTABLE_SEQUENCE")

    expected_facts = set(payload.get("expected_fact_ids", []))
    used_facts = set(payload.get("used_fact_ids", []))
    if not expected_facts.issubset(used_facts):
        errors.add("MISSING_REQUIRED_FACT")
    expected_obligations = set(payload.get("expected_obligation_ids", []))
    discharged_obligations = set(payload.get("discharged_obligation_ids", []))
    if not expected_obligations.issubset(discharged_obligations):
        errors.add("MISSING_PROOF_OBLIGATION")

    arguments = _mapping_records(payload, "arguments")
    argument_ids = [str(argument.get("argument_id", "")) for argument in arguments]
    if len(arguments) != len(payload.get("arguments", [])):
        errors.add("MALFORMED_ARGUMENT")
    if _duplicates(argument_ids):
        errors.add("DUPLICATE_ID")
    if not _is_sorted(argument_ids):
        errors.add("UNSTABLE_SEQUENCE")
    for argument in arguments:
        support_ids = argument.get("support_fact_ids", [])
        if not isinstance(support_ids, list):
            errors.add("MALFORMED_ARGUMENT")
        elif _duplicates(support_ids):
            errors.add("DUPLICATE_ID")
        elif not _is_sorted(support_ids):
            errors.add("UNSTABLE_SEQUENCE")
        if argument.get("rule_id") not in set(payload.get("rule_ids", [])):
            errors.add("UNKNOWN_ARGUMENT_RULE")
        if not set(support_ids).issubset(used_facts):
            errors.add("UNKNOWN_ARGUMENT_SUPPORT")
    if not set(payload.get("accepted_argument_ids", [])).issubset(set(argument_ids)):
        errors.add("UNKNOWN_ACCEPTED_ARGUMENT")

    attacks = _mapping_records(payload, "attacks")
    attack_ids = [str(attack.get("attack_id", "")) for attack in attacks]
    if len(attacks) != len(payload.get("attacks", [])):
        errors.add("MALFORMED_ATTACK")
    if _duplicates(attack_ids):
        errors.add("DUPLICATE_ID")
    if not _is_sorted(attack_ids):
        errors.add("UNSTABLE_SEQUENCE")
    for attack in attacks:
        if attack.get("attacker_id") not in argument_ids or attack.get("target_id") not in argument_ids:
            errors.add("UNKNOWN_ATTACK_ARGUMENT")
        if attack.get("kind") not in {"REBUTTAL", "EXCEPTION", "PRIORITY_DEFEAT"}:
            errors.add("UNKNOWN_ATTACK_KIND")

    snapshots = _mapping_records(payload, "source_snapshots")
    snapshot_ids = [str(snapshot.get("snapshot_id", "")) for snapshot in snapshots]
    if len(snapshots) != len(payload.get("source_snapshots", [])):
        errors.add("MALFORMED_SOURCE_SNAPSHOT")
    if _duplicates(snapshot_ids):
        errors.add("DUPLICATE_ID")
    if not _is_sorted(snapshot_ids):
        errors.add("UNSTABLE_SEQUENCE")
    for snapshot in snapshots:
        snapshot_id = str(snapshot.get("snapshot_id", ""))
        digest = snapshot.get("content_digest")
        if digest != canonical_sha256(snapshot.get("content")):
            errors.add("SOURCE_DIGEST_MISMATCH")
        if expected_source_digests is not None:
            if expected_source_digests.get(snapshot_id) != digest:
                errors.add("STALE_SOURCE_SNAPSHOT")

    rule_pack = payload.get("rule_pack", {})
    if not isinstance(rule_pack, Mapping):
        errors.add("MALFORMED_RULE_PACK")
    elif rule_pack.get("content_digest") != canonical_sha256(rule_pack.get("content")):
        errors.add("RULE_PACK_DIGEST_MISMATCH")

    trace = payload.get("trace", [])
    if not isinstance(trace, list) or not trace:
        errors.add("EMPTY_TRACE")
    else:
        indexes = [step.get("step_index") for step in trace if isinstance(step, Mapping)]
        if indexes != list(range(len(trace))):
            errors.add("UNSTABLE_TRACE")
    if payload.get("trace_digest") != canonical_sha256(trace):
        errors.add("TRACE_DIGEST_MISMATCH")

    semantics = payload.get("semantics", {})
    if not isinstance(semantics, Mapping) or (
        semantics.get("id"), semantics.get("version")
    ) not in KNOWN_SEMANTICS:
        errors.add("UNKNOWN_SEMANTICS")
    checker = payload.get("checker", {})
    if not isinstance(checker, Mapping) or checker.get("id") != CHECKER_ID:
        errors.add("UNKNOWN_CHECKER_ID")
    if not isinstance(checker, Mapping) or checker.get("version") != CHECKER_VERSION:
        errors.add("UNKNOWN_CHECKER_VERSION")

    evidence = payload.get("evidence", {})
    if not isinstance(evidence, Mapping):
        errors.add("MALFORMED_EVIDENCE")
    elif evidence.get("kind") == "CANDIDATE":
        errors.add("CANDIDATE_EVIDENCE")
    elif evidence.get("verified") is not True:
        errors.add("UNVERIFIED_EVIDENCE")

    producer_commit = payload.get("producer_commit")
    if not isinstance(producer_commit, str) or not COMMIT_PATTERN.fullmatch(producer_commit):
        errors.add("INVALID_PRODUCER_COMMIT")
    if payload.get("status") not in KNOWN_DECISIVE_STATUSES:
        errors.add("UNKNOWN_OR_NONDECISIVE_STATUS")

    decisive = not errors
    status = (
        str(payload["status"])
        if decisive
        else (
            DecisionStatus.TAINTED.value
            if any("DIGEST" in error or "CANDIDATE" in error for error in errors)
            else DecisionStatus.UNDECIDED.value
        )
    )
    return EnvelopeVerdict(decisive, status, tuple(sorted(errors)))


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
