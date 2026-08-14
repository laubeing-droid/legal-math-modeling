#!/usr/bin/env python3
"""Independent, task-bounded Horn-to-AAF translation witness checks."""

from __future__ import annotations

from dataclasses import asdict, dataclass
import hashlib
import json
from typing import Any, Iterable, Mapping, Tuple


KNOWN_ATTACK_KINDS = {"REBUTTAL", "EXCEPTION", "PRIORITY_DEFEAT"}
KNOWN_SEMANTICS = {("grounded", "1")}
KNOWN_CYCLE_POLICIES = {"reject", "explicit-undecided"}


def _canonical_sha256(value: Any) -> str:
    content = json.dumps(
        value,
        ensure_ascii=False,
        sort_keys=True,
        separators=(",", ":"),
    ).encode("utf-8")
    return hashlib.sha256(content).hexdigest()


def _sorted_records(
    records: Iterable[Mapping[str, Any]], identifier: str
) -> Tuple[dict[str, Any], ...]:
    normalized = [dict(record) for record in records]
    return tuple(sorted(normalized, key=lambda record: str(record.get(identifier, ""))))


@dataclass(frozen=True)
class TranslationWitness:
    schema_version: str
    input_content: dict[str, Any]
    input_digest: str
    expected_arguments: Tuple[dict[str, Any], ...]
    expected_attacks: Tuple[dict[str, Any], ...]
    output_arguments: Tuple[dict[str, Any], ...]
    output_attacks: Tuple[dict[str, Any], ...]
    semantics: dict[str, str]
    cycle_policy: str
    rejected_inputs: Tuple[dict[str, str], ...]
    witness_digest: str


@dataclass(frozen=True)
class TranslationWitnessReport:
    satisfied: bool
    error_codes: Tuple[str, ...]


def build_translation_witness(
    *,
    input_content: Mapping[str, Any],
    expected_arguments: Iterable[Mapping[str, Any]],
    expected_attacks: Iterable[Mapping[str, Any]],
    output_arguments: Iterable[Mapping[str, Any]],
    output_attacks: Iterable[Mapping[str, Any]],
    semantics_id: str,
    semantics_version: str,
    cycle_policy: str = "reject",
    rejected_inputs: Iterable[Mapping[str, str]] = (),
) -> TranslationWitness:
    """Build a deterministic witness without deciding whether it is valid."""

    payload: dict[str, Any] = {
        "schema_version": "horn-aaf-translation-witness-v1",
        "input_content": dict(input_content),
        "input_digest": _canonical_sha256(input_content),
        "expected_arguments": _sorted_records(expected_arguments, "argument_id"),
        "expected_attacks": _sorted_records(expected_attacks, "attack_id"),
        "output_arguments": _sorted_records(output_arguments, "argument_id"),
        "output_attacks": _sorted_records(output_attacks, "attack_id"),
        "semantics": {"id": semantics_id, "version": semantics_version},
        "cycle_policy": cycle_policy,
        "rejected_inputs": _sorted_records(rejected_inputs, "input_id"),
    }
    payload["witness_digest"] = _canonical_sha256(payload)
    return TranslationWitness(**payload)


def translation_witness_to_dict(witness: TranslationWitness) -> dict[str, Any]:
    return json.loads(json.dumps(asdict(witness), ensure_ascii=False))


def _records(payload: Mapping[str, Any], field: str) -> list[Mapping[str, Any]]:
    value = payload.get(field, [])
    if not isinstance(value, list):
        return []
    return [record for record in value if isinstance(record, Mapping)]


def _id_map(
    records: Iterable[Mapping[str, Any]], identifier: str
) -> tuple[dict[str, Mapping[str, Any]], bool]:
    result: dict[str, Mapping[str, Any]] = {}
    duplicate = False
    for record in records:
        record_id = str(record.get(identifier, ""))
        if not record_id or record_id in result:
            duplicate = True
        result[record_id] = record
    return result, duplicate


def check_translation_witness(
    payload: Mapping[str, Any],
) -> TranslationWitnessReport:
    """Reject omissions, unwitnessed output, and directed-edge mutations."""

    errors: set[str] = set()
    if payload.get("schema_version") != "horn-aaf-translation-witness-v1":
        errors.add("UNKNOWN_WITNESS_SCHEMA")

    digest_payload = dict(payload)
    claimed_digest = digest_payload.pop("witness_digest", None)
    if claimed_digest != _canonical_sha256(digest_payload):
        errors.add("WITNESS_DIGEST_MISMATCH")
    if payload.get("input_digest") != _canonical_sha256(payload.get("input_content")):
        errors.add("INPUT_DIGEST_MISMATCH")

    semantics = payload.get("semantics", {})
    if not isinstance(semantics, Mapping) or (
        semantics.get("id"), semantics.get("version")
    ) not in KNOWN_SEMANTICS:
        errors.add("UNKNOWN_SEMANTICS")
    if payload.get("cycle_policy") not in KNOWN_CYCLE_POLICIES:
        errors.add("MISSING_CYCLE_POLICY")

    expected_arguments = _records(payload, "expected_arguments")
    output_arguments = _records(payload, "output_arguments")
    expected_by_id, duplicate_expected_argument = _id_map(
        expected_arguments, "argument_id"
    )
    output_by_id, duplicate_output_argument = _id_map(output_arguments, "argument_id")
    if duplicate_expected_argument or duplicate_output_argument:
        errors.add("DUPLICATE_ID")
    missing_arguments = set(expected_by_id) - set(output_by_id)
    extra_arguments = set(output_by_id) - set(expected_by_id)
    if missing_arguments:
        errors.add("EXPECTED_ARGUMENT_OMITTED")
    if extra_arguments:
        errors.add("SPURIOUS_ARGUMENT")
    for argument_id in set(expected_by_id).intersection(output_by_id):
        if expected_by_id[argument_id] != output_by_id[argument_id]:
            errors.add("ARGUMENT_WITNESS_MISMATCH")

    input_content = payload.get("input_content", {})
    if not isinstance(input_content, Mapping):
        errors.add("MALFORMED_INPUT_CONTENT")
        input_content = {}
    fact_ids = {str(value) for value in input_content.get("facts", [])}
    rule_ids = {str(value) for value in input_content.get("rules", [])}
    for argument in output_arguments:
        if argument.get("rule_id") not in rule_ids:
            errors.add("ARGUMENT_WITHOUT_INPUT_DERIVATION")
        support_ids = argument.get("support_fact_ids", [])
        if not isinstance(support_ids, list) or not set(support_ids).issubset(fact_ids):
            errors.add("ARGUMENT_WITHOUT_INPUT_DERIVATION")

    expected_attacks = _records(payload, "expected_attacks")
    output_attacks = _records(payload, "output_attacks")
    expected_edges, duplicate_expected_edge = _id_map(expected_attacks, "attack_id")
    output_edges, duplicate_output_edge = _id_map(output_attacks, "attack_id")
    if duplicate_expected_edge or duplicate_output_edge:
        errors.add("DUPLICATE_ID")
    if set(expected_edges) - set(output_edges):
        errors.add("EXPECTED_EDGE_OMITTED")
    if set(output_edges) - set(expected_edges):
        errors.add("SPURIOUS_EDGE")

    for attack_id in set(expected_edges).intersection(output_edges):
        expected = expected_edges[attack_id]
        actual = output_edges[attack_id]
        reversed_priority = (
            expected.get("kind") == "PRIORITY_DEFEAT"
            and actual.get("attacker_id") == expected.get("target_id")
            and actual.get("target_id") == expected.get("attacker_id")
        )
        if reversed_priority:
            errors.add("PRIORITY_DIRECTION_REVERSED")
        elif expected != actual:
            errors.add("EDGE_WITNESS_MISMATCH")

    witness_ids = rule_ids.union(
        str(value) for value in input_content.get("exceptions", [])
    )
    for attack in output_attacks:
        if attack.get("kind") not in KNOWN_ATTACK_KINDS:
            errors.add("UNKNOWN_EDGE_KIND")
        if attack.get("attacker_id") not in output_by_id or attack.get("target_id") not in output_by_id:
            errors.add("EDGE_WITH_UNKNOWN_ARGUMENT")
        if attack.get("input_witness") not in witness_ids:
            errors.add("EDGE_WITHOUT_INPUT_WITNESS")

    return TranslationWitnessReport(not errors, tuple(sorted(errors)))
