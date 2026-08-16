#!/usr/bin/env python3
"""Translation witness contract for dual-IR and backend lowerings.

This module fixes the independent checker contract for translation
witnesses between `LegalSpec`, `Legal-IVL`, and backend targets
(Horn / AAF / ASP / SMT). The checker verifies, per hop:

* expected arguments/attacks are not omitted (no missing edge);
* no spurious argument/attack without an input witness is produced;
* priority-defeat direction follows the recorded priority pair;
* semantics identity is known and version-bound.

The checker never calls any compiler implementation: it only consumes
the declared witness payload. UNKNOWN / malformed payloads are
fail-closed.
"""

from __future__ import annotations

import hashlib
import json
from copy import deepcopy
from dataclasses import dataclass
from typing import Any, Mapping, Sequence, Tuple

SCHEMA_VERSION = "spec-translation-witness-v2"

KNOWN_SEMANTICS: Mapping[str, frozenset[str]] = {
    "grounded": frozenset({"1"}),
    "horn_least_model": frozenset({"1"}),
    "asp_stable_model": frozenset({"1"}),
    "smt_sat": frozenset({"1"}),
}

ATTACK_KINDS = frozenset(
    {
        "REBUTTAL",
        "EXCEPTION",
        "PRIORITY_DEFEAT",
        "UNDERCUT",
        "PREMISE_CHALLENGE",
    }
)


@dataclass(frozen=True)
class TranslationWitnessReport:
    """Independent verdict over a translation witness payload."""

    satisfied: bool
    error_codes: Tuple[str, ...]
    checks: Tuple[str, ...]


def _canonical_digest(payload: Any) -> str:
    encoded = json.dumps(
        payload, sort_keys=True, separators=(",", ":"), ensure_ascii=False
    ).encode("utf-8")
    return hashlib.sha256(encoded).hexdigest()


def build_translation_witness(
    *,
    input_content: Mapping[str, Any],
    expected_arguments: Sequence[Mapping[str, Any]],
    expected_attacks: Sequence[Mapping[str, Any]],
    output_arguments: Sequence[Mapping[str, Any]],
    output_attacks: Sequence[Mapping[str, Any]],
    semantics_id: str,
    semantics_version: str,
) -> dict:
    """Assemble one hop of translation witness with content digests."""

    normalized_input = {
        "facts": tuple(input_content.get("facts", ())),
        "rules": tuple(input_content.get("rules", ())),
        "exceptions": tuple(input_content.get("exceptions", ())),
        "priorities": tuple(
            {"winner": p["winner"], "loser": p["loser"]}
            for p in input_content.get("priorities", ())
        ),
    }
    return {
        "schema_version": SCHEMA_VERSION,
        "input": deepcopy(dict(normalized_input)),
        "input_digest": _canonical_digest(normalized_input),
        "expected_arguments": deepcopy([dict(a) for a in expected_arguments]),
        "expected_attacks": deepcopy([dict(a) for a in expected_attacks]),
        "output_arguments": deepcopy([dict(a) for a in output_arguments]),
        "output_attacks": deepcopy([dict(a) for a in output_attacks]),
        "semantics": {"id": semantics_id, "version": semantics_version},
    }


def translation_witness_to_dict(witness: Mapping[str, Any]) -> dict:
    """Return a stable deep-copied dict form for JSON serialization."""

    return deepcopy(dict(witness))


def _input_witness_tokens(input_section: Mapping[str, Any]) -> frozenset[str]:
    return frozenset(
        input_section.get("facts", ())
    ) | frozenset(
        input_section.get("rules", ())
    ) | frozenset(
        input_section.get("exceptions", ())
    )


def _argument_rule_map(arguments: Sequence[Mapping[str, Any]]) -> dict:
    return {a["argument_id"]: a["rule_id"] for a in arguments}


def check_translation_witness(payload: Mapping[str, Any]) -> TranslationWitnessReport:
    """Independently verify one translation hop against its input witness."""

    errors: list[str] = []
    checks: list[str] = []

    if payload.get("schema_version") != SCHEMA_VERSION:
        errors.append("UNKNOWN_SCHEMA")

    semantics = payload.get("semantics", {})
    if semantics.get("version") not in KNOWN_SEMANTICS.get(semantics.get("id"), frozenset()):
        errors.append("UNKNOWN_SEMANTICS")

    input_section = payload.get("input", {})
    if not isinstance(input_section, Mapping):
        errors.append("MALFORMED_INPUT")
        input_section = {}
    tokens = _input_witness_tokens(input_section)
    priorities = tuple(input_section.get("priorities", ()))
    for priority in priorities:
        if not {"winner", "loser"} <= set(priority):
            errors.append("MALFORMED_INPUT")

    expected_arguments = tuple(payload.get("expected_arguments", ()))
    expected_attacks = tuple(payload.get("expected_attacks", ()))
    output_arguments = tuple(payload.get("output_arguments", ()))
    output_attacks = tuple(payload.get("output_attacks", ()))

    for collection, label in (
        (expected_arguments, "expected_arguments"),
        (expected_attacks, "expected_attacks"),
        (output_arguments, "output_arguments"),
        (output_attacks, "output_attacks"),
    ):
        id_key = "argument_id" if "argument" in label else "attack_id"
        ids = [entry.get(id_key) for entry in collection]
        if len(ids) != len(set(ids)):
            errors.append("DUPLICATE_ID")

    input_facts = frozenset(input_section.get("facts", ()))
    input_rules = frozenset(input_section.get("rules", ()))
    input_exceptions = frozenset(input_section.get("exceptions", ()))

    for argument in expected_arguments:
        if argument.get("rule_id") not in input_rules:
            errors.append("EXPECTED_ARGUMENT_UNWITNESSED")
        if not set(argument.get("support_fact_ids", ())).issubset(input_facts):
            errors.append("EXPECTED_ARGUMENT_UNWITNESSED")
    if not errors:
        checks.append("Expected arguments are fully witnessed by the input.")

    for attack in expected_attacks:
        kind = attack.get("kind")
        witness = attack.get("input_witness")
        if kind not in ATTACK_KINDS:
            errors.append("UNKNOWN_ATTACK_KIND")
        if witness not in tokens:
            errors.append("EXPECTED_EDGE_UNWITNESSED")
        elif kind == "EXCEPTION" and witness not in input_exceptions:
            errors.append("EXPECTED_EDGE_UNWITNESSED")

    expected_argument_ids = {a.get("argument_id") for a in expected_arguments}
    output_argument_by_id = {a.get("argument_id"): a for a in output_arguments}
    for argument in expected_arguments:
        produced = output_argument_by_id.get(argument.get("argument_id"))
        if produced is None:
            errors.append("EXPECTED_ARGUMENT_OMITTED")
        elif dict(produced) != dict(argument):
            errors.append("ARGUMENT_CONTENT_MISMATCH")
    for argument in output_arguments:
        if argument.get("argument_id") not in expected_argument_ids:
            errors.append("SPURIOUS_ARGUMENT")

    expected_attack_by_id = {a.get("attack_id"): a for a in expected_attacks}
    output_attack_by_id = {a.get("attack_id"): a for a in output_attacks}

    for expected in expected_attacks:
        attack_id = expected.get("attack_id")
        produced = output_attack_by_id.get(attack_id)
        if produced is None:
            errors.append("EXPECTED_EDGE_OMITTED")
            continue
        if (produced.get("attacker_id"), produced.get("target_id")) == (
            expected.get("target_id"),
            expected.get("attacker_id"),
        ):
            if produced.get("kind") == "PRIORITY_DEFEAT":
                errors.append("PRIORITY_DIRECTION_REVERSED")
            else:
                errors.append("EDGE_DIRECTION_MISMATCH")
        elif (
            produced.get("attacker_id") != expected.get("attacker_id")
            or produced.get("target_id") != expected.get("target_id")
        ):
            errors.append("EDGE_DIRECTION_MISMATCH")
        elif produced.get("kind") != expected.get("kind") or produced.get(
            "input_witness"
        ) != expected.get("input_witness"):
            errors.append("EDGE_CONTENT_MISMATCH")

    rule_by_argument = _argument_rule_map(output_arguments)
    priority_pairs = {
        (priority.get("winner"), priority.get("loser")) for priority in priorities
    }
    for attack in output_attacks:
        attack_id = attack.get("attack_id")
        if attack_id not in expected_attack_by_id:
            errors.append("SPURIOUS_EDGE")
            continue
        if attack.get("input_witness") not in tokens:
            errors.append("SPURIOUS_EDGE")
        if attack.get("kind") == "PRIORITY_DEFEAT":
            attacker_rule = rule_by_argument.get(attack.get("attacker_id"))
            target_rule = rule_by_argument.get(attack.get("target_id"))
            if (attacker_rule, target_rule) not in priority_pairs:
                if (target_rule, attacker_rule) in priority_pairs:
                    errors.append("PRIORITY_DIRECTION_REVERSED")
                else:
                    errors.append("PRIORITY_WITNESS_MISSING")

    deduplicated = list(dict.fromkeys(errors))
    if not deduplicated:
        checks.append(
            "No expected edge omitted, no spurious edge produced, no direction reversed."
        )
    return TranslationWitnessReport(
        satisfied=not deduplicated,
        error_codes=tuple(deduplicated),
        checks=tuple(checks),
    )
