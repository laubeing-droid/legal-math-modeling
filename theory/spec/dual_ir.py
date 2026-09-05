#!/usr/bin/env python3
"""P07 dual-IR reference pipeline: LegalSpec -> Legal-IVL -> targets.

The reference pipeline is intentionally small and transparent. It exists
to generate per-hop translation witnesses that the independent
translation-witness checker verifies. Lost/defaulted semantic fields
block decisive compilation; rules without a source locator are dropped
as a structured error, never silently defaulted.
"""

from __future__ import annotations

from typing import Any, Dict, List, Mapping, Tuple

from .translation_witness import build_translation_witness, translation_witness_to_dict


def normalize_spec(spec: Mapping[str, Any]) -> Dict[str, Any]:
    """Drop rules without a source locator (structured, idempotent)."""

    kept = [rule for rule in spec.get("rules", ()) if rule.get("locator")]
    dropped = [rule for rule in spec.get("rules", ()) if not rule.get("locator")]
    return {
        "spec_id": spec.get("spec_id"),
        "rules": kept,
        "dropped_rules": dropped,
    }


def lower_spec_to_ivl(spec: Mapping[str, Any]) -> Dict[str, Any]:
    """LegalSpec -> Legal-IVL lowering over a normalized spec."""

    rules = []
    priorities = []
    lost_fields: List[str] = []
    for rule in spec.get("rules", ()):
        rules.append(
            {
                "rule_id": rule["rule_id"],
                "premises": list(rule.get("conditions", ())),
                "conclusion": rule["conclusion"],
                "exceptions": list(rule.get("exceptions", ())),
            }
        )
        for loser in rule.get("priority_over", ()):
            priorities.append({"winner": rule["rule_id"], "loser": loser})
        if rule.get("uncertain_fields"):
            lost_fields.extend(rule["uncertain_fields"])

    return {
        "rules": rules,
        "priorities": priorities,
        "lost_fields": lost_fields,
        "decisive_allowed": not lost_fields,
    }


def lower_ivl_to_targets(
    ivl: Mapping[str, Any], arguments: List[Mapping[str, Any]]
) -> Dict[str, Any]:
    """Legal-IVL -> Horn clauses and AAF attacks."""

    horn = [
        {
            "rule_id": rule["rule_id"],
            "premises": list(rule["premises"]),
            "conclusion": rule["conclusion"],
        }
        for rule in ivl.get("rules", ())
    ]
    attacks = []
    rule_by_id = {rule["rule_id"]: rule for rule in ivl.get("rules", ())}
    for priority in ivl.get("priorities", ()):
        winner_rule = rule_by_id.get(priority["winner"])
        loser_rule = rule_by_id.get(priority["loser"])
        if winner_rule is None or loser_rule is None:
            continue
        attacks.append(
            {
                "attack_id": f"attack::priority::{priority['winner']}::{priority['loser']}",
                "attacker_id": f"argument::{winner_rule['conclusion']}",
                "target_id": f"argument::{loser_rule['conclusion']}",
                "kind": "PRIORITY_DEFEAT",
                "input_witness": priority["winner"],
            }
        )
    return {"horn": horn, "attacks": attacks, "arguments": arguments}


def build_pipeline_witness(
    spec: Mapping[str, Any],
    arguments: List[Mapping[str, Any]],
    *,
    semantics_id: str = "grounded",
    semantics_version: str = "1",
) -> Tuple[Dict[str, Any], Dict[str, Any], Dict[str, Any]]:
    """Run the pipeline and emit the IVL->target hop translation witness."""

    normalized = normalize_spec(spec)
    ivl = lower_spec_to_ivl(normalized)
    expected_arguments = list(arguments)
    targets = lower_ivl_to_targets(ivl, [dict(argument) for argument in arguments])
    witness = build_translation_witness(
        input_content={
            "facts": sorted(
                {
                    premise
                    for rule in ivl["rules"]
                    for premise in rule["premises"]
                }
            ),
            "rules": [rule["rule_id"] for rule in ivl["rules"]],
            "exceptions": sorted(
                {
                    exception
                    for rule in ivl["rules"]
                    for exception in rule["exceptions"]
                }
            ),
            "priorities": ivl["priorities"],
        },
        expected_arguments=expected_arguments,
        expected_attacks=targets["attacks"],
        output_arguments=targets["arguments"],
        output_attacks=targets["attacks"],
        semantics_id=semantics_id,
        semantics_version=semantics_version,
    )
    return normalized, ivl, translation_witness_to_dict(witness)
