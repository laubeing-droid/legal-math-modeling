#!/usr/bin/env python3
"""v1 -> v2 migration with an explicit loss report.

v1 records stay parseable forever but never gain v2 decisive status. The
migrator maps v1 payloads into v2 shapes and records every missing v2
field as an explicit loss entry; nothing is silently defaulted into an
authoritative position. Facts without a source binding migrate as
candidates only.
"""

from __future__ import annotations

from typing import Any, Dict, List, Mapping

from .types import DecisionStatus, IdKind, TypedId

V2_SCHEMA = "spec-canonical-v2"

_KNOWN_V1_FACT_FIELDS = {"fact_id", "predicate", "arguments", "source_ref", "attributes"}
_KNOWN_V1_RULE_FIELDS = {
    "rule_id",
    "kind",
    "premises",
    "conclusions",
    "exceptions",
    "priority_over",
    "notes",
}


def migrate_v1_fact(payload: Mapping[str, Any]) -> Dict[str, Any]:
    """Migrate one v1 canonical fact into v2 with a loss report."""

    loss_report: List[str] = []
    fact_id = payload.get("fact_id")
    if not fact_id:
        loss_report.append("MISSING_FACT_ID")
        fact_id = "unknown"

    source_ref = payload.get("source_ref")
    if not source_ref:
        loss_report.append("NO_SOURCE_BINDING_DOWNGRADED_TO_CANDIDATE")

    unknown_fields = sorted(set(payload) - _KNOWN_V1_FACT_FIELDS)
    for field in unknown_fields:
        loss_report.append(f"UNKNOWN_V1_FIELD:{field}")

    return {
        "schema_version": V2_SCHEMA,
        "type": "LegalFact",
        "id": TypedId(IdKind.FACT, str(fact_id)).canonical,
        "predicate": payload.get("predicate", ""),
        "arguments": list(payload.get("arguments", ())),
        "source_ref": source_ref,
        "authority_level": (
            "SOURCE_BOUND_CANDIDATE" if source_ref else "UNTRUSTED_PROPOSAL"
        ),
        "admitted": False,
        "loss_report": loss_report,
    }


def migrate_v1_rule(payload: Mapping[str, Any]) -> Dict[str, Any]:
    """Migrate one v1 canonical rule into v2 with a loss report."""

    loss_report: List[str] = []
    rule_id = payload.get("rule_id")
    if not rule_id:
        loss_report.append("MISSING_RULE_ID")
        rule_id = "unknown"

    if not payload.get("conclusions"):
        loss_report.append("EMPTY_CONCLUSIONS")

    unknown_fields = sorted(set(payload) - _KNOWN_V1_RULE_FIELDS)
    for field in unknown_fields:
        loss_report.append(f"UNKNOWN_V1_FIELD:{field}")

    return {
        "schema_version": V2_SCHEMA,
        "type": "LegalRule",
        "id": TypedId(IdKind.RULE, str(rule_id)).canonical,
        "kind": payload.get("kind", ""),
        "version": "unknown",
        "premises": list(payload.get("premises", ())),
        "conclusions": list(payload.get("conclusions", ())),
        "exceptions": list(payload.get("exceptions", ())),
        "priority_over": list(payload.get("priority_over", ())),
        "loss_report": loss_report,
    }


def migrate_v1_payload(payload: Mapping[str, Any]) -> Dict[str, Any]:
    """Migrate a v1 certificate-shaped payload header; v1 stays non-decisive."""

    status = payload.get("status")
    known_statuses = {member.value for member in DecisionStatus}
    loss_report: List[str] = ["V1_PAYLOAD_NEVER_DECISIVE_IN_V2"]
    if status not in known_statuses:
        loss_report.append(f"UNKNOWN_V1_STATUS:{status}")
        status = DecisionStatus.UNDECIDED.value

    return {
        "schema_version": V2_SCHEMA,
        "type": "MigrationReport",
        "source_schema": payload.get("schema_version", "unknown"),
        "migrated_status": status,
        "decisive": False,
        "loss_report": loss_report,
    }
