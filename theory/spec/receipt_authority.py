#!/usr/bin/env python3
"""P01/P05 receipt authority reference semantics.

Authority lattice UNTRUSTED_PROPOSAL < SOURCE_BOUND_CANDIDATE <
HUMAN_REVIEWED_CANDIDATE < ADMITTED_FORMAL_INPUT. Levels never escalate
through count, confidence, model identity, or repeated runs; escalation
requires an independent, scope-bound external authority receipt. Human
receipts prove only that the named person/role performed the named action
on the named input; they never prove legal correctness.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Any, Iterable, List, Mapping, Optional, Tuple

AUTHORITY_ORDER = (
    "UNTRUSTED_PROPOSAL",
    "SOURCE_BOUND_CANDIDATE",
    "HUMAN_REVIEWED_CANDIDATE",
    "ADMITTED_FORMAL_INPUT",
)

REQUIRED_LEVEL = {
    "PROPOSAL": "UNTRUSTED_PROPOSAL",
    "SOURCE_BINDING": "SOURCE_BOUND_CANDIDATE",
    "FACT_ATTESTATION": "ADMITTED_FORMAL_INPUT",
    "CERTIFICATE": "ADMITTED_FORMAL_INPUT",
    "DECISION_STATUS": "ADMITTED_FORMAL_INPUT",
}


def authority_rank(level: str) -> int:
    if level not in AUTHORITY_ORDER:
        raise ValueError(f"Unknown authority level: {level}")
    return AUTHORITY_ORDER.index(level)


def can_issue(issuer_level: str, artifact_kind: str) -> bool:
    required = REQUIRED_LEVEL.get(artifact_kind)
    if required is None:
        return False
    return authority_rank(issuer_level) >= authority_rank(required)


@dataclass(frozen=True)
class ReceiptReport:
    valid: bool
    escalated_level: Optional[str]
    error_codes: Tuple[str, ...]


def verify_authority_receipt(
    receipt: Mapping[str, Any],
    *,
    expected_scope: Optional[str] = None,
    now_day: Optional[int] = None,
) -> ReceiptReport:
    """Verify an escalation receipt; fail-closed on any binding defect."""

    errors: List[str] = []

    issuer = receipt.get("issuer_level")
    target = receipt.get("target_level")
    if issuer not in AUTHORITY_ORDER or target not in AUTHORITY_ORDER:
        errors.append("UNKNOWN_AUTHORITY_LEVEL")
    else:
        if authority_rank(target) != authority_rank(issuer) + 1:
            errors.append("LEVEL_SKIP_NOT_ALLOWED")
        if authority_rank(target) <= authority_rank(issuer):
            errors.append("NO_ESCALATION")

    if expected_scope is not None and receipt.get("case_scope") != expected_scope:
        errors.append("RECEIPT_SCOPE_MISMATCH")

    if not receipt.get("issuer_identity"):
        errors.append("MISSING_ISSUER_IDENTITY")
    if not receipt.get("subject"):
        errors.append("MISSING_RECEIPT_SUBJECT")
    if receipt.get("self_issued") is True:
        errors.append("SELF_ISSUED_RECEIPT")

    if now_day is not None:
        issued_day = receipt.get("issued_day")
        expiry_day = receipt.get("expiry_day")
        if issued_day is None or expiry_day is None:
            errors.append("MISSING_RECEIPT_VALIDITY_WINDOW")
        elif not (issued_day <= now_day <= expiry_day):
            errors.append("RECEIPT_EXPIRED")

    if receipt.get("revoked") is True:
        errors.append("RECEIPT_REVOKED")

    deduplicated = list(dict.fromkeys(errors))
    escalated = None
    if not deduplicated:
        escalated = target
    return ReceiptReport(
        valid=not deduplicated,
        escalated_level=escalated,
        error_codes=tuple(deduplicated),
    )


def consensus_level(levels: Iterable[str]) -> str:
    """Consensus over proposals never escalates: the max level wins."""

    levels = tuple(levels)
    if not levels:
        return "UNTRUSTED_PROPOSAL"
    return AUTHORITY_ORDER[max(authority_rank(level) for level in levels)]
