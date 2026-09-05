#!/usr/bin/env python3
"""P09 three-gate fact admission reference semantics.

source gate != interpretation gate != fact gate. Each gate has an
independent state PASS | FAIL | BLOCKED | DISPUTED. Hash/content binding
never implies source authority; rule/checker/solver PASS never implies
fact reliability. Candidate, user-assumed, disputed, revoked, or expired
attestations never enter the decisive premise set.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Any, Iterable, List, Mapping, Optional, Tuple

GATE_STATES = frozenset({"PASS", "FAIL", "BLOCKED", "DISPUTED"})
ADMITTED_STATUS = "ADMITTED"
NON_DECISIVE_STATUSES = frozenset(
    {"CANDIDATE", "USER_ASSUMED", "DISPUTED", "REVOKED", "EXPIRED"}
)


@dataclass(frozen=True)
class AdmissionReport:
    admitted: bool
    taint: str
    error_codes: Tuple[str, ...]
    checks: Tuple[str, ...]


def compute_taint(inputs: Iterable[Mapping[str, Any]]) -> str:
    """Any tainted input taints the whole derivation (no laundering)."""

    for item in inputs:
        if item.get("taint") == "TAINTED":
            return "TAINTED"
    return "CLEAN"


def check_fact_admission(
    candidate: Mapping[str, Any],
    *,
    gates: Mapping[str, str],
    attestations: Iterable[Mapping[str, Any]] = (),
    case_scope: Optional[str] = None,
    run_scope: Optional[str] = None,
) -> AdmissionReport:
    """Verify the three gates, attestation binding, and taint closure."""

    errors: List[str] = []
    checks: List[str] = []

    for gate in ("source", "interpretation", "fact"):
        state = gates.get(gate)
        if state not in GATE_STATES:
            errors.append(f"UNKNOWN_{gate.upper()}_GATE_STATE")
        elif state != "PASS":
            errors.append(f"{gate.upper()}_GATE_{state}")

    attestation_list = tuple(attestations)
    if not attestation_list:
        errors.append("MISSING_ATTESTATION")

    for attestation in attestation_list:
        status = attestation.get("status")
        if status != ADMITTED_STATUS:
            if status in NON_DECISIVE_STATUSES:
                errors.append(f"{status}_ATTESTATION_NOT_DECISIVE")
            else:
                errors.append("UNKNOWN_ATTESTATION_STATUS")
        if case_scope is not None and attestation.get("case_scope") != case_scope:
            errors.append("CROSS_SCOPE_REPLAY")
        if run_scope is not None and attestation.get("run_scope") != run_scope:
            errors.append("CROSS_RUN_REPLAY")
        if attestation.get("fact_id") != candidate.get("fact_id"):
            errors.append("ATTESTATION_BINDING_MISMATCH")
        if attestation.get("revoked") is True:
            errors.append("REVOKED_ATTESTATION_NOT_DECISIVE")
        if attestation.get("expired") is True:
            errors.append("EXPIRED_ATTESTATION_NOT_DECISIVE")

    taint = compute_taint(candidate.get("inputs", ()))
    if taint == "TAINTED":
        errors.append("TAINTED_INPUT_NONINTERFERENCE")

    deduplicated = list(dict.fromkeys(errors))
    if not deduplicated:
        checks.append("All three gates PASS with bound, admitted attestations.")
    return AdmissionReport(
        admitted=not deduplicated,
        taint=taint,
        error_codes=tuple(deduplicated),
        checks=tuple(checks),
    )


def revoke_attestation(attestations: Iterable[Mapping[str, Any]], fact_id: str) -> List[dict]:
    """Monotone revocation: only the targeted fact's attestation changes."""

    result = []
    for attestation in attestations:
        updated = dict(attestation)
        if attestation.get("fact_id") == fact_id:
            updated["status"] = "REVOKED"
            updated["revoked"] = True
        result.append(updated)
    return result
