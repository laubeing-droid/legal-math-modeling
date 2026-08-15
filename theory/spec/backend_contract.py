#!/usr/bin/env python3
"""P04 multi-backend contract reference semantics.

Backends: DIRECT_REFERENCE, HORN, ARGUMENTATION, CLOSED_FORM, ASP, SMT.
Routing over typed features is total and deterministic; unsupported
features never fall into a wrong backend. UNKNOWN/TIMEOUT/
BACKEND_UNAVAILABLE/ERROR never map to FALSE, REFUTED, or PASS.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Any, Mapping, Optional, Tuple

BACKENDS = frozenset(
    {"DIRECT_REFERENCE", "HORN", "ARGUMENTATION", "CLOSED_FORM", "ASP", "SMT"}
)

DECISIVE_OUTCOMES = frozenset({"SAT", "UNSAT"})
FAIL_CLOSED_OUTCOMES = frozenset(
    {"UNKNOWN", "TIMEOUT", "BACKEND_UNAVAILABLE", "ERROR"}
)


@dataclass(frozen=True)
class RoutingReport:
    backend: Optional[str]
    error_codes: Tuple[str, ...]


def route_backend(features: Mapping[str, Any]) -> RoutingReport:
    """Deterministic routing over typed features."""

    errors: list = []
    required_flags = (
        "needs_nonmonotonic",
        "needs_arithmetic",
        "needs_disjunction",
        "plain_horn",
    )
    for flag in required_flags:
        if flag not in features:
            errors.append(f"MISSING_FEATURE:{flag}")
        elif not isinstance(features[flag], bool):
            errors.append(f"WRONG_FEATURE_SORT:{flag}")
    if errors:
        return RoutingReport(None, tuple(errors))

    if features["needs_nonmonotonic"]:
        return RoutingReport("ASP", ())
    if features["needs_arithmetic"]:
        return RoutingReport("SMT", ())
    if features["needs_disjunction"]:
        return RoutingReport("ASP", ())
    if features["plain_horn"]:
        return RoutingReport("HORN", ())
    return RoutingReport("DIRECT_REFERENCE", ())


def classify_outcome(outcome: str) -> str:
    """Map solver outcomes; fail-closed outcomes never become decisive."""

    if outcome in DECISIVE_OUTCOMES:
        return "DECISIVE"
    if outcome in FAIL_CLOSED_OUTCOMES:
        return "FAIL_CLOSED"
    return "FAIL_CLOSED"


def outcome_to_failure_status(outcome: str) -> str:
    mapping = {
        "SAT": "SUCCESS",
        "UNSAT": "SUCCESS",
        "UNKNOWN": "UNKNOWN",
        "TIMEOUT": "TIMEOUT",
        "BACKEND_UNAVAILABLE": "BACKEND_UNAVAILABLE",
        "ERROR": "ERROR",
    }
    return mapping.get(outcome, "ERROR")


def check_solver_receipt(receipt: Mapping[str, Any]) -> Tuple[bool, Tuple[str, ...]]:
    """Solver identity/options/seed/limits/problem digest are receipt identity."""

    errors: list = []
    for field in ("solver_id", "options_digest", "seed", "limits", "problem_digest"):
        if receipt.get(field) in (None, ""):
            errors.append(f"MISSING_RECEIPT_FIELD:{field}")
    if not errors and receipt.get("outcome") not in DECISIVE_OUTCOMES | FAIL_CLOSED_OUTCOMES:
        errors.append("UNKNOWN_OUTCOME")
    return (not errors, tuple(errors))
