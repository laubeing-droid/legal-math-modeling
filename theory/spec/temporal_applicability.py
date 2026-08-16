#!/usr/bin/env python3
"""P06 temporal applicability reference semantics.

Distinguishes publication time, effective interval, event time, observed
time, as-of time, decision time, correction/retraction time, and the
supersession chain. Interval endpoints and timezone granularity are
explicit. Observed-at never lags behind the allowed as-of (no future
information backflow). Retracted/corrected/superseded sources invalidate
their old certificates.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Any, Iterable, List, Mapping, Optional, Tuple

TEMPORAL_SCHEMA = "spec-temporal-applicability-v2"

VERSION_STATUSES = frozenset({"ACTIVE", "SUPERSEDED", "RETRACTED", "CORRECTED"})


@dataclass(frozen=True)
class TemporalReport:
    applicable: bool
    error_codes: Tuple[str, ...]
    checks: Tuple[str, ...]


def effective_at(version: Mapping[str, Any], day: int) -> bool:
    """Left-closed effective interval; right endpoint closed when present."""

    if day < version["effective_from"]:
        return False
    upper = version.get("effective_to")
    return upper is None or day <= upper


def check_temporal_applicability(
    version: Mapping[str, Any],
    *,
    event_day: int,
    observed_day: int,
    as_of_day: int,
    decision_day: Optional[int] = None,
) -> TemporalReport:
    """Verify version applicability at the decision/event time points."""

    errors: List[str] = []
    checks: List[str] = []

    if version.get("schema_version") != TEMPORAL_SCHEMA:
        errors.append("UNKNOWN_SCHEMA")

    if version.get("status") not in VERSION_STATUSES:
        errors.append("UNKNOWN_VERSION_STATUS")
    elif version["status"] != "ACTIVE":
        errors.append(f"{version['status']}_SOURCE_INVALIDATED")

    if version.get("timezone") is None or version.get("granularity") is None:
        errors.append("IMPLICIT_TIME_GRANULARITY")

    effective_from = version.get("effective_from")
    effective_to = version.get("effective_to")
    if effective_from is None:
        errors.append("MISSING_EFFECTIVE_INTERVAL")
    elif effective_to is not None and effective_to < effective_from:
        errors.append("INVERTED_EFFECTIVE_INTERVAL")

    if observed_day > as_of_day:
        errors.append("FUTURE_INFORMATION_BACKFLOW")

    if effective_from is not None:
        if not effective_at(version, event_day):
            errors.append("OUTSIDE_EFFECTIVE_INTERVAL")
        if decision_day is not None and not effective_at(version, decision_day):
            errors.append("DECISION_OUTSIDE_EFFECTIVE_INTERVAL")

    deduplicated = list(dict.fromkeys(errors))
    if not deduplicated:
        checks.append("Version applicable at bound time points.")
    return TemporalReport(
        applicable=not deduplicated,
        error_codes=tuple(deduplicated),
        checks=tuple(checks),
    )


def build_version_record(
    *,
    snapshot_id: str,
    publication_day: int,
    effective_from: int,
    effective_to: Optional[int] = None,
    status: str = "ACTIVE",
    timezone: str = "UTC",
    granularity: str = "DAY",
) -> dict:
    """Assemble an explicit version record for fixtures and tests."""

    return {
        "schema_version": TEMPORAL_SCHEMA,
        "snapshot_id": snapshot_id,
        "publication_day": publication_day,
        "effective_from": effective_from,
        "effective_to": effective_to,
        "status": status,
        "timezone": timezone,
        "granularity": granularity,
    }


def check_supersession_chain(edges: Iterable[Mapping[str, str]]) -> Tuple[str, ...]:
    """Classify supersession chains; self-supersession and cycles fail."""

    errors: List[str] = []
    seen_pairs = set()
    adjacency: dict = {}
    for edge in edges:
        old, new = edge.get("old"), edge.get("new")
        if old == new:
            errors.append("SELF_SUPERSESSION")
        if (old, new) in seen_pairs:
            errors.append("DUPLICATE_SUPERSESSION")
        seen_pairs.add((old, new))
        adjacency.setdefault(old, set()).add(new)

    for start in adjacency:
        visited = set()
        stack = [start]
        while stack:
            node = stack.pop()
            if node in visited:
                continue
            visited.add(node)
            for nxt in adjacency.get(node, ()):
                if nxt == start:
                    errors.append("SUPERSESSION_CYCLE")
                stack.append(nxt)

    return tuple(dict.fromkeys(errors))
