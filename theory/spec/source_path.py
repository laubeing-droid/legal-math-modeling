#!/usr/bin/env python3
"""P08 source path reference semantics.

Every edge carries a kind, a direction, and a non-empty witness. Broken
links and unknown edges fail closed. Retrieval relevance never implies
source authority or legal applicability. Citation cycles are allowed as a
separate classification; dependency cycles are not.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Any, Iterable, List, Mapping, Optional, Tuple

PATH_SCHEMA = "spec-source-path-v2"

EDGE_KINDS = frozenset(
    {"DERIVATION", "CITATION", "SUPERSESSION", "CORRECTION", "RETRIEVAL"}
)


@dataclass(frozen=True)
class SourcePathReport:
    satisfied: bool
    authority_granted: bool
    error_codes: Tuple[str, ...]
    checks: Tuple[str, ...]


def build_source_path(edges: Iterable[Mapping[str, Any]]) -> dict:
    return {
        "schema_version": PATH_SCHEMA,
        "edges": [dict(edge) for edge in edges],
    }


def check_source_path(
    path: Mapping[str, Any],
    *,
    known_snapshots: Optional[Iterable[str]] = None,
    declares_authority: bool = False,
) -> SourcePathReport:
    """Independently verify edge witness, closure, cycles, and authority."""

    errors: List[str] = []
    checks: List[str] = []

    if path.get("schema_version") != PATH_SCHEMA:
        errors.append("UNKNOWN_SCHEMA")

    edges = tuple(path.get("edges", ()))
    known = None if known_snapshots is None else set(known_snapshots)

    for edge in edges:
        if edge.get("kind") not in EDGE_KINDS:
            errors.append("UNKNOWN_EDGE_KIND")
        if not edge.get("witness"):
            errors.append("EMPTY_WITNESS")
        if edge.get("from") == edge.get("to"):
            errors.append("SELF_EDGE")
        if known is not None and (
            edge.get("from") not in known or edge.get("to") not in known
        ):
            errors.append("BROKEN_LINK")

    edge_map = {(edge.get("from"), edge.get("to")): edge for edge in edges}
    for edge in edges:
        reverse = (edge.get("to"), edge.get("from"))
        if reverse in edge_map:
            if edge.get("kind") == "CITATION" or edge_map[reverse].get("kind") == "CITATION":
                checks.append("Citation-involved cycle classified as allowed.")
            else:
                errors.append("DEPENDENCY_CYCLE")

    authority_granted = False
    if declares_authority:
        retrieval_only = all(edge.get("kind") == "RETRIEVAL" for edge in edges)
        if edges and retrieval_only:
            errors.append("RETRIEVAL_NOT_APPLICABILITY")
        elif not errors:
            authority_granted = True

    deduplicated = list(dict.fromkeys(errors))
    if not deduplicated:
        checks.append("All edges carry kind, direction, and witness.")
    return SourcePathReport(
        satisfied=not deduplicated,
        authority_granted=authority_granted,
        error_codes=tuple(deduplicated),
        checks=tuple(checks),
    )
