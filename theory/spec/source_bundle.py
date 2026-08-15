#!/usr/bin/env python3
"""P02 source bundle reference semantics.

A source bundle preserves source hierarchy and locators; it never accepts
flat text only. Each entry binds a content digest and a locator digest.
Changing content or locator breaks the corresponding binding. Duplicate
snapshots and references outside the closure fail closed.
"""

from __future__ import annotations

import hashlib
import json
from dataclasses import dataclass
from typing import Any, Iterable, List, Mapping, Tuple

BUNDLE_SCHEMA = "spec-source-bundle-v2"


@dataclass(frozen=True)
class SourceBundleReport:
    satisfied: bool
    error_codes: Tuple[str, ...]
    checks: Tuple[str, ...]


def canonical_digest(value: Any) -> str:
    encoded = json.dumps(
        value, sort_keys=True, separators=(",", ":"), ensure_ascii=False
    ).encode("utf-8")
    return hashlib.sha256(encoded).hexdigest()


def build_bundle_entry(
    *,
    snapshot_id: str,
    locator: Mapping[str, str],
    content: str,
    version: str,
) -> dict:
    """Build one bundle entry with recomputable content/locator digests."""

    return {
        "snapshot_id": snapshot_id,
        "locator": dict(locator),
        "content": content,
        "content_digest": canonical_digest(content),
        "locator_digest": canonical_digest(dict(locator)),
        "version": version,
    }


def build_source_bundle(entries: Iterable[Mapping[str, Any]]) -> dict:
    return {
        "schema_version": BUNDLE_SCHEMA,
        "entries": [dict(entry) for entry in entries],
        "snapshot_ids": [entry["snapshot_id"] for entry in entries],
    }


def check_source_bundle(
    bundle: Mapping[str, Any],
    *,
    known_versions: frozenset[str] = frozenset({"spec-schema-v2"}),
) -> SourceBundleReport:
    """Independently verify structure, bindings, duplicates, and closure."""

    errors: List[str] = []
    checks: List[str] = []

    if bundle.get("schema_version") != BUNDLE_SCHEMA:
        errors.append("UNKNOWN_SCHEMA")

    entries = tuple(bundle.get("entries", ()))
    snapshot_ids = [entry.get("snapshot_id") for entry in entries]
    if len(snapshot_ids) != len(set(snapshot_ids)):
        errors.append("DUPLICATE_SNAPSHOT")

    for entry in entries:
        locator = entry.get("locator")
        if not isinstance(locator, Mapping) or not locator.get("path"):
            errors.append("MISSING_LOCATOR")
            continue
        if entry.get("content_digest") != canonical_digest(entry.get("content")):
            errors.append("SOURCE_DIGEST_MISMATCH")
        if entry.get("locator_digest") != canonical_digest(dict(locator)):
            errors.append("LOCATOR_DIGEST_MISMATCH")
        if entry.get("version") not in known_versions:
            errors.append("UNKNOWN_VERSION")

    declared_ids = set(bundle.get("snapshot_ids", ()))
    if declared_ids != set(snapshot_ids):
        errors.append("BROKEN_REFERENCE")

    deduplicated = list(dict.fromkeys(errors))
    if not deduplicated:
        checks.append("Every entry binding recomputed independently.")
    return SourceBundleReport(
        satisfied=not deduplicated,
        error_codes=tuple(deduplicated),
        checks=tuple(checks),
    )
