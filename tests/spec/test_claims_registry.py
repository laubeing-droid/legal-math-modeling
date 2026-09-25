"""Gate tests for the RC-02 machine-readable claims registry.

The registry mirrors ALLOWED_CLAIMS.md / FORBIDDEN_CLAIMS.md exactly; the
drift gate re-parses both markdown surfaces and compares claim text, so
editing one side without the other fails closed. Content gates: unique ids,
the fallback rule (absent evidence is UNKNOWN/BLOCKED, never PASS), and the
registry-size claim tracking the live canonical registry (52 after TY-01..04).
"""

from __future__ import annotations

import re

import pytest

from theory.spec.claims_registry import (
    ClaimsRegistryDefect,
    drift_problems,
    load_registry,
    parse_allowed_md,
    parse_forbidden_md,
)
from theory.spec.canonical_v2 import canonical_v2_type_names


def test_registry_loads_with_unique_ids_and_fallback() -> None:
    doc = load_registry()

    assert len(doc["allowed"]) == 7
    assert len(doc["forbidden"]) == 11
    assert "UNKNOWN" in doc["fallback_rule"] and "PASS" in doc["fallback_rule"]


def test_registry_stays_in_lockstep_with_markdown_sources() -> None:
    assert drift_problems() == []


def test_tampered_registry_surfaces_as_drift(tmp_path, monkeypatch) -> None:
    import json

    import theory.spec.claims_registry as cr

    doctored = load_registry()
    doctored["forbidden"][0]["claim"] = "everything is fine, actually"
    fake = tmp_path / "claims_registry.json"
    fake.write_text(json.dumps(doctored, ensure_ascii=False), encoding="utf-8")
    monkeypatch.setattr(cr, "REGISTRY_PATH", fake)

    problems = cr.drift_problems()
    assert problems, "tampered registry must not pass the drift gate"


def test_registry_size_claim_tracks_live_registry() -> None:
    doc = load_registry()
    size_claims = [
        row["claim"] for row in doc["allowed"] if "distinct types" in row["claim"]
    ]
    assert len(size_claims) == 1
    match = re.search(r"contains (\d+) distinct types", size_claims[0])
    assert match is not None
    assert int(match.group(1)) == len(canonical_v2_type_names())


def test_python_suite_claim_requires_full_execution_report() -> None:
    # The allowed claim about the Python suite must demand the full report,
    # never a subset run (AGENTS: never report a subset as a full pass).
    row = next(r for r in load_registry()["allowed"] if r["claim"] == "The Python suite passed")
    assert "Full collection and full execution report" in row["minimum_evidence"]
