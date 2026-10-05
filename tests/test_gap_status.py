"""Gate tests for the generated ten-gap closure status (round-2 F7).

The artifact replaces the hand-written "all ten gaps closed" ledger line; its
value is that a deleted/renamed witness degrades the status instead of leaving
a stale green. The rejection path simulates exactly that.
"""

from __future__ import annotations

import importlib.util
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
TOOL = ROOT / "scripts" / "ci" / "generate_gap_status.py"
ARTIFACT = ROOT / "docs" / "formal-release" / "gap_status.json"

_spec = importlib.util.spec_from_file_location("generate_gap_status", TOOL)
gen = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(gen)


def _status(doc: dict, gid: int) -> str:
    return next(g["status"] for g in doc["gaps"] if g["gap"] == gid)


def test_generator_script_and_artifact_exist() -> None:
    assert TOOL.exists()
    assert ARTIFACT.is_file()


def test_committed_artifact_is_fresh() -> None:
    proc = subprocess.run(
        [sys.executable, str(TOOL), "--check"], capture_output=True, text=True
    )
    assert proc.returncode == 0, proc.stdout + proc.stderr


def test_check_ignores_the_volatile_generated_on() -> None:
    """A correct regeneration on another date/timezone must not read as stale
    (run 37347663435 red: local midnight rolled the date; Linux LF vs CRLF)."""
    doc = gen.build()
    shifted = dict(doc, generated_on="1999-01-01")
    assert gen._strip_volatile(shifted) == gen._strip_volatile(doc)
    assert "generated_on" not in gen._strip_volatile(doc)


def test_status_matches_source_side_truth() -> None:
    doc = gen.build()
    assert _status(doc, 3) == "OPEN", "the registered instanceM refutation must hold gap 3 open"
    assert _status(doc, 1) == "PARTIAL", "no downstream consumer -> gap 1 stays partial"
    assert set(g["gap"] for g in doc["gaps"]) == set(range(1, 11))


def test_no_gap_is_rated_without_evidence() -> None:
    doc = gen.build()
    for g in doc["gaps"]:
        assert g["evidence"], f"gap {g['gap']} has a status without an evidence string"


def test_rejection_path_witness_disappears(monkeypatch) -> None:
    """If the naming-uniqueness theorem is gone, gap 10 must not stay CLOSED."""
    original = gen._seam
    monkeypatch.setattr(gen, "_seam", lambda name: "-- theorem removed\n" if name == "StatuteChain.lean" else original(name))
    doc = gen.build()
    assert _status(doc, 10) == "WITNESS_MISSING"
    assert _status(doc, 3) != "OPEN"  # refutation lives in the same file -> also degraded


def test_gate_is_wired_through_the_ci_pytest_job() -> None:
    workflow = (ROOT / ".github" / "workflows" / "lean-build.yml").read_text(encoding="utf-8")
    assert "pytest" in workflow
    assert Path(__file__).parent.name == "tests"
