"""Gates over the repo-wide closure census (the report's "`Iff.rfl` 全仓定向扫" UNKNOWN).

The census turns a sampling claim into a counted one: P1-10 said a quarter of the
declarations are contract relabelling, and the only graded surface was the 133
T-spectrum carriers. This artifact classifies how every theorem in the package is
closed, so the shape claim rests on a count that anyone can regenerate.
"""

from __future__ import annotations

import importlib.util
import json
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
TOOL = ROOT / "scripts" / "ci" / "generate_trivial_proof_census.py"
CENSUS = ROOT / "docs" / "formal-release" / "trivial_proof_census.json"
MANIFEST = ROOT / "docs" / "formal-release" / "theorem_inventory_v3.json"

_spec = importlib.util.spec_from_file_location("generate_trivial_proof_census", TOOL)
census = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(census)


def _doc() -> dict:
    return json.loads(CENSUS.read_text(encoding="utf-8"))


def test_closure_classes_partition_every_theorem() -> None:
    doc = _doc()
    counts = doc["closure_counts"]
    assert set(counts) == {"TRIVIAL_TERM", "DECIDE_CLOSED", "TACTIC"}
    assert sum(counts.values()) == doc["theorem_declarations"], "a class is missing or double"
    assert len(doc["trivial_term_declarations"]) == counts["TRIVIAL_TERM"]


def test_census_and_manifest_count_the_same_declarations() -> None:
    """One grammar across the artifacts, checked against the other artifact's total."""

    inv = json.loads(MANIFEST.read_text(encoding="utf-8"))
    by_path = {f["path"]: f for f in inv["files"]}
    package = sum(by_path[p]["theorem_count"] for p in inv["scopes"]["juris_lean_package"])
    assert _doc()["theorem_declarations"] == package, (
        "the census and the source inventory disagree about how many theorems exist; "
        "they should share scripts/lean_grammar.py's rule"
    )


def test_classifier_is_not_vacuous() -> None:
    cases = {
        "theorem a : 1 = 1 := rfl": "TRIVIAL_TERM",
        "theorem b : True := trivial": "TRIVIAL_TERM",
        "theorem c : p ↔ q := Iff.rfl": "TRIVIAL_TERM",
        "theorem d : f x = f x := by\n  rfl": "TRIVIAL_TERM",
        "theorem e : decide (1 = 1) := by decide": "DECIDE_CLOSED",
        "theorem f : x = x := by\n  induction x with\n  | zero => rfl": "TACTIC",
        "theorem g (h : A) : B := by\n  simp [h]": "TACTIC",
    }
    for block, want in cases.items():
        assert census.classify(block) == want, block


def test_commented_proofs_do_not_count() -> None:
    """A `theorem ... := rfl` inside a comment block is not a declaration.

    This is the exact shape the UNPROVED targets took after the P0-3 downgrade, so
    the census would otherwise re-inflate the count it is supposed to police.
    """

    code = census.strip_comments("/-\ntheorem ghost : True := trivial\n-\n")
    assert "ghost" not in code
    assert census.blocks(census.strip_comments("-- theorem ghost : True := rfl")) == []


def test_check_mode_passes_offline() -> None:
    proc = subprocess.run(
        [sys.executable, str(TOOL), "--check"], cwd=ROOT,
        capture_output=True, text=True, encoding="utf-8", errors="replace",
    )
    assert proc.returncode == 0, proc.stdout + proc.stderr


def test_census_labels_what_it_does_not_judge() -> None:
    doc = _doc()
    assert doc["status"] == "source_shape_census_not_a_judgement_about_content"
    assert "not Lean-compiler evidence" in doc["authority_note"]
    assert doc["schema_version"] == "trivial-proof-census-v1"
