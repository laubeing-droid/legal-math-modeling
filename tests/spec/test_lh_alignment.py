"""LH-01/LH-02 gate tests: the 127 external-ledger targets stay honestly
pending, and the P01-P13 mapping names theorems that actually exist in the
repo, copied verbatim from FullMath/Acceptance.lean."""

from __future__ import annotations

import json
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
LH01 = ROOT / "theory" / "spec" / "lh_alignment" / "lh01_t_targets.json"
LH02 = ROOT / "theory" / "spec" / "lh_alignment" / "lh02_probability_mapping.json"
ACCEPTANCE = (
    ROOT / "proofs" / "lean" / "juris_lean" / "JurisLean" / "FullMath" / "Acceptance.lean"
)


def test_lh01_has_127_pending_external_targets() -> None:
    doc = json.loads(LH01.read_text(encoding="utf-8"))
    ids = [row["id"] for row in doc["targets"]]
    assert ids == [f"T{i:02d}" for i in range(1, 128)]
    assert len(set(ids)) == 127
    assert all(row["status"] == "EXTERNAL_LEDGER_PENDING" for row in doc["targets"])
    assert all(row["layer"] is None for row in doc["targets"])
    assert doc["namespace"] == "EXTERNAL_T_LEDGER"


def test_lh02_rows_are_complete_and_never_rewritten() -> None:
    doc = json.loads(LH02.read_text(encoding="utf-8"))
    ids = [row["id"] for row in doc["rows"]]
    assert ids == [f"P{i:02d}" for i in range(1, 14)]
    assert all(row["theorem"] for row in doc["rows"])
    assert all(row["proof_file"] for row in doc["rows"])
    assert all(row["rewritten"] is False for row in doc["rows"])


def test_lh02_theorem_names_match_acceptance_verbatim() -> None:
    acceptance = ACCEPTANCE.read_text(encoding="utf-8")
    doc = json.loads(LH02.read_text(encoding="utf-8"))
    for row in doc["rows"]:
        # The acceptance line assigns each target to a fully qualified theorem.
        pattern = rf"theorem target_{row['id']} : Contracts\.target_{row['id']} := (\S+)"
        match = re.search(pattern, acceptance)
        assert match is not None, f"{row['id']} missing from Acceptance.lean"
        assert match.group(1) == row["theorem"], row["id"]


def test_lh02_proof_files_exist_and_declare_the_theorem() -> None:
    doc = json.loads(LH02.read_text(encoding="utf-8"))
    for row in doc["rows"]:
        proof = ROOT / row["proof_file"]
        assert proof.exists(), row["proof_file"]
        text = proof.read_text(encoding="utf-8")
        bare = row["theorem"].rsplit(".", 1)[-1]
        assert re.search(rf"^theorem {bare}\b", text, re.MULTILINE), (
            f"{bare} not declared in {row['proof_file']}"
        )
