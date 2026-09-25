"""LH-01/LH-02 gate tests.

LH-01 v2: the 127 targets are RECOVERED from the in-repo T-spectrum ledger
(docs/master-plan/基线/T谱/), every row carries a first-pass seven-layer
assignment plus a DRAFT_PENDING_USER_REVIEW flag, and every cited source
file actually exists in the repository. LH-02: the P01-P13 mapping names
theorems that actually exist, copied verbatim from FullMath/Acceptance.lean.
"""

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
VALID_LAYERS = {"L0", "L1", "L2", "L3", "L4", "(L5)", "L6"}


def test_lh01_has_127_recovered_targets_with_layers() -> None:
    doc = json.loads(LH01.read_text(encoding="utf-8"))
    rows = doc["targets"]
    ids = [row["id"] for row in rows]
    expected = [f"T{i:02d}" for i in range(1, 10)] + [f"T{i}" for i in range(10, 128)]
    assert ids == expected
    assert len(set(ids)) == 127
    assert doc["schema_version"] == "lh01-t-targets-v2-recovered"


def test_lh01_every_row_layered_and_pending_review() -> None:
    doc = json.loads(LH01.read_text(encoding="utf-8"))
    for row in doc["targets"]:
        assert row["layer"] in VALID_LAYERS, row["id"]
        assert row["layer_rule"].startswith(("R1", "R2", "R3", "R4", "R5", "R6", "R7", "R8", "R9")), row["id"]
        assert row["review_pending"] is True
        assert row["confidence"] in {"high", "medium", "low"}
    # Every layer rule cited by a row exists in the documented rule table.
    rules = set(doc["layer_rules"])
    for row in doc["targets"]:
        assert row["layer_rule"].split()[0] in rules, row["id"]


def test_lh01_cited_sources_exist_in_repo() -> None:
    doc = json.loads(LH01.read_text(encoding="utf-8"))
    cited = set()
    for row in doc["targets"]:
        for token in re.findall(r"T谱/[^\s+（]+", row["source"]):
            cited.add(token)
    assert cited, "no in-repo sources cited"
    for rel in cited:
        assert (ROOT / "docs" / "master-plan" / "基线" / rel).exists(), rel


def test_lh01_tail_has_volumes_from_approved_plan() -> None:
    doc = json.loads(LH01.read_text(encoding="utf-8"))
    tail = {row["id"]: row for row in doc["targets"] if int(row["id"][1:]) >= 112}
    assert len(tail) == 16
    assert all(row["volume"] for row in tail.values())
    v11 = [i for i, r in tail.items() if r["volume"] == "V11"]
    assert v11 == [f"T{i}" for i in list(range(113, 118)) + [120, 121]]
    v05 = sorted(i for i, r in tail.items() if r["volume"] == "V05")
    assert v05 == ["T112", "T118", "T119"]


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
