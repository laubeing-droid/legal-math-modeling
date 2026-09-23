"""Invariant tests for the generated Lean source inventory."""

import importlib.util
import json
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
GEN = ROOT / "scripts" / "ci" / "generate_theorem_manifest.py"
INVENTORY = ROOT / "docs" / "formal-release" / "theorem_inventory_v3.json"


def generate(tmp_path: Path, name: str) -> Path:
    out = tmp_path / name
    subprocess.run(
        [sys.executable, str(GEN), "--output", str(out)],
        cwd=ROOT,
        capture_output=True,
        text=True,
        check=True,
    )
    return out


def load(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8"))


def test_generation_is_deterministic(tmp_path):
    a = generate(tmp_path, "a.json")
    b = generate(tmp_path, "b.json")
    assert load(a)["source_inventory_digest"] == load(b)["source_inventory_digest"]


def test_committed_inventory_verifies_against_working_tree():
    proc = subprocess.run(
        [sys.executable, str(GEN), "--verify", str(INVENTORY)],
        cwd=ROOT,
        capture_output=True,
        text=True,
    )
    assert proc.returncode == 0, proc.stdout


def test_tampered_hash_is_detected(tmp_path):
    src = generate(tmp_path, "src.json")
    doc = load(src)
    doc["files"][0]["sha256"] = "0" * 64
    tampered = tmp_path / "tampered.json"
    tampered.write_text(json.dumps(doc), encoding="utf-8")
    proc = subprocess.run(
        [sys.executable, str(GEN), "--verify", str(tampered)],
        cwd=ROOT,
        capture_output=True,
        text=True,
    )
    assert proc.returncode == 1
    assert "hash mismatch" in proc.stdout


def test_audit_driver_names_equal_ulm_theorem_names():
    """The axiom audit covers exactly the ULM package's theorems, no more, no less."""
    doc = load(INVENTORY)
    by_path = {f["path"]: f for f in doc["files"]}
    ulm = [by_path[p] for p in doc["scopes"]["ulm_package"]]

    declared = {
        x["name"] for e in ulm for x in e["declarations"] if x["kind"] == "theorem"
    }
    audited = {
        t.rsplit(".", 1)[-1] for e in ulm for t in e["print_axioms_targets"]
    }
    assert audited == declared
    assert len(declared) > 0


def test_inventory_is_bound_to_a_subject_and_labels_authority():
    doc = load(INVENTORY)
    assert len(doc["subject"]["commit"]) == 40
    assert len(doc["subject"]["tree"]) == 40
    assert doc["status"] == "static_source_inventory_not_release_certificate"
    assert "CI_NOT_RUN" in doc["authority_note"]
    assert doc["hash_contract"] == "sha256-raw-committed-bytes-v1"


def test_scope_labels_are_disjoint_and_unioned():
    doc = load(INVENTORY)
    ulm = set(doc["scopes"]["ulm_package"])
    support = set(doc["scopes"]["ulm_import_closure"])
    everything = set(doc["scopes"]["all_tracked_lean"])
    assert not (ulm & support)
    assert (ulm | support) <= everything
