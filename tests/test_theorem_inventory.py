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


def test_built_package_scope_is_reported_separately():
    """A count over all tracked Lean cannot be quoted as what lake build checks."""
    doc = load(INVENTORY)
    pkg = set(doc["scopes"]["juris_lean_package"])
    everything = set(doc["scopes"]["all_tracked_lean"])
    assert pkg <= everything
    assert pkg < everything, "standalone draft artifacts must stay visible as a separate residual"
    assert doc["scope_definitions"]["juris_lean_package"]
    summary = doc["scope_summary"]
    assert summary["juris_lean_package"]["file_count"] == len(pkg)
    assert summary["juris_lean_package"]["theorem_count"] <= summary["all_tracked_lean"]["theorem_count"]


def test_subject_binding_declares_whether_the_label_fits():
    """Qoder audit P2-16: the subject used to lag one commit behind its bytes."""
    doc = load(INVENTORY)
    binding = doc["subject_binding"]
    assert binding["rule"] == "every recorded sha256 must equal git show <subject>:<path>"
    assert binding["files_total"] == len(doc["files"])
    assert binding["binding"] in ("BOUND_TO_SUBJECT", "STALE_SUBJECT")
    diverging = {d["path"] for d in binding["files_diverging_from_subject"]}
    if binding["binding"] == "BOUND_TO_SUBJECT":
        assert not diverging
    # whatever the label says, the diverging paths must be real tracked files
    assert diverging <= {f["path"] for f in doc["files"]}


def test_no_counted_declaration_lives_in_a_sorry_body():
    """Qoder audit P0-3: the inventory counted theorems whose bodies said sorry."""
    import hashlib
    import re
    import subprocess

    doc = load(INVENTORY)
    offenders = []
    for entry in doc["files"]:
        raw = (ROOT / entry["path"]).read_bytes()
        assert hashlib.sha256(raw).hexdigest() == entry["sha256"], entry["path"]
        text = raw.decode("utf-8", errors="replace")
        depth = 0
        owner = None
        for lineno, line in enumerate(text.splitlines(), 1):
            code, depth = _strip_lean_line(line, depth)
            head = re.match(r"^(?:@\[[^\]]*\][ \t]*)*(theorem|lemma)\s+(\S+)", code)
            if head:
                owner = (head.group(2), lineno)
            if owner and re.search(r"\bsorry\b|\badmit\b|native_decide", code):
                offenders.append((entry["path"], owner, lineno))
    assert not offenders, offenders


def _strip_lean_line(line: str, depth: int):
    out = []
    i = 0
    in_string = False
    while i < len(line):
        ch = line[i]
        nxt = line[i + 1] if i + 1 < len(line) else ""
        if depth > 0:
            if ch == "/" and nxt == "-":
                depth += 1
                i += 2
                continue
            if ch == "-" and nxt == "/":
                depth -= 1
                i += 2
                continue
            i += 1
            continue
        if not in_string and ch == "-" and nxt == "-":
            break
        if not in_string and ch == "/" and nxt == "-":
            depth += 1
            i += 2
            continue
        if ch == '"':
            in_string = not in_string
        out.append(ch)
        i += 1
    return "".join(out), depth


def test_guard_scan_covers_every_counted_file():
    """The scan root must reach everything the count covers (audit P1-8)."""
    import subprocess
    import sys

    proc = subprocess.run(
        [sys.executable, str(ROOT / "scripts" / "scan_lean_guards.py"), "--all-tracked"],
        cwd=ROOT,
        capture_output=True,
        text=True,
    )
    assert proc.returncode == 0, proc.stdout + proc.stderr
    doc = load(INVENTORY)
    assert f"{doc['scope_summary']['all_tracked_lean']['file_count']} files" in proc.stdout


def test_generator_can_refuse_a_stale_label(tmp_path):
    import subprocess
    import sys

    out = tmp_path / "strict.json"
    proc = subprocess.run(
        [sys.executable, str(GEN), "--output", str(out), "--require-bound"],
        cwd=ROOT,
        capture_output=True,
        text=True,
    )
    doc = load(INVENTORY)
    bound = not doc["subject_binding"]["files_diverging_from_subject"]
    if bound:
        assert proc.returncode == 0, proc.stdout + proc.stderr
    else:
        assert proc.returncode == 2
        assert "does not describe" in proc.stderr
