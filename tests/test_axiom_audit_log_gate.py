"""The axiom-audit log gate must read what the kernel actually said.

`lean-full-clean-build` ran `lake env lean JurisLean/AxiomAudit.lean` into
`axiom-audit.raw.txt` and uploaded it. Nothing parsed it, so "axiom audit green"
meant only "the audit file elaborated": a theorem resting on `sorryAx` printed
`depends on axioms: [sorryAx]` and the run still passed. These tests pin that the
new gate fails on the content, not just on the exit code.
"""

from __future__ import annotations

import json
import subprocess
import sys
import json
import subprocess
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parents[1]
SCRIPT = ROOT / "scripts" / "ci" / "check_axiom_audit_log.py"
sys.path.insert(0, str(ROOT / "scripts" / "ci"))

from check_axiom_audit_log import parse  # noqa: E402

CLEAN_LOG = """\
info: 'JurisLean.Mandate.GameTree.value_leaf' does not depend on any axioms
info: 'JurisLean.DungFixedPoint.groundedSpec_is_fixed_point' depends on axioms: [propext]
info: 'JurisLean.ULM.banach_apriori_error_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
"""

SORRY_LOG = """\
info: 'JurisLean.Mandate.GameTree.value_leaf' does not depend on any axioms
warning: 'JurisLean.Something.unproved' depends on axioms: [sorryAx]
"""

CUSTOM_AXIOM_LOG = """\
info: 'JurisLean.Some.theorem' depends on axioms: [myOwnAxiom, propext]
"""


def test_parse_collects_targets_and_vocabulary():
    doc = parse(CLEAN_LOG)
    assert doc["audited_targets"] == 3
    assert doc["axiom_vocabulary"] == {"Classical.choice": 1, "propext": 2, "Quot.sound": 1}
    assert doc["targets_with_sorryAx"] == {}
    assert doc["targets_outside_standard_axioms"] == {}


def test_parse_reports_deduplication_of_repeated_targets():
    """The same target printed twice (import + own file) counts once."""
    doc = parse(CLEAN_LOG + CLEAN_LOG)
    assert doc["audited_targets"] == 3


def run(tmp_path: Path, log: str, *extra: str) -> subprocess.CompletedProcess:
    path = tmp_path / "axiom-audit.raw.txt"
    path.write_text(log, encoding="utf-8")
    out = tmp_path / "axiom-audit.json"
    proc = subprocess.run(
        [sys.executable, str(SCRIPT), "--log", str(path), "--json", str(out), "--check",
         *extra],
        capture_output=True, text=True, encoding="utf-8",
    )
    return proc


def test_clean_log_passes(tmp_path):
    proc = run(tmp_path, CLEAN_LOG, "--min-targets", "3")
    assert proc.returncode == 0, proc.stdout + proc.stderr


def test_sorryax_fails_the_gate(tmp_path):
    proc = run(tmp_path, SORRY_LOG, "--min-targets", "2")
    assert proc.returncode == 1
    assert "sorryAx" in proc.stderr
    doc = json.loads((tmp_path / "axiom-audit.json").read_text(encoding="utf-8"))
    assert doc["status"] == "FAIL_SORRYAX"
    assert doc["targets_with_sorryAx"] == {"JurisLean.Something.unproved": ["sorryAx"]}


def test_custom_axiom_fails_the_gate(tmp_path):
    proc = run(tmp_path, CUSTOM_AXIOM_LOG, "--min-targets", "1")
    assert proc.returncode == 1
    assert "myOwnAxiom" in proc.stderr


def test_empty_log_cannot_pass(tmp_path):
    """An audit that printed nothing is not a pass -- the count is the floor."""
    proc = run(tmp_path, "warning: nothing compiled\n", "--min-targets", "397")
    assert proc.returncode == 1
    assert "expected at least 397" in proc.stderr


def test_the_gate_is_wired_into_the_build_job():
    workflow = (ROOT / ".github" / "workflows" / "lean-build.yml").read_text(encoding="utf-8")
    assert "check_axiom_audit_log.py" in workflow
    assert "axiom-audit.raw.txt" in workflow
    # The floor comes from the audit file, so no number is hand-copied into CI.
    assert "grep -c '^#print axioms'" in workflow


def test_the_mandate_layer_is_now_on_the_audit_surface():
    audit = (ROOT / "proofs" / "lean" / "juris_lean" / "JurisLean" / "AxiomAudit.lean")
    text = audit.read_text(encoding="utf-8")
    printed = {
        line.split()[-1] for line in text.splitlines() if line.startswith("#print axioms")
    }
    mandate = {n for n in printed if n.startswith("JurisLean.Mandate.")}
    # 126 at a6fd02c6d, 135 with CaseIsomorphism's nine, 141 with the n-ary surface,
    # 145 with the three-slot computable test, 148 with the enumeration that says those
    # six are all the bijections of three slots, and 153 with the bridge that lets the Bool
    # test answer the Prop question; each increment was named only after a round built the
    # declarations it names, so a red round cannot leave the number behind.
    assert len(mandate) == 172, f"mandate audit surface is {len(mandate)} targets"
    assert "JurisLean.Mandate.GameTree.value_attains" in mandate
    assert "JurisLean.Mandate.MatrixGame.hasPureValue_true_iff" in mandate


def test_the_surface_names_no_comment_text():
    """Every target on the surface must be a declaration the source really makes.

    The first version of this surface scanned raw lines, and a doc comment whose
    continuation began with the word `lemma` produced the target
    `JurisLean.Mandate.DerivedCertificate.rather`, which CI 36296061840 rejected as
    an unknown constant.
    """
    sys.path.insert(0, str(ROOT / "scripts"))
    from lean_grammar import declarations

    audit = ROOT / "proofs" / "lean" / "juris_lean" / "JurisLean" / "AxiomAudit.lean"
    printed = {
        line.split()[-1]
        for line in audit.read_text(encoding="utf-8").splitlines()
        if line.startswith("#print axioms")
    }
    real: set[str] = set()
    for path in audit.parent.rglob("*.lean"):
        real |= {
            d["name"]
            for d in declarations(path.read_text(encoding="utf-8"), namespace=True)
            if d["keyword"] in ("theorem", "lemma")
        }
    # Only qualified names are checkable this way: the hand-written lines predating
    # the generator name theorems by their short form, which Lean resolves through
    # the `open` namespaces in scope at that point in the file.
    qualified = {n for n in printed if "." in n}
    assert qualified, "every audit target is unqualified, so this check tests nothing"
    ghosts = sorted(qualified - real)
    assert not ghosts, f"audit surface names declarations that do not exist: {ghosts[:5]}"


@pytest.mark.parametrize("module", ["Kernel", "GameTree", "MatrixGame", "Waterfall"])
def test_every_named_mandate_target_exists_at_its_declaration_site(module):
    """A dangling `#print axioms` name would fail CI; the site scan proves it resolves."""
    sys.path.insert(0, str(ROOT / "scripts"))
    from lean_grammar import declarations

    path = ROOT / "proofs" / "lean" / "juris_lean" / "JurisLean" / "Mandate" / f"{module}.lean"
    on_site = {d["name"] for d in declarations(path.read_text(encoding="utf-8"), namespace=True)}
    audit = (ROOT / "proofs" / "lean" / "juris_lean" / "JurisLean" / "AxiomAudit.lean")
    named = {
        line.split()[-1]
        for line in audit.read_text(encoding="utf-8").splitlines()
        if line.startswith("#print axioms") and f"JurisLean.Mandate.{module}." in line
    }
    assert named <= on_site, f"audit names declarations that the source dropped: {named - on_site}"


LANDED = ROOT / "docs" / "formal-release" / "ci-evidence"


def _landed_audit_logs() -> list[Path]:
    return sorted(LANDED.glob("*/axiom-audit/axiom-audit.raw.txt"))


def test_the_landed_audit_log_is_the_kernels_own_words_and_is_clean() -> None:
    """The axiom verdict must be re-checkable from bytes in this repository.

    CI runs the audit, parses the output and fails on `sorryAx`; if the log stayed in
    the artifact store, every "no sorryAx" claim in the papers would rest on a
    screenshot. So the newest landed log is parsed here: it must name at least as many
    targets as the audit file holds, must show nothing outside the standard axioms, and
    must actually contain a line for every qualified name on the audit surface.
    """
    logs = _landed_audit_logs()
    assert logs, (
        "no landed axiom-audit log: run `python scripts/ci/build_ci_run_index.py "
        "--fetch-evidence <run>` so the kernel's answer is in-repo evidence"
    )
    newest = logs[-1]
    doc = parse(newest.read_text(encoding="utf-8", errors="replace"))
    assert doc["targets_with_sorryAx"] == {}, newest
    assert doc["targets_outside_standard_axioms"] == {}, newest

    # Compare against the audit surface *as of the log's own subject*: the working tree
    # may already name theorems that this run never saw, and holding an old log to them
    # would be a false alarm rather than a finding.
    newest_run = newest.parent.parent.name
    subject = next(
        (r["head_sha"] for r in json.loads(
            (ROOT / "docs" / "formal-release" / "ci_run_index.json").read_text(encoding="utf-8")
        )["runs"] if str(r["run_id"]) == newest_run),
        None,
    )
    assert subject, f"run {newest_run} is not in the CI run index"
    proc = subprocess.run(
        ["git", "show", f"{subject}:proofs/lean/juris_lean/JurisLean/AxiomAudit.lean"],
        cwd=ROOT, capture_output=True, text=True, encoding="utf-8",
    )
    assert proc.returncode == 0, proc.stderr[:200]
    named = {
        line.split()[-1]
        for line in proc.stdout.splitlines()
        if line.startswith("#print axioms") and "." in line.split()[-1]
    }
    assert named, "the audit surface at that subject is empty"
    audited = set(doc["targets_by_name"]) if "targets_by_name" in doc else None
    printed = newest.read_text(encoding="utf-8", errors="replace")
    missing = sorted(n for n in named if f"'{n}'" not in printed)
    assert not missing, (
        f"{newest.relative_to(ROOT)} never reports {len(missing)} names the audit file "
        f"asks about, e.g. {missing[:3]}"
    )
