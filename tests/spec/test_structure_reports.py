"""Gates for the two generated structure accounts (audit judgements 1 and D12).

Both accounts exist because the repository asserted things it had never
measured: that the concept spectrum is unified by shared mathematical
structure, and that the eleven-volume plan was progressing. These tests keep the
measurements on the record and stop either number from being quietly improved
by editing prose.
"""

from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
TOOL = ROOT / "scripts" / "ci" / "generate_structure_and_volume_reports.py"
KERNEL = ROOT / "docs" / "formal-release" / "kernel_reuse_report.json"
VOLUMES = ROOT / "docs" / "master-plan" / "基线" / "T谱" / "卷覆盖账.jsonl"
LEDGER = ROOT / "theory" / "spec" / "lh_alignment" / "t_p_coverage.jsonl"
PAPER_CN = ROOT / "docs" / "paper-rewrite" / "paper_cn.md"

# Recorded facts about the current corpus. Changing one of these means the
# structure actually changed, not that the wording did.
RECORDED_GENESALYSIS_CARRIERS_PER_THEOREM = 1.59
RECORDED_GENESALYSIS_MATHLIB_MODULES = 1
RECORDED_UNFILED_TARGETS = 16
SHARED_KERNELS = ("JurisLean.FullMath.Core.Foundations", "JurisLean.LegalIds")


def _kernel() -> dict:
    return json.loads(KERNEL.read_text(encoding="utf-8"))


def _volume_rows() -> list[dict]:
    return [
        json.loads(line)
        for line in VOLUMES.read_text(encoding="utf-8").splitlines()
        if line.strip()
    ]


def _ledger_rows() -> list[dict]:
    return [
        json.loads(line)
        for line in LEDGER.read_text(encoding="utf-8").splitlines()
        if line.strip()
    ]


def test_reports_are_reproducible_from_source() -> None:
    proc = subprocess.run([sys.executable, str(TOOL), "--check"], cwd=ROOT,
                          capture_output=True, text=True)
    assert proc.returncode == 0, proc.stdout + proc.stderr


def test_kernel_report_names_the_real_shared_modules() -> None:
    shared = _kernel()["modules_imported_by_5_or_more"]
    for kernel_module in SHARED_KERNELS:
        assert shared.get(kernel_module, 0) >= 5, (kernel_module, shared)


def test_genealogy_does_not_reuse_the_shared_kernels() -> None:
    """Judgement 1 stays on record: the new line is a chain, not a kernel."""
    report = _kernel()
    genealogy = report["genealogy"]
    edges = {e["module"]: e["imports_genealogy_modules"]
             for e in report["genealogy"]["intra_genealogy_import_edges"]}
    assert edges, "no Genealogy import edges measured"
    deps = {d for v in edges.values() for d in v}
    for kernel_module in SHARED_KERNELS:
        assert kernel_module not in deps, (
            f"{kernel_module} is now imported by Genealogy; if the kernel really "
            "was adopted, update this gate together with the paper's unity claim"
        )
    assert genealogy["modules_importing_mathlib"] == [
        "JurisLean.Genealogy.Part3"
    ], "Mathlib adoption in Genealogy changed; update the density claim"
    assert genealogy["carriers_per_theorem"] == RECORDED_GENESALYSIS_CARRIERS_PER_THEOREM
    assert len(genealogy["modules_importing_mathlib"]) == RECORDED_GENESALYSIS_MATHLIB_MODULES


def test_no_volume_may_claim_closure_while_targets_are_projections() -> None:
    rows = _volume_rows()
    ledger = _ledger_rows()
    general = [
        r["t_id"]
        for r in ledger
        if all(c["proof_grade"] == "GENERAL" for c in r["p_coverage"] if c["relation"] == "EXACT")
    ]
    for row in rows:
        if row["volume"] == "UNFILED":
            continue
        assert row["completion"] != "CLOSED", row["volume"]
        assert row["general_form_closed"] == 0 or row["volume"] in general
    assert not any(r["completion"] == "CLOSED" for r in rows)


def test_unfiled_targets_stay_visible() -> None:
    unfiled = next(r for r in _volume_rows() if r["volume"] == "UNFILED")
    assert unfiled["t_targets"] == RECORDED_UNFILED_TARGETS
    assert unfiled["completion"] == "UNFILED"
    assert "排卷回执" in unfiled["status_note"]
    v11 = next(r for r in _volume_rows() if r["volume"] == "V11")
    assert v11["completion"] == "EMPTY"
    assert v11["declared_increment"] == 7, "the receipt's V11 quota must stay recorded"


def test_volume_targets_are_disjoint_except_by_design() -> None:
    rows = {r["volume"]: r for r in _volume_rows() if r["volume"] != "UNFILED"}
    total = sum(r["t_targets"] for r in rows.values())
    assert total + next(r for r in _volume_rows() if r["volume"] == "UNFILED")["t_targets"] == 127


def test_paper_states_the_general_form_count() -> None:
    paper = PAPER_CN.read_text(encoding="utf-8")
    full = sum(
        1
        for r in _ledger_rows()
        if all(c["coverage"] == "FULL" for c in r["p_coverage"] if c["relation"] == "EXACT")
    )
    assert full == 0
    assert f"0/127" in paper or "一般式的闭合数是 0" in paper
