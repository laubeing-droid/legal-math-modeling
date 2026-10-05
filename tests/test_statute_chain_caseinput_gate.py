"""Gate tests for the statuteChain_on × case-input sentence gate (round-2 F3).

The gate's value is its rejection path, so half of these tests construct
sentences that MUST go red and assert they do; the wiring test pins the CI
channel (the python-gates job runs this very file).
"""

from __future__ import annotations

import importlib.util
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
TOOL = ROOT / "scripts" / "ci" / "check_statute_chain_caseinput_claim.py"

_spec = importlib.util.spec_from_file_location("check_statute_chain_caseinput_claim", TOOL)
gate = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(gate)


def test_gate_script_exists_and_exposes_the_scanner() -> None:
    assert TOOL.exists(), "gate script missing from scripts/ci/"
    assert callable(gate.find_violations)
    assert callable(gate.find_violations_in_text)


def test_gate_is_wired_through_the_ci_pytest_job() -> None:
    """The wiring channel: lean-build.yml's python-gates job runs this tests/ tree."""
    workflow = (ROOT / ".github" / "workflows" / "lean-build.yml").read_text(encoding="utf-8")
    assert "pytest" in workflow
    assert Path(__file__).parent.name == "tests"


def test_committed_docs_tree_is_clean() -> None:
    hits = gate.find_violations(ROOT / "docs")
    assert hits == [], f"gate fired on committed docs: {hits[:3]}"


def test_rejection_path_fires_on_case_juan_sentence() -> None:
    bad = "一个脱敏样例案卷端到端跑通 `statuteChain_on`。"
    hits = gate.find_violations_in_text(bad)
    assert len(hits) == 1 and hits[0][0] == 1


def test_rejection_path_fires_on_caseinput_token() -> None:
    bad = "CaseInput 的输出经 hornOfCase 直接喂给 statuteChain_on。"
    assert gate.find_violations_in_text(bad), "CaseInput coupling must go red"


def test_substring_variant_still_fires() -> None:
    bad = "案卷数据跑在 statuteChain_on_instanceM 上。"
    assert gate.find_violations_in_text(bad), "substring variant must go red"


def test_separate_sentences_are_allowed() -> None:
    ok = "`statuteChain_on` 只挂在手写 `instanceM` 上。案卷输入层全仓无下游消费者。"
    assert gate.find_violations_in_text(ok) == []


def test_cli_is_fail_closed(tmp_path: Path) -> None:
    (tmp_path / "bad.md").write_text("案卷跑通 statuteChain_on。", encoding="utf-8")
    proc = subprocess.run(
        [sys.executable, str(TOOL), str(tmp_path)],
        capture_output=True,
        text=True,
    )
    assert proc.returncode == 1, proc.stdout + proc.stderr
    assert "FAIL" in proc.stdout


def test_cli_passes_on_clean_tree(tmp_path: Path) -> None:
    (tmp_path / "ok.md").write_text("`statuteChain_on` 是链谓词。案卷层另说。", encoding="utf-8")
    proc = subprocess.run(
        [sys.executable, str(TOOL), str(tmp_path)],
        capture_output=True,
        text=True,
    )
    assert proc.returncode == 0, proc.stdout + proc.stderr
