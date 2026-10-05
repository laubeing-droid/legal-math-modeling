"""Gate tests for the one-paper-one-artifact-one-count gate (round-2 F6).

The rejection path is the point: synthetic drafts carrying two different
theorem counts against the same artifact MUST go red.
"""

from __future__ import annotations

import importlib.util
import json
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
TOOL = ROOT / "scripts" / "ci" / "check_paper_single_count.py"
ARTIFACT = ROOT / "docs" / "formal-release" / "theorem_inventory_v3.json"

_spec = importlib.util.spec_from_file_location("check_paper_single_count", TOOL)
gate = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(gate)

ALLOWED = gate.allowed_counts(ARTIFACT)


def _fake_artifact(tmp_path: Path, theorem_count: int = 3617, decl_count: int = 3751) -> Path:
    doc = {
        "scope_summary": {
            "juris_lean_package": {
                "theorem_count": theorem_count,
                "counted_declaration_count": decl_count,
            },
            "all_tracked_lean": {
                "theorem_count": theorem_count + 12,
                "counted_declaration_count": decl_count + 12,
            },
        }
    }
    path = tmp_path / "inventory.json"
    path.write_text(json.dumps(doc), encoding="utf-8")
    return path


def test_gate_script_exists_and_allowed_set_is_artifact_derived() -> None:
    assert TOOL.exists()
    assert ALLOWED, "allowed set must be recomputed from the artifact"
    summary = json.loads(ARTIFACT.read_text(encoding="utf-8"))["scope_summary"]
    assert summary["juris_lean_package"]["theorem_count"] in ALLOWED
    assert summary["all_tracked_lean"]["theorem_count"] in ALLOWED


def test_gate_is_wired_through_the_ci_pytest_job() -> None:
    workflow = (ROOT / ".github" / "workflows" / "lean-build.yml").read_text(encoding="utf-8")
    assert "pytest" in workflow
    assert Path(__file__).parent.name == "tests"


def test_both_paper_drafts_match_the_current_artifact() -> None:
    hits = gate.find_violations()
    assert hits == [], f"stale counts in drafts: {[(h[0].name, h[1], h[3]) for h in hits[:5]]}"


def test_rejection_path_fires_on_two_counts_one_artifact(tmp_path: Path) -> None:
    """The B6 shape: 3240 in one sentence, the artifact's 3617 in another."""
    artifact = _fake_artifact(tmp_path)
    draft = tmp_path / "paper.md"
    draft.write_text(
        "全仓 3240 条定理声明，绑定同一清单工件。另一处又写 3617 条定理。",
        encoding="utf-8",
    )
    hits = gate.find_violations((draft,), artifact)
    assert len(hits) == 1 and hits[0][3] == 3240


def test_rejection_path_fires_on_sha256_only_number(tmp_path: Path) -> None:
    artifact = _fake_artifact(tmp_path)
    draft = tmp_path / "paper.md"
    draft.write_text("定理声明共 3252 条（清单工件）。", encoding="utf-8")
    hits = gate.find_violations((draft,), artifact)
    assert len(hits) == 1 and hits[0][3] == 3252


def test_artifact_values_pass_and_years_are_ignored(tmp_path: Path) -> None:
    artifact = _fake_artifact(tmp_path)
    draft = tmp_path / "paper.md"
    draft.write_text(
        "2026 年重算：定理声明 3617 条，计入声明总数 3751；另一作用域 3629 条定理。",
        encoding="utf-8",
    )
    assert gate.find_violations((draft,), artifact) == []


def test_cli_is_fail_closed(tmp_path: Path) -> None:
    artifact = _fake_artifact(tmp_path)
    draft = tmp_path / "paper.md"
    draft.write_text("定理声明 3240 条。", encoding="utf-8")
    proc = subprocess.run(
        [sys.executable, str(TOOL), str(draft), str(artifact)],
        capture_output=True,
        text=True,
    )
    assert proc.returncode == 1, proc.stdout + proc.stderr
    assert "3240" in proc.stdout
