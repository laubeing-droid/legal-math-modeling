"""P2-26: CI run ids quoted in the repository must carry in-repo evidence.

Before this gate the markdown named a batch of GitHub Actions runs as proof of build
and axiom-audit status while nothing in the repository said what those runs were,
so a third party could only check the claim by having `gh` credentials of their
own. `scripts/ci/build_ci_run_index.py` now snapshots each run's subject commit,
branch, trigger, conclusion, per-job conclusions and artifact count next to the
file:line that quotes it; these tests keep that account honest without touching
the network.
"""

from __future__ import annotations

import copy
import importlib.util
import json
import re
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
TOOL = ROOT / "scripts" / "ci" / "build_ci_run_index.py"
INDEX = ROOT / "docs" / "formal-release" / "ci_run_index.json"

_spec = importlib.util.spec_from_file_location("build_ci_run_index", TOOL)
build_ci_run_index = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(build_ci_run_index)

GREEN_TOKENS = ("全绿", "全部通过", "权威验证", "success", "all green", "green")
RED_TOKENS = ("fail", "失败", "红", "cancel", "未通过", "error", "错", "超时")
# A green word only attaches to the run named just before it; a transition arrow,
# a sentence end, or another commit/run mention starts a new subject. The list
# separator "、" deliberately does NOT: a job enumeration ends in "全部 success".
SEGMENT_END = re.compile(r"[。；;]|→|\b\d{11}\b|\b[0-9a-f]{7}\b")


def _attached_window(line: str, after: int) -> str:
    m = SEGMENT_END.search(line, after)
    return line[after : m.start() if m else len(line)]


def _doc() -> dict:
    return json.loads(INDEX.read_text(encoding="utf-8"))


def _line(loc: str) -> str:
    rel, n = loc.rsplit(":", 1)
    return (ROOT / rel).read_text(encoding="utf-8").splitlines()[int(n) - 1]


def _context(loc: str, below: int = 2) -> str:
    """The quoted line plus what immediately follows it — how the passage reads."""

    rel, n = loc.rsplit(":", 1)
    lines = (ROOT / rel).read_text(encoding="utf-8").splitlines()
    start = int(n) - 1
    return "\n".join(lines[start : start + 1 + below])


def test_every_quoted_run_id_is_in_the_index() -> None:
    quoted = build_ci_run_index.run_ids_in_markdown()
    recorded = {str(r["run_id"]) for r in _doc()["runs"]}
    assert set(quoted) <= recorded, f"runs quoted without evidence: {sorted(set(quoted) - recorded)}"
    assert recorded <= set(quoted), f"index records nothing quotes: {sorted(recorded - set(quoted))}"


def test_citations_in_the_index_are_real_locations() -> None:
    """The index may not invent the quotes it says it checked."""

    for r in _doc()["runs"]:
        assert r["quoted_by"], r["run_id"]
        for loc in r["quoted_by"]:
            assert str(r["run_id"]) in _line(loc), f"{r['run_id']} claims {loc}, which does not name it"


def test_each_run_record_is_complete() -> None:
    for r in _doc()["runs"]:
        assert re.fullmatch(r"[0-9a-f]{40}", r["head_sha"] or ""), r["run_id"]
        assert r["conclusion"], r["run_id"]
        assert r["jobs"], f"run {r['run_id']} recorded with no jobs"
        assert all(j["name"] for j in r["jobs"]), r["run_id"]
        assert isinstance(r["artifacts_total"], int), r["run_id"]


def test_head_commits_of_quoted_runs_exist_in_this_repository() -> None:
    """Actions metadata becomes evidence only when it lands on a commit we have."""

    for r in _doc()["runs"]:
        proc = subprocess.run(
            ["git", "cat-file", "-e", f"{r['head_sha']}^{{commit}}"],
            cwd=ROOT, capture_output=True,
        )
        assert proc.returncode == 0, f"run {r['run_id']} head {r['head_sha']} not in repo"


def _calls_run_green(line: str, run_id: str) -> bool:
    """Does this line attach a green word to this run id?"""

    for m in re.finditer(run_id, line):
        window = _attached_window(line, m.end()).lower()
        if any(t in window for t in GREEN_TOKENS):
            return True
    return False


def test_a_quoted_line_may_not_call_a_non_success_run_green() -> None:
    """Adjacent praise for a red run is the defect this index exists to catch.

    The passage, not the single line: the sentence that names a run can end mid
    thought and call its jobs success on the next line.
    """

    bad = [
        f"{loc}: {_context(loc)[:160]!r}"
        for r in _doc()["runs"] if r["conclusion"] != "success"
        for loc in r["quoted_by"]
        if _calls_run_green(_context(loc), str(r["run_id"]))
    ]
    assert not bad, "non-success runs quoted as green:\n" + "\n".join(bad)


def test_green_adjacency_rule_actually_bites() -> None:
    """The rule must catch a real over-claim and spare the honest phrasing."""

    assert _calls_run_green("- run 34512426708 全绿，公理零依赖", "34512426708")
    assert _calls_run_green("- run 34512426708 (**success** at bd364c5)", "34512426708")
    # The shape this repository actually contained: the run id named, then the jobs
    # called success two lines down while the run itself concluded cancelled.
    assert _calls_run_green(
        "- Lean 权威管线 run **34519379252**（attempt 2）：lean-full-clean-build\n"
        "  加 Axiom audit）、release-certificate、final-gate、\n"
        "  lean-module-build(BusinessRelations) 全部 success。\n",
        "34519379252",
    )
    # The honest rewrite: the run-level conclusion is named in the same clause.
    assert not _calls_run_green(
        "- Lean 权威管线 run **34519379252**（attempt 2；此 run 的 run 级结论为\n"
        "  cancelled——下方点名的 Delta 作业超时被取消）：lean-full-clean-build\n"
        "  加 Axiom audit）、release-certificate、final-gate、python-gates、\n"
        "  lean-module-build(BusinessRelationsAudit) 全部 success。\n",
        "34519379252",
    )
    assert not _calls_run_green(
        "- 收敛轨迹：34512426708（7af4e7e，11 错）→ 88644bc 全绿。", "34512426708"
    )
    assert not _calls_run_green("- run 34512426708 结论 failure", "34512426708")


def test_red_runs_are_also_named_as_red_somewhere() -> None:
    """Every non-success run must have at least one honest location."""

    for r in _doc()["runs"]:
        if r["conclusion"] == "success":
            continue
        lines = " ".join(_context(loc).lower() for loc in r["quoted_by"])
        assert any(t in lines for t in RED_TOKENS), (
            f"run {r['run_id']} concluded {r['conclusion']} but no quote says so "
            "in its own passage"
        )


def test_the_audited_subjects_own_runs_are_recorded() -> None:
    """The green and the red at the audited commit must both be on file."""

    by_id = {str(r["run_id"]): r for r in _doc()["runs"]}
    assert by_id["36259479766"]["conclusion"] == "success"
    assert by_id["36259479766"]["head_sha"].startswith("b57d4aa")
    assert by_id["36258179200"]["conclusion"] == "failure"
    assert by_id["36258179200"]["head_sha"].startswith("1488685")


def test_index_labels_itself_as_metadata_not_certificate() -> None:
    doc = _doc()
    assert doc["schema_version"] == "ci-run-index-v1"
    assert doc["status"] == "external_actions_metadata_snapshot_not_release_certificate"
    assert "does not certify any theorem" in doc["authority_note"]


def test_check_mode_is_offline_and_passes() -> None:
    proc = subprocess.run(
        [sys.executable, str(TOOL), "--check"], cwd=ROOT,
        capture_output=True, text=True, encoding="utf-8",
    )
    assert proc.returncode == 0, proc.stdout + proc.stderr


def test_check_mode_rejects_a_dropped_record(tmp_path) -> None:
    doc = _doc()
    assert len(doc["runs"]) >= 2
    tampered = copy.deepcopy(doc)
    drop = str(tampered["runs"][0]["run_id"])
    tampered["runs"] = tampered["runs"][1:]
    path = tmp_path / "tampered.json"
    path.write_text(json.dumps(tampered), encoding="utf-8")
    proc = subprocess.run(
        [sys.executable, str(TOOL), "--check", "--index", str(path)], cwd=ROOT,
        capture_output=True, text=True, encoding="utf-8",
    )
    assert proc.returncode == 1
    assert drop in proc.stderr
