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


def test_runs_the_papers_rely_on_are_recheckable_here() -> None:
    """A run the papers cite must resolve to a commit this repository contains.

    Whether some *older* document's run head is still reachable is a property of the
    machine doing the check, not of the evidence, so the index stores no such flag --
    it used to, and CI correctly complained that the stored answer disagreed with the
    checker. Reachability is recomputed here, and only demanded of the papers.
    """

    paper_runs = [
        r for r in _doc()["runs"] if any("paper-rewrite" in loc for loc in r["quoted_by"])
    ]
    assert paper_runs, "no run is quoted by the papers any more; this gate needs re-reading"
    for r in paper_runs:
        proc = subprocess.run(
            ["git", "cat-file", "-e", f"{r['head_sha']}^{{commit}}"], cwd=ROOT, capture_output=True
        )
        assert proc.returncode == 0, (
            f"run {r['run_id']} is cited by the papers but its subject commit is not here"
        )


def test_index_stores_no_machine_relative_facts() -> None:
    for r in _doc()["runs"]:
        assert "head_commit_present" not in r, (
            "a presence flag cannot be a fact about a run: it depends on who checks"
        )


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
