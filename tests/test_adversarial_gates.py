"""Adversarial pins from the third-track test of the 62-module promotion wave.

Two gates were found silent under attack and fixed in scripts/ci/; these tests
keep them closed:

* a name in ``_EXTERNAL_ROOT_PROMOTED`` that matches no file on disk used to be
  swallowed whole -- ``--write`` then silently dropped the real module from the
  release root (it falls back into auto-quarantine) and every later check stayed
  green. The promotion table is now validated like the quarantine table.
* ``ci_run_index.md`` was never read by ``--check``: changing a run id digit in
  the table left the gate green while the table told a reader something else.
  The committed markdown must now be the byte-exact render of its JSON.

The quarantine design itself is pinned too, so nobody "simplifies" it away: an
unbooked arrival under ``External/`` is auto-quarantined (check passes, module
stays out of the root) and importing a quarantined module from the release root
trips the bypass alarm.
"""

from __future__ import annotations

import importlib.util
import json
import shutil
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
REACH_TOOL = ROOT / "scripts" / "ci" / "check_import_reachability.py"
INDEX_TOOL = ROOT / "scripts" / "ci" / "build_ci_run_index.py"
LEAN_BASE = ROOT / "proofs" / "lean" / "juris_lean"
PKG = LEAN_BASE / "JurisLean"
ROOT_MODULE = LEAN_BASE / "JurisLean.lean"
INDEX_JSON = ROOT / "docs" / "formal-release" / "ci_run_index.json"
INDEX_MD = ROOT / "docs" / "formal-release" / "ci_run_index.md"

# The one External module no other module imports: only the root block reaches
# it, so demoting it is invisible to every sibling-import defense.
SOLE_EXTERNAL_LEAF = "JurisLean.External.FixedPointTheorems"


def make_tree(tmp_path: Path) -> Path:
    """A full-fidelity copy of the package tree plus the reachability script."""
    base = tmp_path / "proofs" / "lean" / "juris_lean"
    base.mkdir(parents=True)
    shutil.copytree(PKG, base / "JurisLean")
    shutil.copyfile(ROOT_MODULE, base / "JurisLean.lean")
    tool = tmp_path / "scripts" / "ci" / "check_import_reachability.py"
    tool.parent.mkdir(parents=True)
    shutil.copyfile(REACH_TOOL, tool)
    return tmp_path


def run_reach(tree: Path, *extra: str) -> subprocess.CompletedProcess:
    return subprocess.run(
        [sys.executable, "scripts/ci/check_import_reachability.py", *extra],
        cwd=tree, capture_output=True, text=True, encoding="utf-8",
    )


def edit_script(tree: Path, old: str, new: str) -> None:
    tool = tree / "scripts" / "ci" / "check_import_reachability.py"
    text = tool.read_text(encoding="utf-8")
    assert old in text, f"script copy no longer contains {old!r}"
    tool.write_text(text.replace(old, new, 1), encoding="utf-8")


def test_ghost_promoted_name_fails_check_and_write_without_writing(tmp_path) -> None:
    tree = make_tree(tmp_path)
    edit_script(tree, "_EXTERNAL_ROOT_PROMOTED: set[str] = {\n",
                '_EXTERNAL_ROOT_PROMOTED: set[str] = {\n'
                '    "JurisLean.External.GameTheory.Math.GhostModule",\n')
    root = tree / "proofs/lean/juris_lean/JurisLean.lean"
    aggregator = tree / "proofs/lean/juris_lean/JurisLean/FullMath/All.lean"
    root_before, agg_before = root.read_bytes(), aggregator.read_bytes()

    for extra in ([], ["--write"]):
        proc = run_reach(tree, *extra)
        assert proc.returncode == 1, proc.stdout + proc.stderr
        assert "GhostModule" in proc.stderr, proc.stderr

    # Fail-closed: the refused --write must not have written anything either.
    assert root.read_bytes() == root_before, "--write damaged the root module before failing"
    assert aggregator.read_bytes() == agg_before, "--write damaged the aggregator before failing"


def test_typoed_promotion_of_a_real_leaf_is_refused_before_the_silent_demotion(tmp_path) -> None:
    """One wrong letter used to quietly kick the module out of the release root."""
    tree = make_tree(tmp_path)
    edit_script(tree, f'"{SOLE_EXTERNAL_LEAF}",', f'"{SOLE_EXTERNAL_LEAF[:-1]}z",')
    proc = run_reach(tree)
    assert proc.returncode == 1, proc.stdout + proc.stderr
    assert f"{SOLE_EXTERNAL_LEAF[:-1]}z" in proc.stderr, proc.stderr
    assert run_reach(tree, "--write").returncode == 1


def test_unbooked_external_arrival_is_quarantined_and_cannot_sneak_into_the_root(tmp_path) -> None:
    tree = make_tree(tmp_path)
    rogue = tree / "proofs/lean/juris_lean/JurisLean/External/GameTheory/Math/Rogue.lean"
    rogue.write_text("-- rogue arrival, no bookkeeping\n"
                     "import JurisLean.External.GameTheory.Math.Probability\n",
                     encoding="utf-8")

    proc = run_reach(tree)
    assert proc.returncode == 0, proc.stdout + proc.stderr  # auto-quarantine is the design

    root = tree / "proofs/lean/juris_lean/JurisLean.lean"
    text = root.read_text(encoding="utf-8")
    root.write_text(text.replace(
        "import JurisLean.External.GameTheory.Math.Probability\n",
        "import JurisLean.External.GameTheory.Math.Probability\n"
        "import JurisLean.External.GameTheory.Math.Rogue\n"), encoding="utf-8")
    proc = run_reach(tree)
    assert proc.returncode == 1, proc.stdout + proc.stderr
    assert "quarantined module(s) reached" in proc.stderr, proc.stderr
    assert "Rogue" in proc.stderr


def test_unbooked_non_external_arrival_fails_as_unreachable(tmp_path) -> None:
    tree = make_tree(tmp_path)
    rogue = tree / "proofs/lean/juris_lean/JurisLean/RogueOutside.lean"
    rogue.write_text("-- rogue arrival outside External\nimport JurisLean.Basic\n",
                     encoding="utf-8")
    proc = run_reach(tree)
    assert proc.returncode == 1, proc.stdout + proc.stderr
    assert "unreachable" in proc.stderr and "RogueOutside" in proc.stderr, proc.stderr


def test_deleted_root_import_of_the_sole_external_leaf_fails(tmp_path) -> None:
    tree = make_tree(tmp_path)
    root = tree / "proofs/lean/juris_lean/JurisLean.lean"
    text = root.read_text(encoding="utf-8")
    assert f"import {SOLE_EXTERNAL_LEAF}\n" in text
    root.write_text(text.replace(f"import {SOLE_EXTERNAL_LEAF}\n", ""), encoding="utf-8")
    proc = run_reach(tree)
    assert proc.returncode == 1, proc.stdout + proc.stderr
    assert SOLE_EXTERNAL_LEAF in proc.stderr, proc.stderr


def _load_index_tool():
    spec = importlib.util.spec_from_file_location("bri_gate", INDEX_TOOL)
    bri = importlib.util.module_from_spec(spec)
    assert spec and spec.loader
    spec.loader.exec_module(bri)
    return bri


def test_committed_markdown_index_is_the_byte_exact_render_of_its_json() -> None:
    bri = _load_index_tool()
    doc = json.loads(INDEX_JSON.read_text(encoding="utf-8"))
    assert INDEX_MD.read_text(encoding="utf-8") == bri.render_markdown(doc), (
        "ci_run_index.md drifted from ci_run_index.json: regenerate with "
        "python scripts/ci/build_ci_run_index.py"
    )


def test_check_mode_rejects_a_tampered_markdown_index(tmp_path) -> None:
    """--check used to validate only the JSON; a tampered table passed untouched."""
    run_ids = ["33946211096", "33946211721"]
    notes = tmp_path / "notes"
    notes.mkdir()
    for n, rid in enumerate(run_ids):
        (notes / f"quote{n}.md").write_text(f"run {rid} was green, see it.\n", encoding="utf-8")

    def record(rid: str, line: int) -> dict:
        return {
            "run_id": int(rid), "quoted_by": [f"notes/quote{line}.md:1"],
            "workflow": "w", "name": "n", "head_sha": "0" * 40, "head_branch": "b",
            "event": "push", "status": "completed", "conclusion": "success",
            "created_at": "c", "updated_at": "u",
            "html_url": f"https://x/{rid}", "jobs_total": 1, "started": True,
            "jobs": [{"name": "j", "status": "completed", "conclusion": "success"}],
            "artifacts_total": 0, "evidence": None,
        }

    doc = {"schema_version": "ci-run-index-v1", "status": "s", "authority_note": "a",
           "repository": "r", "verify_command": "v", "quote_scan": "q",
           "runs": [record(rid, n) for n, rid in enumerate(run_ids)]}
    docs = tmp_path / "docs" / "formal-release"
    docs.mkdir(parents=True)
    (docs / "ci_run_index.json").write_text(
        json.dumps(doc, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    rendered = _load_index_tool().render_markdown(doc)
    (docs / "ci_run_index.md").write_text(rendered, encoding="utf-8")
    (docs / "ci-evidence").mkdir()  # no digests.json: the evidence loop must skip

    # The tool resolves its ROOT from its own path, so a copy under tmp_path is
    # what makes it read the scratch index; the quote scan needs a git index.
    tool = tmp_path / "scripts" / "ci" / "build_ci_run_index.py"
    tool.parent.mkdir(parents=True)
    shutil.copyfile(INDEX_TOOL, tool)
    assert subprocess.run(["git", "init", "-q", "."], cwd=tmp_path,
                          capture_output=True).returncode == 0
    assert subprocess.run(["git", "add", "-A", "-f"], cwd=tmp_path,
                          capture_output=True).returncode == 0

    def check() -> subprocess.CompletedProcess:
        return subprocess.run(
            [sys.executable, "scripts/ci/build_ci_run_index.py", "--check"],
            cwd=tmp_path, capture_output=True, text=True, encoding="utf-8",
        )

    proc = check()
    assert proc.returncode == 0, proc.stdout + proc.stderr  # the clean pair passes

    tampered = rendered.replace(run_ids[0], "93946211096", 1)
    assert tampered != rendered
    (docs / "ci_run_index.md").write_text(tampered, encoding="utf-8")
    proc = check()
    assert proc.returncode == 1, proc.stdout + proc.stderr
    assert "stale markdown index" in proc.stderr, proc.stderr
