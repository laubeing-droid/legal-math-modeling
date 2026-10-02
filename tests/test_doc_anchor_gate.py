"""Doc anchors must resolve: a cited location in the construction docs is a claim.

The delivery notes and the binding table quote theorem locations. Every one of those
was checked when written, and a single mid-file insertion still invalidated 36 of them
at once, because line numbers are not stable facts -- they are coordinates into a file
that keeps growing.

The gate used to recognise one shape, `` `name:LINE` ``, and to skip an unrecognised name
in silence. Both halves of that mattered: the table shape `` `name` | `:LINE` `` drifted by
264 lines while the gate printed "anchors current", and a theorem name that exists nowhere
in the Lean tree could be listed as delivered with a green check. These tests pin the four
shapes the gate now reads, the exemption table that replaces the silence, and the boundary
of what `--fix` is allowed to touch.
"""

import subprocess
import sys
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parents[1]
SCRIPT = ROOT / "scripts" / "ci" / "check_doc_anchors.py"
sys.path.insert(0, str(SCRIPT.parent))
import check_doc_anchors as GATES  # noqa: E402

CARRIER = "proofs/lean/juris_lean/JurisLean/Seams/BoundaryClosure.lean"


def facts():
    """Read the coordinates the fixtures cite out of source, so tests cannot stale out."""

    lines = (ROOT / CARRIER).read_text(encoding="utf-8").splitlines()
    name = "joinTaint_eq_tainted_iff"
    declared = [i for i, text in enumerate(lines, 1) if text.startswith(f"theorem {name}")]
    blank = next(i for i, text in enumerate(lines, 1) if not text.strip())
    assert len(declared) == 1, f"fixture wants one {name}, found {declared}"
    return {"name": name, "line": declared[0], "blank": blank, "count": len(lines)}


def run(tmp_path, body: str, *extra: str) -> subprocess.CompletedProcess:
    doc = tmp_path / "cite.md"
    doc.write_text(body, encoding="utf-8")
    return subprocess.run(
        [sys.executable, str(SCRIPT), "--doc", str(doc), *extra],
        cwd=ROOT, capture_output=True, text=True, encoding="utf-8", errors="replace",
    )


def test_the_construction_docs_anchor_gate_passes():
    proc = subprocess.run(
        [sys.executable, str(SCRIPT)], cwd=ROOT, capture_output=True, text=True,
        encoding="utf-8", errors="replace",
    )
    assert proc.returncode == 0, proc.stdout + proc.stderr
    assert "stale anchors" not in proc.stdout


def test_the_gate_actually_reads_source_lines(tmp_path):
    """Shape 1: `name:LINE` -- a wrong line must be rejected, not nodded through."""

    real = facts()["line"]
    bad = run(tmp_path, "see `joinTaint_eq_tainted_iff:1`\n")
    assert bad.returncode == 1, bad.stdout + bad.stderr
    assert "joinTaint_eq_tainted_iff:1" in bad.stdout
    assert f"{real}" in bad.stdout, "the report must show where the source really is"

    good = run(tmp_path, f"see `joinTaint_eq_tainted_iff:{real}`\n")
    assert good.returncode == 0, good.stdout + good.stderr


def test_table_shape_binds_a_lone_line_number_to_the_name_before_it(tmp_path):
    """Shape 2a: `name` | `:LINE`, the shape the old regex never saw."""

    f = facts()
    good = run(tmp_path, f"| `{f['name']}` | `:{f['line']}` | note |\n")
    assert good.returncode == 0, good.stdout + good.stderr

    bad = run(tmp_path, f"| `{f['name']}` | `:1` | note |\n")
    assert bad.returncode == 1, bad.stdout + bad.stderr
    assert f"{f['name']}:1" in bad.stdout
    assert f"{f['line']}" in bad.stdout


def test_line_then_name_shape_uses_the_trailing_name_as_its_subject(tmp_path):
    """Shape 2b: `:LINE name` -- the name lives on that line."""

    f = facts()
    good = run(tmp_path, f"清单：`:{f['line']} {f['name']}`、\n")
    assert good.returncode == 0, good.stdout + good.stderr

    bad = run(tmp_path, f"清单：`:1 {f['name']}`、\n")
    assert bad.returncode == 1, bad.stdout + bad.stderr
    assert f"{f['name']}:1" in bad.stdout


def test_file_anchor_must_land_on_a_real_nonblank_line(tmp_path):
    """Shape 3: `file.lean:LINE` -- existence and a live line, not a declaration line."""

    f = facts()
    good = run(tmp_path, f"见 `BoundaryClosure.lean:{f['line']}`。\n")
    assert good.returncode == 0, good.stdout + good.stderr

    onto_blank = run(tmp_path, f"见 `BoundaryClosure.lean:{f['blank']}`。\n")
    assert onto_blank.returncode == 1, onto_blank.stdout + onto_blank.stderr
    assert "blank" in onto_blank.stdout or "misses" in onto_blank.stdout

    past_end = run(tmp_path, f"见 `BoundaryClosure.lean:{f['count'] + 40}`。\n")
    assert past_end.returncode == 1, past_end.stdout + past_end.stderr


def test_file_anchor_that_names_a_resident_must_name_the_right_line(tmp_path):
    """Shape 3b: `file:LINE resident` -- the resident is the thing under the number."""

    f = facts()
    good = run(tmp_path, f"`BoundaryClosure.lean:{f['line']} {f['name']}`\n")
    assert good.returncode == 0, good.stdout + good.stderr

    bad = run(tmp_path, "`BoundaryClosure.lean:1 " + f["name"] + "`\n")
    assert bad.returncode == 1, bad.stdout + bad.stderr
    assert "file anchor misses" in bad.stdout
    assert f"{f['line']}" in bad.stdout, "the report must say where the resident sits"


def test_missing_file_anchor_is_red_not_skipped(tmp_path):
    """A file that does not exist cannot be nodded through as 'not a declaration name'."""

    bad = run(tmp_path, "见 `docs/history/no_such_carrier_at_all.md:12`。\n")
    assert bad.returncode == 1, bad.stdout + bad.stderr
    assert "no_such_carrier_at_all.md:12" in bad.stdout


def test_volume_and_line_reference_is_checked_when_the_volume_exists(tmp_path):
    """`09:209` names a volume of the plan; a timestamp must not be read as one."""

    good = run(tmp_path, "读数见 `09:1`，另有 `18:41` 的时钟读数不是引用。\n")
    assert good.returncode == 0, good.stdout + good.stderr

    bad = run(tmp_path, "读数见 `09:99999999`。\n")
    assert bad.returncode == 1, bad.stdout + bad.stderr
    assert "09:99999999" in bad.stdout


def test_bare_name_cited_beside_real_declarations_must_exist(tmp_path):
    """Shape 4: the headline defect -- a name with no green check behind it.

    `applicability_matches_source_semantics` is listed as a delivered S1 theorem beside one
    that is real, while the same document admits the name appears nowhere in the tree.
    """

    f = facts()
    ghost = run(tmp_path, f"契约要求：`{f['name']}`、`applicability_matches_source_semantics`\n")
    assert ghost.returncode == 1, ghost.stdout + ghost.stderr
    assert "applicability_matches_source_semantics" in ghost.stdout

    real_pair = run(tmp_path, f"契约要求：`{f['name']}`、`carriesTaint_iff_taintOfInputs_tainted`\n")
    assert real_pair.returncode == 0, real_pair.stdout + real_pair.stderr


def test_bare_name_in_prose_is_not_demanded_to_be_a_declaration(tmp_path):
    """A cell that cites no declarations at all must not be policed for names."""

    doc = tmp_path / "cite.md"
    body = "状态：`UNKNOWN`，工件 `axiom-audit.json`，运行 `36770138720` 于 `c03663cb`\n"
    proc = run(tmp_path, body)
    assert proc.returncode == 0, proc.stdout + proc.stderr
    assert doc.read_text(encoding="utf-8") == body, "the gate must not rewrite a check run"


def test_exemptions_are_listed_with_a_reason(tmp_path):
    """Silence was the bug: an excuse is allowed only as a written decision."""

    assert GATES.EXEMPT, "the exemption table must exist"
    for name, reason in GATES.EXEMPT.items():
        assert isinstance(reason, str) and len(reason) >= 12, f"{name} has no real reason"
    # A listed name still has to be a name the gate cannot resolve, or the entry is dead.
    index = GATES.build_index()
    dead = [n for n in GATES.EXEMPT if GATES.resolve_token(n, index).kind != "unknown"]
    assert not dead, f"exemption entries that already resolve are dead weight: {dead}"


def test_unbound_coordinate_is_reported_but_does_not_fail(tmp_path):
    """A line number the doc never attached to a file is a gap to name, not a drift to guess."""

    proc = run(tmp_path, "台账靶（`:78`）。\n")
    assert proc.returncode == 0, proc.stdout + proc.stderr
    assert "unbound" in proc.stdout


def test_historical_readings_are_not_treated_as_anchors(tmp_path):
    """`225->294` and `audited_targets=1949` are numbers of their moment; leave them alone."""

    body = "读数 `225→294`，`audited_targets=1949`，2966 jobs，`287 of 296 modules, 11 allowed`\n"
    proc = run(tmp_path, body)
    assert proc.returncode == 0, proc.stdout + proc.stderr


def test_fix_rewrites_only_an_unambiguous_declaration_anchor(tmp_path):
    """--fix may move a number, never a file, and never where two lines could be meant."""

    f = facts()
    other = "carriesTaint_iff_taintOfInputs_tainted"
    other_line = next(
        i for i, text in enumerate(
            (ROOT / CARRIER).read_text(encoding="utf-8").splitlines(), 1
        ) if text.startswith(f"theorem {other}")
    )
    doc = tmp_path / "cite.md"
    body = (
        f"| `{f['name']}` | `:1` | stale, one file, one line |\n"
        f"| `{other}` | `:1` | stale too |\n"
        f"range `BoundaryClosure.lean:1-3` stays\n"
        f"file token `LegalModelV2.lean:999999` stays\n"
    )
    doc.write_text(body, encoding="utf-8")
    proc = subprocess.run(
        [sys.executable, str(SCRIPT), "--doc", str(doc), "--fix"],
        cwd=ROOT, capture_output=True, text=True, encoding="utf-8", errors="replace",
    )
    assert proc.returncode == 0, proc.stdout + proc.stderr
    fixed = doc.read_text(encoding="utf-8")
    assert f"| `{f['name']}` | `:{f['line']}` |" in fixed
    assert f"| `{other}` | `:{other_line}` |" in fixed
    assert "range `BoundaryClosure.lean:1-3` stays" in fixed, "a range is not a declaration line"
    assert "file token `LegalModelV2.lean:999999` stays" in fixed, "no resident, no repair"
    # Only digits move.
    import re
    assert re.sub(r"\d+", "#", fixed) == re.sub(r"\d+", "#", body)


def test_the_gate_reports_where_it_refuses_to_repair(tmp_path):
    """Refusing is a result too: an anchor with two candidate homes must be shown, not fixed."""

    index = GATES.build_index()
    multi = [n for n, sites in index.decl.items() if len({f for f, _ in sites}) > 1]
    assert multi, "fixture needs a name declared in more than one file"
    name = sorted(multi)[0]
    proc = run(tmp_path, f"see `{name}:1`\n")
    assert proc.returncode == 1, proc.stdout + proc.stderr
    assert f"{name}:1" in proc.stdout
    fix_run = subprocess.run(
        [sys.executable, str(SCRIPT), "--doc", str(tmp_path / "cite.md"), "--fix"],
        cwd=ROOT, capture_output=True, text=True, encoding="utf-8", errors="replace",
    )
    assert "0 anchors rewritten" in fix_run.stdout, fix_run.stdout
