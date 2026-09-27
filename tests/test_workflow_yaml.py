"""Workflows must be parseable, and a quoted `run:` scalar must not carry comments.

Run 36295032321 did not fail a build step: it failed to start. Nothing ran, so there
was no job, no log, and the only symptom was a red X on a commit whose 465 local
gates were green. Cause: the step's `run:` was a YAML single-quoted scalar, and the
lines added to it contained `grep -c '^#print axioms'`. Inside a quoted scalar the
apostrophe closes the value, and because such a scalar *folds* its lines into one
shell command, a `#` comment line would also have swallowed every command after it.

The repository already paid for the folding half of this once (the `python-gates`
step was converted for exactly that reason), so the rule is now checked rather than
remembered.
"""

from __future__ import annotations

import re
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parents[1]
WORKFLOWS = sorted((ROOT / ".github" / "workflows").glob("*.yml"))

RUN_KEY = re.compile(r"^(\s*)run:\s*(.*)$")


def quoted_run_scalars(text: str) -> list[tuple[int, list[str]]]:
    """(line number, body lines) for every `run: '...'` that continues over lines."""

    found: list[tuple[int, list[str]]] = []
    lines = text.splitlines()
    for i, line in enumerate(lines):
        m = RUN_KEY.match(line)
        if not m:
            continue
        value = m.group(2).strip()
        if not value.startswith("'") or value.endswith("'") and value != "'":
            continue
        indent = len(m.group(1))
        body: list[str] = []
        for j in range(i + 1, len(lines)):
            following = lines[j]
            if following.strip() == "'":
                break
            if following.strip() and (
                len(following) - len(following.lstrip()) <= indent
            ):
                break
            body.append(following)
        if body:
            found.append((i + 1, body))
    return found


def comment_lines_inside_quoted_runs(text: str) -> list[int]:
    """Quoted scalars fold their lines into one command, so a `#` line kills the rest.

    Only this is held against the existing steps: apostrophes inside a quoted scalar
    are YAML's problem to reject, and `yaml.safe_load` covers that separately.
    """
    return [
        lineno
        for lineno, body in quoted_run_scalars(text)
        if any(b.strip().startswith("#") for b in body)
    ]


def test_workflows_exist():
    assert WORKFLOWS, "no workflow files found"


@pytest.mark.parametrize("path", WORKFLOWS, ids=lambda p: p.name)
def test_quoted_run_blocks_carry_no_comment_lines(path: Path):
    offenders = comment_lines_inside_quoted_runs(path.read_text(encoding="utf-8"))
    assert not offenders, (
        f"{path.name}: `run:` at line(s) {offenders} is a quoted scalar containing a "
        "# comment line; YAML folds the lines into a single command, so the comment "
        "swallows every command after it. Use `run: |-`."
    )


@pytest.mark.parametrize("path", WORKFLOWS, ids=lambda p: p.name)
def test_workflow_is_valid_yaml(path: Path):
    yaml = pytest.importorskip("yaml")
    doc = yaml.safe_load(path.read_text(encoding="utf-8"))
    assert isinstance(doc, dict) and "jobs" in doc


def test_the_scan_actually_bites(tmp_path):
    """A fixture with the real defect must be reported, or the gate is decoration."""
    quote = chr(39)
    bad_lines = [
        "jobs:",
        "  x:",
        "    steps:",
        "      - name: t",
        "        run: " + quote + "set -e",
        "",
        "          # explain something",
        "          grep -c x f",
        "          " + quote,
    ]
    bad = tmp_path / "bad.yml"
    bad.write_text("\n".join(bad_lines) + "\n", encoding="utf-8")
    text = bad.read_text(encoding="utf-8")
    assert comment_lines_inside_quoted_runs(text) == [5]
    assert quoted_run_scalars(text)[0][1], "the scanner saw no body lines"

    good_lines = [
        "jobs:",
        "  x:",
        "    steps:",
        "      - name: t",
        "        run: |-",
        "          set -e",
        "          # explain something",
        "          grep -c " + quote + "^#print axioms" + quote + " f",
    ]
    good = tmp_path / "good.yml"
    good.write_text("\n".join(good_lines) + "\n", encoding="utf-8")
    assert comment_lines_inside_quoted_runs(good.read_text(encoding="utf-8")) == []
    assert quoted_run_scalars(good.read_text(encoding="utf-8")) == []


def test_the_axiom_log_gate_is_still_wired_in():
    text = (ROOT / ".github" / "workflows" / "lean-build.yml").read_text(encoding="utf-8")
    assert "check_axiom_audit_log.py --log axiom-audit.raw.txt --check" in text
    assert "AUDIT_TARGETS=$(grep -c" in text
