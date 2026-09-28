"""The `应为 N` anchors in the R-item table are commands, so they must equal their commands.

The close-out gate parses the 28-finding table; nothing parsed the R-item table beside it.
Its last column hands the reader a greppable check -- "should be 9", "should be 21" -- and
those figures were verified by hand once. A row that says the audit surface holds N named
targets for a module keeps reading true on the page after the module grows, which is the
numeric-drift class the audit kept returning to, so it gets a gate rather than a promise.

The second rule is the cheap version of the same idea: a row may not cite a Lean module
file that is no longer in the tree.
"""

from __future__ import annotations

import re
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
LEDGER = ROOT / "docs" / "master-plan" / "03_证明战役台账.md"

ROW = re.compile(r"^\|\s*R-[0-9]")
# `grep -c '^#print axioms JurisLean.Mandate.X' <file>`（应为 N）
ANCHOR = re.compile(
    r"`grep -c '(\^#print axioms [A-Za-z0-9_.]+)' ([^`]+)`（应为 (\d+)）"
)
MODULE_FILE = re.compile(r"Mandate/([A-Za-z0-9_]+)\.lean")


def _rows() -> list[str]:
    text = LEDGER.read_text(encoding="utf-8")
    return [line for line in text.splitlines() if ROW.match(line)]


def _live_count(pattern: str, rel_path: str) -> int:
    path = ROOT / rel_path
    assert path.exists(), f"anchor cites a missing file: {rel_path}"
    prefix = pattern.lstrip("^")
    return sum(1 for line in path.read_text(encoding="utf-8").splitlines() if line.startswith(prefix))


def test_the_anchor_rules_see_the_rows_they_claim() -> None:
    rows = _rows()
    assert len(rows) >= 10, f"only {len(rows)} R rows parsed; the table moved or vanished"
    assert len(ANCHOR.findall(LEDGER.read_text(encoding="utf-8"))) >= 3, (
        "no `应为 N` anchor is being parsed, so this gate checks nothing"
    )


def _stale_anchors(row: str) -> list[tuple[str, str, int]]:
    out = []
    for pattern, path, claimed in ANCHOR.findall(row):
        actual = _live_count(pattern, path.strip())
        if str(actual) != claimed:
            out.append((pattern, claimed, actual))
    return out


def test_every_expected_count_anchor_matches_the_live_grep() -> None:
    stale = [s for row in _rows() for s in _stale_anchors(row)]
    assert not stale, f"anchor claims a count the command no longer gives: {stale}"


def test_every_module_named_in_a_row_still_exists_as_a_source_file() -> None:
    missing = sorted({
        name for row in _rows() for name in MODULE_FILE.findall(row)
        if not (ROOT / "proofs" / "lean" / "juris_lean" / "JurisLean" / "Mandate" / f"{name}.lean").exists()
    })
    assert not missing, f"rows cite Mandate modules that are not in the tree: {missing}"


def test_a_wrong_anchor_figure_would_actually_go_red() -> None:
    """Prove the comparison is live: the same row with a sabotaged figure must be stale."""
    text = LEDGER.read_text(encoding="utf-8")
    found = ANCHOR.search(text)
    assert found, "no anchor to mutate, so this gate checks nothing"
    pattern, path, claimed = found.groups()
    live = _live_count(pattern, path.strip())
    assert str(live) == claimed
    sabotaged = found.group(0).replace(f"（应为 {claimed}）", f"（应为 {live + 7}）")
    assert _stale_anchors(sabotaged), "the anchor rule did not notice a figure I changed by hand"
