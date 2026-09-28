"""The 28-finding reconciliation table must keep pointing at things that exist.

The audit's P0-1 class was an account that contradicted the source it described, and the
mechanism chosen for it was to generate the account from the source. This table is hand
written -- it maps each of the 28 findings to the mechanism and the gate that keeps it from
recurring -- so it cannot be generated. What it can do is fail loudly the moment a row
names a gate that no longer exists, which is how a hand written account actually rots: the
test is renamed, the row keeps pointing at it, and a later reader audits against nothing.

The row count is pinned too. Dropping a finding from this table would silently reduce the
scope of the audit that produced it.

Counts inside the rows are deliberately not checked: AGENTS forbids treating a count as a
timeless fact, and the rows that carry one say so and name the command that recomputes it.
"""

from __future__ import annotations

import re
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
LEDGER = ROOT / "docs" / "master-plan" / "03_证明战役台账.md"

FINDING_ROW = re.compile(r"^\|\s*(P[0-3]-[0-9]+)[^\n]*\|\s*$", re.M)
BACKTICKED = re.compile(r"`([^`]+)`")
EXPECTED_FINDINGS = 28


def _rows(text: str | None = None) -> list[str]:
    if text is None:
        text = LEDGER.read_text(encoding="utf-8")
    start = text.index("### 28 条发现逐条对账")
    end = text.index("\n### ", start + 10)
    return [l for l in text[start:end].splitlines() if re.match(r"\|\s*P[0-3]-", l)]


def test_the_findings_table_has_every_row_it_claims() -> None:
    rows = _rows()
    assert len(rows) == EXPECTED_FINDINGS, (
        f"the table holds {len(rows)} findings; the audit that produced it counted "
        f"{EXPECTED_FINDINGS} -- a row must not be dropped, only closed"
    )
    ids = [re.match(r"\|\s*(P[0-3]-[0-9]+)", r).group(1) for r in rows]
    assert len(set(ids)) == len(ids), "a finding id appears twice"


def test_dropping_a_row_would_actually_go_red() -> None:
    """A pin nobody can break is decoration, so break it on a copy of the table."""
    text = LEDGER.read_text(encoding="utf-8")
    mutated = text.replace(_rows()[-1], "", 1)
    assert len(_rows(mutated)) == EXPECTED_FINDINGS - 1, (
        "the parser does not see rows, so the row-count pin can never fail"
    )
    assert len(_rows()) == EXPECTED_FINDINGS


def test_every_gate_named_in_the_table_still_exists() -> None:
    """A row pointing at a renamed test audits nothing, so the row must fail instead."""
    known_tests: set[str] = set()
    proc = subprocess.run(
        ["git", "grep", "-ho", r"def \(test_[A-Za-z0-9_]*\)"],
        capture_output=True, text=True, encoding="utf-8", cwd=ROOT,
    )
    assert proc.returncode == 0, proc.stderr
    for line in proc.stdout.splitlines():
        known_tests.add(line.replace("def ", ""))

    py_names = {p.name for p in ROOT.rglob("*.py") if ".lake" not in p.parts}
    missing: list[str] = []
    for row in _rows():
        for token in BACKTICKED.findall(row):
            tok = token.strip()
            if re.fullmatch(r"test_[A-Za-z0-9_]*", tok):
                if tok not in known_tests:
                    missing.append(tok)
            elif tok.endswith(".py"):
                if Path(tok).name not in py_names:
                    missing.append(tok)
    assert not missing, f"findings rows name gates that no longer exist: {sorted(missing)}"


def test_rows_that_quote_a_count_name_the_route_that_recomputes_it() -> None:
    """A bare number in the mechanism or evidence cell is the drift class this table is for.

    The finding cell is exempt: it quotes what the auditor counted, and a voided claim stays
    voided with its original wording. A row is exempt when it names a script, a `--check`
    mode, an artifact path, an attesting run, or says outright that the figure floats.
    """
    exempt_markers = (".py", "--check", "run ", "docs/", "现算", "浮动", "勘误", "作废", "认定")
    offenders = []
    for row in _rows():
        cells = row.split("|")
        if any(m in row for m in exempt_markers):
            continue
        for cell in cells[3:]:
            for m in re.finditer(r"(?<![:\.\w-])(\d{3,})(?![\w])", cell):
                offenders.append((m.group(1), cell.strip()[:60]))
    assert not offenders, f"count with no recompute route in a live cell: {offenders}"
