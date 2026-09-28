"""Counts written into the 28-finding table must come with a route that recomputes them.

`tests/spec/test_ledger_closeout_citations.py` already parses that table: it checks the 28
rows exist, are unique, bucket the way the ledger claims, and each cites an evidence item
that exists in the suite. What it does not ask is whether a *number* written into the
mechanism or evidence cell still describes anything. A row asserting "232 files scanned"
keeps reading true after the tool starts reporting 236, and silent numeric drift inside an
account of findings is the same defect class the audit's P0-1 was about.

So this module checks one thing, in the cells the other gate leaves open: a row may state a
figure of three digits or more in its mechanism or evidence cells only if that same row
names how to recompute it -- a script, a `--check` mode, an artifact path, an attesting CI
run, or words saying the figure floats. The finding cell is exempt because there the table
quotes the auditor's original wording, including claims this repository later voided.
"""

from __future__ import annotations

import re
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
LEDGER = ROOT / "docs" / "master-plan" / "03_证明战役台账.md"

TABLE_HEAD = "### 28 条发现逐条对账"
EXEMPT_MARKERS = (".py", "--check", "run ", "docs/", "现算", "浮动", "勘误", "作废", "认定")
BARE_FIGURE = re.compile(r"(?<![:.\w-])(\d{3,})(?!\w)")
ROW = re.compile(r"^\|\s*P[0-3]-")


def _rows(text: str) -> list[str]:
    start = text.index(TABLE_HEAD)
    end = text.index("\n### ", start + len(TABLE_HEAD) + 1)
    return [line for line in text[start:end].splitlines() if ROW.match(line)]


def _offenders(rows: list[str]) -> list[tuple[str, str]]:
    """Figures stranded in a live cell of a row that offers no way to recompute them."""
    out: list[tuple[str, str]] = []
    for row in rows:
        if any(marker in row for marker in EXEMPT_MARKERS):
            continue
        for cell in row.split("|")[3:]:
            for match in BARE_FIGURE.finditer(cell):
                out.append((match.group(1), cell.strip()[:60]))
    return out


def test_the_table_this_rule_reads_is_the_one_it_claims() -> None:
    """A rule that silently parses zero rows is a rule that always passes."""
    rows = _rows(LEDGER.read_text(encoding="utf-8"))
    assert len(rows) == 28, (
        f"this rule sees {len(rows)} findings; the close-out gate pins the table at 28, so "
        "a different count here means the rule stopped covering the table it describes"
    )


def test_the_rule_fires_on_a_stranded_figure_and_not_on_a_routed_one() -> None:
    """Prove the check can go red, and that the exemption is a route rather than an escape."""
    stranded = "| P9-99 sample | conclusion | mechanism holds 236 of them | evidence cell |"
    routed = "| P9-99 sample | conclusion | mechanism holds 236 of them | `tool.py --check` |"
    quoted_only = "| P9-99 sample | the auditor counted 433 of them | mechanism | evidence |"

    assert _offenders([stranded]), "a bare figure in the mechanism cell slipped through"
    assert not _offenders([routed]), "a row that names its recompute route was flagged"
    assert not _offenders([quoted_only]), (
        "the finding cell quotes the auditor and must stay exempt, or the table cannot "
        "record a voided claim with its original number"
    )


def test_no_live_cell_carries_a_figure_without_a_recompute_route() -> None:
    offenders = _offenders(_rows(LEDGER.read_text(encoding="utf-8")))
    assert not offenders, (
        f"figure quoted in a mechanism or evidence cell with no way to recompute it: {offenders}"
    )
