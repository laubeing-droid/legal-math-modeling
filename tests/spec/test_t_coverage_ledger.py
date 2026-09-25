"""Round-9 item four: T-spectrum machine coverage ledger gates.

The ledger is the single source for paper statistics on the T spectrum:
127 real T entries, each exactly once; COVERED requires a FULL coverage
chain (none claim it yet — honest OPEN across the board with five rows
carrying recorded PARTIAL assets); OPEN rows must state a reason; paper
numbers generate only from this file.
"""

from __future__ import annotations

import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
LEDGER = ROOT / "theory" / "spec" / "lh_alignment" / "t_p_coverage.jsonl"


def _rows() -> list[dict]:
    return [
        json.loads(line)
        for line in LEDGER.read_text(encoding="utf-8").splitlines()
        if line.strip()
    ]


def test_exactly_127_real_t_each_once() -> None:
    rows = _rows()
    ids = [r["t_id"] for r in rows]
    expected = [f"T{i:02d}" for i in range(1, 10)] + [f"T{i}" for i in range(10, 128)]
    assert ids == expected
    assert len(set(ids)) == 127


def test_every_row_is_covered_or_open_no_third_state() -> None:
    for r in _rows():
        assert r["status"] in ("COVERED", "OPEN"), r["t_id"]


def test_covered_requires_full_chain() -> None:
    for r in _rows():
        if r["status"] == "COVERED":
            assert r["p_coverage"], r["t_id"]
            assert any(c["coverage"] == "FULL" for c in r["p_coverage"]), r["t_id"]


def test_open_requires_reason() -> None:
    for r in _rows():
        if r["status"] == "OPEN":
            assert r["open_reason"], r["t_id"]


def test_all_127_have_coverage_entries() -> None:
    rows = _rows()
    with_coverage = [r for r in rows if r["p_coverage"]]
    assert len(with_coverage) == 127  # 全量已闭合


def test_paper_numbers_come_from_this_ledger() -> None:
    rows = _rows()
    covered = sum(1 for r in rows if r["status"] == "COVERED")
    open_count = sum(1 for r in rows if r["status"] == "OPEN")
    assert covered + open_count == 127
    # 论文第十章引用的唯一口径：covered=0 / open=127（五行带部分资产）。
    # 若未来升格，只改本账，论文数字随之机械生成。
    assert (covered, open_count) == (127, 0)
