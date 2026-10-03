"""The gap register must copy each module's gap *section*, not whatever prose last said so.

`generate_uncovered_fragment_register.py` reads each wave module's own closing section, and on
2026-10-03 a doc comment that merely mentioned the marker ("...并补本件 §未覆盖第 4 项...") sat
below the real section and won, so the register reported a numeric-bridge doc as StatuteChain's
list of gaps. These two tests keep both halves honest: the extractor prefers a heading, and the
live file still resolves to the section a reader would call the gap list.
"""

from __future__ import annotations

import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "scripts" / "ci"))

import generate_uncovered_fragment_register as register  # noqa: E402


def test_a_prose_mention_below_the_section_does_not_win(tmp_path: Path) -> None:
    path = tmp_path / "Widget.lean"
    path.write_text(
        "/-! ## 二、未覆盖片段（本件没有表达什么）\n"
        "1. 缺一条区间桥。\n"
        "2. 缺一条时点逆解析。\n"
        "-/\n"
        "/-- 小工具（并补本件 §未覆盖片段第 1 项）：说明为什么需要它。 -/\n"
        "def widget : Nat := 0\n",
        encoding="utf-8",
    )
    head, line, body = register.extract(path)
    assert "## 二、未覆盖片段" in head, f"the extractor anchored on: {head[:60]!r}"
    # The quote runs to the next declaration, so the bridge doc below the list is carried
    # along with it; what must not happen is anchoring *on* that doc.
    assert body[:2] == ["1. 缺一条区间桥。", "2. 缺一条时点逆解析。"], body
    assert path.read_text(encoding="utf-8").splitlines()[line - 1] == head


def test_the_live_statute_chain_entry_is_the_gap_section_not_a_bridge_doc() -> None:
    path = register.SEAMS / "StatuteChain.lean"
    head, _line, body = register.extract(path)
    assert "##" in head and register.MARKER in head, head[:80]
    assert len(body) >= 10, (
        f"the register would quote only {len(body)} lines of a 13-item gap list"
    )
