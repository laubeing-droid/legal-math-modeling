"""QA-01: paper-rewrite claim guard for the docs/paper-rewrite layout.

The legacy scripts/check_paper_claims.py is hard-wired to the old root/paper
layout and cannot run over docs/paper-rewrite; sections 1-3 relied on manual
scanning. This guard makes the discipline machine-checkable for the new
sections: forbidden phrasings absent, Chinese and English structurally
isomorphic (paragraph markers correspond), exactly one scope box per new
section, a claims table per section, monitored numbers in the new sections
bound to a subject SHA or run id on the same line, and Lean tactic names kept
out of the body text.
"""

from __future__ import annotations

import re
from pathlib import Path

CN = Path(__file__).resolve().parents[2] / "docs" / "paper-rewrite" / "paper_cn.md"
EN = Path(__file__).resolve().parents[2] / "docs" / "paper-rewrite" / "paper_en.md"

FORBIDDEN = (
    "85/94",
    "97 jobs",
    "91-module",
    "2993",
    "46/46 mutations killed",
    "score 1.0",
    "发布层 fail-closed",
)
MONITORED_INTS = {145, 27, 46, 91, 94, 97, 206, 452, 476, 2993}
HEX40 = re.compile(r"[0-9a-f]{40}")
RUN_ID = re.compile(r"\b\d{10,12}\b")  # GitHub Actions run ids used by this paper
TACTICS = ("rfl", "decide", "congrArg")
MARKER = re.compile(r"<!-- (S[4-9]-P\d{2}) -->")
SCOPE = re.compile(r"\[(S[4-9])-SCOPE\]")


def _new_sections(text: str) -> str:
    split = re.split(r"^## (?:第[四五六七八九]节|Section [4-9])\b.*$", text, flags=re.MULTILINE)
    return "".join(split[1:]) if len(split) > 1 else ""


def test_forbidden_phrasings_absent() -> None:
    for path in (CN, EN):
        text = path.read_text(encoding="utf-8")
        for token in FORBIDDEN:
            assert token not in text, f"{token!r} found in {path.name}"


def test_paragraph_markers_correspond_between_languages() -> None:
    cn_markers = MARKER.findall(CN.read_text(encoding="utf-8"))
    en_markers = MARKER.findall(EN.read_text(encoding="utf-8"))
    assert cn_markers == en_markers


CN_ORDINALS = {4: "四", 5: "五", 6: "六", 7: "七", 8: "八", 9: "九"}


def _section_splitter(n: int) -> str:
    return rf"^## (?:第{CN_ORDINALS[n]}节|Section {n})\b"


def test_exactly_one_scope_box_per_new_section() -> None:
    for path in (CN, EN):
        text = path.read_text(encoding="utf-8")
        for n in range(4, 10):
            section = re.split(_section_splitter(n), text, flags=re.MULTILINE)
            assert len(section) >= 2, f"section {n} missing in {path.name}"
            body = section[1].split("\n## ")[0]
            found = SCOPE.findall(body)
            assert found == [f"S{n}"], f"{path.name} section {n}: {found}"


def test_claims_table_rows_exist_per_section() -> None:
    for path in (CN, EN):
        text = path.read_text(encoding="utf-8")
        for n in range(4, 10):
            section = re.split(_section_splitter(n), text, flags=re.MULTILINE)[1].split(
                "\n## "
            )[0]
            assert re.search(rf"^\| S{n}-C\d", section, re.MULTILINE), (
                f"{path.name} section {n} lacks claims rows"
            )


def test_monitored_numbers_in_new_sections_carry_binding() -> None:
    for path in (CN, EN):
        body = _new_sections(path.read_text(encoding="utf-8"))
        for line in body.splitlines():
            numbers = {int(m) for m in re.findall(r"(?<![\w.])\d+(?![\w.])", line)}
            flagged = numbers & MONITORED_INTS
            if flagged:
                assert HEX40.search(line) or RUN_ID.search(line), (
                    f"{path.name}: monitored {flagged} without subject/run binding: {line[:80]}"
                )


def test_tactic_names_stay_out_of_new_section_body() -> None:
    for path in (CN, EN):
        body = _new_sections(path.read_text(encoding="utf-8"))
        stripped = re.sub(r"\|.*\|", "", body)  # tables may cite file names, not tactics
        for tactic in TACTICS:
            assert not re.search(rf"\b{tactic}\b", stripped), (
                f"{path.name}: tactic {tactic} leaked into body text"
            )
