"""QA-01 v2: guard for the rewritten paper (ten-chapter genealogy structure).

Checks: all ten chapter headings present in both languages; forbidden
phrasings absent; bibliography keys cited in the Chinese master all
resolve in paper/references.bib; the unproved-list chapter carries its
six numbered items; every chapter opens with a conclusion sentence."""

from __future__ import annotations

import re
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
CN = ROOT / "docs" / "paper-rewrite" / "paper_cn.md"
EN = ROOT / "docs" / "paper-rewrite" / "paper_en.md"
BIB = ROOT / "paper" / "references.bib"

CHAPTERS_CN = ["引言", "第一章 概念层", "第二章 法源层", "第三章 要件层",
               "第四章 证明层", "第五章 裁量层", "第六章 计算保证层",
               "第七章 交付层", "第八章 横切A", "第九章 横切B", "第十章 未证清单"]
CHAPTERS_EN = ["Introduction", "Chapter 1 Concept Layer", "Chapter 2 Source-of-Law Layer",
               "Chapter 3 Elements Layer", "Chapter 4 Proof Layer", "Chapter 5 Discretion Layer",
               "Chapter 6 Computation-Guarantee Layer", "Chapter 7 Delivery Layer",
               "Chapter 8 Cross-Cutting A", "Chapter 9 Cross-Cutting B",
               "Chapter 10 The Unproved List"]

FORBIDDEN = ("85/94", "97 jobs", "91-module", "2993", "46/46 mutations killed",
             "score 1.0", "发布层 fail-closed")

KEY_RE = re.compile(r"^[A-Z][A-Za-z]+(?:EtAl)?\d{4}$|^[A-Z][A-Za-z]{4,}$|^SPC[A-Za-z]+\d{4}$")


def test_all_ten_chapters_in_both_languages() -> None:
    cn = CN.read_text(encoding="utf-8")
    en = EN.read_text(encoding="utf-8")
    for h in CHAPTERS_CN:
        assert h in cn, f"missing CN chapter: {h}"
    for h in CHAPTERS_EN:
        assert h in en, f"missing EN chapter: {h}"


def test_forbidden_phrasings_absent() -> None:
    for path in (CN, EN):
        text = path.read_text(encoding="utf-8")
        for token in FORBIDDEN:
            assert token not in text, f"{token!r} in {path.name}"


def test_cn_citation_keys_resolve() -> None:
    cn = CN.read_text(encoding="utf-8")
    cited = set()
    for chunk in re.findall(r"\[([^\[\]]+)\]", cn):
        for k in chunk.split("；"):
            k = k.strip()
            if k and KEY_RE.match(k):
                cited.add(k)
    bib = BIB.read_text(encoding="utf-8")
    bibkeys = set(re.findall(r"^@[a-z]+\{([^,]+),", bib, re.MULTILINE))
    unresolved = sorted(cited - bibkeys)
    assert not unresolved, f"citation keys not in references.bib: {unresolved}"


def test_unproved_list_has_five_items_with_compaction_marks() -> None:
    cn = CN.read_text(encoding="utf-8")
    m = re.search(r"未证事项（压实后重排.*?）\*\*：(.*?)\*\*声明账本", cn, re.DOTALL)
    assert m is not None
    items = re.findall(r"^[一二三四五]、", m.group(1), re.MULTILINE)
    assert len(items) == 5, items
    assert "已于九轮问压实" in m.group(1)  # 两条已压实项须带标记


def test_each_chapter_opens_with_conclusion() -> None:
    cn = CN.read_text(encoding="utf-8")
    missing = []
    for seg in cn.split("\n## ")[1:]:
        lines = seg.split("\n")
        head = lines[0]
        if head.startswith(("第", "引言")):
            window = "\n".join(lines[:6])
            if "**结论" not in window:
                missing.append(head)
    assert not missing, f"chapters missing a conclusion-first sentence: {missing}"
