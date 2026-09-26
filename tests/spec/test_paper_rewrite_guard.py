"""QA-01 v3: guard for the rewritten paper (ten-chapter genealogy structure).

v2 checked a hand-written list of stale numeric phrases ("85/94", "97 jobs",
"2993") and nothing else, so a fresh over-claim could pass it. Qoder audit
P2-24 named exactly this gap: the register the repository says it enforces
(`docs/formal-release/FORBIDDEN_CLAIMS.md`) was never linked to the gate, which
is how "全部经持续集成权威验证，无一条 sorry" reached the abstract.

v3 links them: every bullet in the register must carry at least one literal
paper-side signal phrase that this test blocks, and any numeric theorem claim
must be bound to a commit, a CI run id, or the inventory artifact on its own
line (ALLOWED_CLAIMS.md: qualifiers are part of the claim, not caveats).

Checks kept from v2: ten chapter headings in both languages, legacy stale
figures absent, CN citation keys resolvable, unproved-list shape,
conclusion-first opening per chapter.
"""

from __future__ import annotations

import json
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
CN = ROOT / "docs" / "paper-rewrite" / "paper_cn.md"
EN = ROOT / "docs" / "paper-rewrite" / "paper_en.md"
BIB = ROOT / "paper" / "references.bib"
REGISTER = ROOT / "docs" / "formal-release" / "FORBIDDEN_CLAIMS.md"

CHAPTERS_CN = ["引言", "第一章 概念层", "第二章 法源层", "第三章 要件层",
               "第四章 证明层", "第五章 裁量层", "第六章 计算保证层",
               "第七章 交付层", "第八章 横切A", "第九章 横切B", "第十章 未证清单"]
CHAPTERS_EN = ["Introduction", "Chapter 1 Concept Layer", "Chapter 2 Source-of-Law Layer",
               "Chapter 3 Elements Layer", "Chapter 4 Proof Layer", "Chapter 5 Discretion Layer",
               "Chapter 6 Computation-Guarantee Layer", "Chapter 7 Delivery Layer",
               "Chapter 8 Cross-Cutting A", "Chapter 9 Cross-Cutting B",
               "Chapter 10 The Unproved List"]

LEGACY_STALE = ("85/94", "97 jobs", "91-module", "2993", "46/46 mutations killed",
                "score 1.0", "发布层 fail-closed")

# One entry per bullet of FORBIDDEN_CLAIMS.md, in file order. Each lists literal
# phrasings that would assert that bullet's forbidden thing in either paper.
CLAIM_SIGNALS: tuple[tuple[str, tuple[str, ...]], ...] = (
    ("entire juris-calculus verified", ("整部 juris-calculus 已", "整个系统已完备验证")),
    ("python generally refinement-proved", ("Python 已全量精化证明", "实现已全量精化证明")),
    ("three fixtures prove all cases", ("三条夹具证明全部", "三条夹具证明所有")),
    ("green workflow suffices alone",
     ("全部经持续集成权威验证", "all verified by the CI authority", "CI 绿即证明正确")),
    ("count or audit proves legal correctness",
     ("定理数证明", "公理审计证明实体法", "计数即证明")),
    ("horn-to-AAF globally complete", ("Horn→AAF 全局完备", "不遗漏任何边")),
    ("traces universally sound", ("生产证明迹普遍可靠", "普遍可靠的独立检查器")),
    ("incremental equals full", ("增量式与全量重算恒等", "增量等于全量")),
    ("banach/privacy/calibration established",
     ("Banach 完备性已闭合", "隐私已确立", "38 个常数已标定")),
    ("later commits certified", ("后续提交自动继承", "继承该 PASS")),
    ("artifacts are a permanent archive", ("CI 工件永久存档", "工件即永久证据")),
)

# A numeric theorem claim is only allowed with a binding on the same line.
COUNT_RE = re.compile(r"一千七百\d十[一二三四五六七八九]?|\b1[7-9]\d{2}\b|\b1[0-9]{3} 条定理")
BINDING_RE = re.compile(r"\b[0-9a-f]{7,40}\b|\b3\d{10}\b|theorem_inventory_v3\.json")
# Words that make a bare carrier count read as a proved proposition.
OVERCLAIM_ON_COUNT = ("无一条 sorry", "zero sorry", "全部经持续集成权威验证")

KEY_RE = re.compile(r"^[A-Z][A-Za-z]+(?:EtAl)?\d{4}$|^[A-Z][A-Za-z]{4,}$|^SPC[A-Za-z]+\d{4}$")


def _papers() -> list[Path]:
    return [CN, EN]


def _register_bullets() -> list[str]:
    text = REGISTER.read_text(encoding="utf-8")
    return [
        line[2:].strip()
        for line in text.splitlines()
        if line.startswith("- ")
    ]


def test_register_and_signals_stay_one_to_one() -> None:
    """Adding a forbidden claim without a paper-side signal fails loudly."""
    bullets = _register_bullets()
    assert len(bullets) == len(CLAIM_SIGNALS), (
        f"register has {len(bullets)} bullets, gate covers {len(CLAIM_SIGNALS)}; "
        "give the new bullet a paper-side signal or drop it deliberately"
    )


def test_forbidden_claim_signals_absent() -> None:
    texts = {p.name: p.read_text(encoding="utf-8") for p in _papers()}
    for _label, phrases in CLAIM_SIGNALS:
        for phrase in phrases:
            for name, text in texts.items():
                assert phrase not in text, f"{phrase!r} in {name} violates the register"


def test_legacy_stale_figures_absent() -> None:
    for path in _papers():
        text = path.read_text(encoding="utf-8")
        for token in LEGACY_STALE:
            assert token not in text, f"{token!r} in {path.name}"


def test_numeric_theorem_claims_are_bound() -> None:
    for path in _papers():
        for lineno, line in enumerate(path.read_text(encoding="utf-8").splitlines(), 1):
            if not COUNT_RE.search(line):
                continue
            assert BINDING_RE.search(line), (
                f"{path.name}:{lineno} states a theorem count with no commit, CI run "
                f"id, or inventory artifact on the same line: {line[:90]!r}"
            )


def test_no_bare_ci_or_sorry_promise() -> None:
    """The audit's P0-3 class: a count advertised as CI-verified/sorry-free."""
    for path in _papers():
        text = path.read_text(encoding="utf-8")
        for phrase in OVERCLAIM_ON_COUNT:
            assert phrase not in text, f"{phrase!r} in {path.name}"


def test_all_ten_chapters_in_both_languages() -> None:
    cn = CN.read_text(encoding="utf-8")
    en = EN.read_text(encoding="utf-8")
    for h in CHAPTERS_CN:
        assert h in cn, f"missing CN chapter: {h}"
    for h in CHAPTERS_EN:
        assert h in en, f"missing EN chapter: {h}"


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
    m = re.search(r"未证事项（[^）]*）\*\*：(.*?)\*\*声明账本", cn, re.DOTALL)
    assert m is not None
    items = re.findall(r"^[一二三四五]、", m.group(1), re.MULTILINE)
    assert len(items) == 5, items
    assert re.search(r"已(于|经).{0,12}压实", m.group(1)), "closed items must carry a compaction mark"


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


def test_markdown_bold_is_balanced_per_line() -> None:
    """P3-21: chapter 10 shipped an unterminated `**结论…` plus a stray brace."""
    for path in _papers():
        for lineno, line in enumerate(path.read_text(encoding="utf-8").splitlines(), 1):
            assert line.count("**") % 2 == 0, f"{path.name}:{lineno} unbalanced ** markup"
            assert "。}" not in line, f"{path.name}:{lineno} stray '}}' inside prose"


def test_no_placeholder_closing() -> None:
    for path in _papers():
        text = path.read_text(encoding="utf-8")
        assert "此致\n readers" not in text, f"{path.name} still ends on a placeholder addressee"


INVENTORY = ROOT / "docs" / "formal-release" / "theorem_inventory_v3.json"


def _counts() -> dict:
    import json

    doc = json.loads(INVENTORY.read_text(encoding="utf-8"))
    pkg = doc["scope_summary"]["juris_lean_package"]
    allc = doc["scope_summary"]["all_tracked_lean"]
    return {
        "pkg_theorems": pkg["theorem_count"],
        "all_theorems": allc["theorem_count"],
        "pkg_files": pkg["file_count"],
        "audit_targets": pkg["print_axioms_distinct_targets"],
        "audit_cmds": pkg["print_axioms_command_count"],
    }


def test_paper_counts_equal_the_artifact() -> None:
    """The audit's count-drift class, closed structurally.

    A branch that adds modules moves the inventory; if the paper is not
    regenerated in the same commit, the paper now lies about its own artifact.
    Every number the papers quote is compared digit-for-digit against
    theorem_inventory_v3.json, so the two cannot diverge in a commit.
    """
    c = _counts()
    cn = CN.read_text(encoding="utf-8")
    en = EN.read_text(encoding="utf-8")
    assert f"`juris_lean_package` {c['pkg_theorems']} 条定理声明" in cn
    assert f"`all_tracked_lean` {c['all_theorems']} 条" in cn
    assert f"{c['audit_targets']} 个具名目标" in cn
    assert f"{c['audit_cmds']} 行" in cn
    assert f"{c['pkg_theorems']} theorem declarations in scope `juris_lean_package`" in en
    assert f"{c['all_theorems']} in scope `all_tracked_lean`" in en
    assert f"{c['audit_targets']} named targets" in en
    assert f"{c['audit_cmds']} `#print axioms` commands" in en


def test_papers_use_plain_digits_not_numeral_phrases() -> None:
    """Chinese numeral counts cannot be machine-checked, so they are not allowed."""
    for path in (CN, EN):
        text = path.read_text(encoding="utf-8")
        assert "一千七百" not in text, f"{path.name} states a count in numerals"
        assert not re.search(r"1,\d{3}", text), f"{path.name} uses a thousands comma"


LEDGER = ROOT / "theory" / "spec" / "lh_alignment" / "t_p_coverage.jsonl"


def _ledger_derived() -> dict:
    import collections

    rows = [json.loads(l) for l in LEDGER.read_text(encoding="utf-8").splitlines() if l.strip()]
    exact = [c for r in rows for c in r["p_coverage"] if c["relation"] == "EXACT"]
    grades = collections.Counter(c["proof_grade"] for c in exact)
    return {
        "rows": len(rows),
        "carriers": len({c["theorem"] for c in exact}),
        "general": grades["GENERAL"],
        "projection": grades["DEF_PROJECTION"],
        "witness": grades["WITNESS"],
        "full": sum(
            1
            for r in rows
            if all(c["coverage"] == "FULL" for c in r["p_coverage"] if c["relation"] == "EXACT")
        ),
    }


def test_paper_T_spectrum_numbers_equal_the_ledger() -> None:
    """Same drift rule for the strength split the papers advertise."""
    d = _ledger_derived()
    cn = CN.read_text(encoding="utf-8")
    assert f"{d['carriers']} 条定理给满 {d['rows']} 个 T 位" in cn
    assert (
        f"GENERAL {d['general']} / DEF_PROJECTION {d['projection']} / WITNESS {d['witness']}" in cn
    )
    assert f"{d['full']}/{d['rows']}" in cn


def test_ledger_gate_and_paper_agree_on_full_count() -> None:
    d = _ledger_derived()
    assert d["rows"] == 127
    assert d["full"] == 0, "a T target reached general form; update the claim deliberately"
