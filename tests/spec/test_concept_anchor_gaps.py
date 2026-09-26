"""Gates for concept-level anchor honesty (audit Q1, D8, P2-15, P2-17, P3-20).

`theory/spec/p_registry.json` is the live concept ledger: 132 entries, each with
file+symbol anchors. Its anchors all resolve, which is why the audit could only
find the softer disease: a third of the concepts are carried by Python and
pytest alone, and three concepts the frozen genealogy marks ✅ (defined there as
"已证（Lean 定理）") have no Lean anchor at all.

These gates freeze the observed sets so the gap cannot widen silently, and force
any narrowing to come from real Lean anchors rather than from re-worded prose.
"""

from __future__ import annotations

import json
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
REGISTRY = ROOT / "theory" / "spec" / "p_registry.json"
GENEALOGY = ROOT / "docs" / "master-plan" / "基线" / "法律概念总谱.md"

# Concepts whose only anchors are Python modules or pytest files.
CONTRACT_ONLY_CONCEPTS = frozenset({
    "P-007", "P-008", "P-013", "P-016", "P-025", "P-032", "P-037", "P-039", "P-044",
    "P-045", "P-046", "P-059", "P-067", "P-069", "P-071", "P-072", "P-075", "P-076",
    "P-077", "P-088", "P-090", "P-101", "P-108", "P-109", "P-110", "P-111", "P-112",
    "P-113", "P-115", "P-116", "P-118", "P-123",
})

# Concepts the frozen genealogy marks ✅ = "已证（Lean 定理）" while the live
# registry gives them no Lean anchor. Reasons must name the real situation.
PROVEN_TIER_WITHOUT_LEAN_ANCHOR = {
    "P-013": "期日计算：registry 只锚 theory/spec/temporal_applicability.py；"
             "总谱 ✅ 档要求 Lean 定理，需补挂真实日历/期间定理或降档",
    "P-044": "证明责任：registry 只锚 theory/burden_of_proof_tracker.py；"
             "FullMath/Burden/ 下确有定理但未挂为 P-044 锚",
    "P-069": "法律后果形态：registry 只锚 theory/spec/canonical_v2/kernel.py::transfer",
}

# Tier marks as counted row-by-row out of the frozen table.
RECORDED_TIERS = {"✅": 27, "📦": 62, "📋": 39, "❓": 4}
RECORDED_BUCKET_COUNTS = {
    "L0 概念层桶": 10, "贯穿桶": 3, "L1 法源层桶": 12, "L2 问题与要件层桶": 13,
    "L3 证明与责任层桶": 14, "L4 论证与裁量层桶": 38, "(L5) 计算与保证层桶": 13,
    "L6 交付与工作台层桶": 4, "横切A 经验校准桶": 11, "横切B 回执与压制桶": 14,
}


def _entries() -> list[dict]:
    return json.loads(REGISTRY.read_text(encoding="utf-8"))["entries"]


def _genealogy_rows() -> list[tuple[str, str]]:
    rows = []
    for line in GENEALOGY.read_text(encoding="utf-8").splitlines():
        if not line.startswith("| P-") or "| P 号 |" in line:
            continue
        pid = line.split("|")[1].strip()
        mark = next((m for m in ("✅", "📦", "📋", "❓") if m in line), "")
        rows.append((pid, mark))
    return rows


def test_registry_shape_and_anchor_resolution() -> None:
    entries = _entries()
    assert len(entries) == 132
    assert [e["id"] for e in entries] == [f"P-{i:03d}" for i in range(1, 133)]
    for e in entries:
        assert e["anchors"], e["id"]
        for a in e["anchors"]:
            path = ROOT / a["file"]
            assert path.exists(), f"{e['id']}: anchor file missing: {a['file']}"
            if a.get("symbol"):
                text = path.read_text(encoding="utf-8", errors="replace")
                assert re.search(r"\b" + re.escape(a["symbol"]) + r"\b", text), (
                    f"{e['id']}: anchor symbol {a['symbol']!r} not found in {a['file']}"
                )


def test_contract_only_set_is_exactly_as_recorded() -> None:
    """32 of 132 concepts have no Lean carrier. It must not grow silently."""
    actual = frozenset(
        e["id"] for e in _entries()
        if not any(a["file"].endswith(".lean") for a in e["anchors"])
    )
    assert actual == CONTRACT_ONLY_CONCEPTS, (
        f"added without a Lean anchor: {sorted(actual - CONTRACT_ONLY_CONCEPTS)}; "
        f"newly covered: {sorted(CONTRACT_ONLY_CONCEPTS - actual)}"
    )


def test_proven_tier_concepts_declare_their_anchor_gap() -> None:
    marks = dict(_genealogy_rows())
    proven = {pid for pid, m in marks.items() if m == "✅"}
    with_lean = {
        e["id"] for e in _entries() if any(a["file"].endswith(".lean") for a in e["anchors"])
    }
    gap = proven - with_lean
    assert gap == set(PROVEN_TIER_WITHOUT_LEAN_ANCHOR), (
        f"✅ concepts without a Lean anchor changed: {sorted(gap)}; "
        "either attach a real Lean anchor or downgrade the tier mark through the "
        "genealogy change procedure"
    )
    for reason in PROVEN_TIER_WITHOUT_LEAN_ANCHOR.values():
        assert len(reason) > 20


def test_frozen_genealogy_tier_arithmetic_is_self_consistent() -> None:
    """P2-17: the self-audit section used to state 61/40 while the table says 62/39."""
    from collections import Counter

    counts = Counter(mark for _pid, mark in _genealogy_rows())
    assert dict(counts) == RECORDED_TIERS
    assert sum(counts.values()) == 132
    text = GENEALOGY.read_text(encoding="utf-8")
    for tier, n in RECORDED_TIERS.items():
        assert f"{tier} {n}" in text or f"{tier}{n}" in text, (
            f"tier total for {tier} must be stated once and match the table ({n})"
        )


def test_bucket_headers_match_row_counts() -> None:
    """P3-20: the L3 header claimed 13 items while the table held 14 rows."""
    text = GENEALOGY.read_text(encoding="utf-8").splitlines()
    seen = {}
    current = None
    for line in text:
        m = re.match(r"^### (.+?)（(P-\d+)\.\.(P-\d+)，(\d+) 项）", line)
        if m:
            current = m.group(1)
            seen[current] = [int(m.group(4)), 0, m.group(2), m.group(3)]
            continue
        if line.startswith("### "):
            current = None
        if current and line.startswith("| P-") and "| P 号 |" not in line:
            seen[current][1] += 1
            pid = line.split("|")[1].strip()
            seen[current][2] = min(seen[current][2], pid)
            seen[current][3] = max(seen[current][3], pid)
    assert len(seen) == 10
    for bucket, (declared, actual, first, last) in seen.items():
        assert actual == declared, f"{bucket}: header says {declared}, table has {actual}"
        assert bucket not in RECORDED_BUCKET_COUNTS or actual == RECORDED_BUCKET_COUNTS[bucket]
    assert sum(a for _d, a, _f, _l in seen.values()) == 132
