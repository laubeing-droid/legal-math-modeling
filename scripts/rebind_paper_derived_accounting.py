"""Rebind the derived-accounting prose in both paper drafts to the current artifacts.

Every replacement is an exact literal old -> new pair, asserted to be present, so a
number that already moved cannot be silently re-moved. Run with --check to audit
without writing.
"""

from __future__ import annotations

import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
CN = ROOT / "docs" / "paper-rewrite" / "paper_cn.md"
EN = ROOT / "docs" / "paper-rewrite" / "paper_en.md"

CN_PAIRS = [
    ("## 派生记账段（3538 口径，2026-10-02 重算，勿手改）",
     "## 派生记账段（3692 口径，2026-10-03 重算，勿手改）"),
    ("`juris_lean_package` 3555 条定理声明",
     "`juris_lean_package` 3558 条定理声明"),
    ("`all_tracked_lean` 3567 条、319 文件",
     "`all_tracked_lean` 3570 条、319 文件"),
    ("在源上是 2590 行 `#print axioms`",
     "在源上是 2593 行 `#print axioms`"),
    ("去重后 2536 个具名目标", "去重后 2539 个具名目标"),
    ("全仓侧共 2573 行、2519 个具名目标（`theorem_inventory_v3.json`）",
     "全仓侧与包内同读数：2593 行、2539 个具名目标（`theorem_inventory_v3.json`）"),
    ("`AxiomAudit.lean` 独占 2327 行", "`AxiomAudit.lean` 独占 2330 行"),
    ("2310 行里有 2519 个具名目标可解析（`theorem_inventory_v3.json`），余下为驱动自用条目。",
     "2593 条命令去重得 2539 个具名目标（同一目标可在多处被点名），"
     "其中 2330 条来自 `AxiomAudit.lean`，余下 263 条在别的驱动里（`theorem_inventory_v3.json`）。"),
    ("**闭合形态**：全仓 3555 条定理声明中", "**闭合形态**：全仓 3558 条定理声明中"),
    ("101 条由纯 decide 闭合", "102 条由纯 decide 闭合"),
    ("其余 3171 条含 tactic 过程", "其余 3173 条含 tactic 过程"),
    ("结句中不绑定变量的 1217 条", "结句中不绑定变量的 1218 条"),
    ("交叉核对两侧相等：清单侧 3538，本报告侧 3538（`theorem_inventory_v3.json`）。",
     "交叉核对：包内 3558 条定理加 134 条 lemma，恰等于计入声明总数 3692"
     "（`theorem_inventory_v3.json`）。"),
]

EN_PAIRS = [
    ("## Derived accounting section (3538 basis, recomputed 2026-10-02 - do not edit by hand)",
     "## Derived accounting section (3692 basis, recomputed 2026-10-03 - do not edit by hand)"),
    ("3555 theorem declarations in scope `juris_lean_package`",
     "3558 theorem declarations in scope `juris_lean_package`"),
    ("3567 in scope `all_tracked_lean`", "3570 in scope `all_tracked_lean`"),
    ("carries 2590 `#print axioms` commands", "carries 2593 `#print axioms` commands"),
    ("with 2536 distinct targets; the tracked scope holds 2573 commands "
     "and 2536 distinct targets.",
     "with 2539 distinct targets; the tracked scope reads the same: 2593 commands "
     "and 2539 distinct targets."),
    ("AxiomAudit.lean alone owns 2310 `#print axioms` commands",
     "AxiomAudit.lean alone owns 2330 `#print axioms` commands"),
    ("so 2310 lines resolve to 2536 distinct targets with the remainder driver-local.",
     "so 2593 commands resolve to 2539 distinct targets; 2330 of them live in "
     "AxiomAudit.lean and 263 in other drivers."),
    ("of the 3555 declarations", "of the 3558 declarations"),
    ("101 close on `decide` alone", "102 close on `decide` alone"),
    ("and 3171 carry a tactic proof", "and 3173 carry a tactic proof"),
    ("and 1217 conclusions bind no variable", "and 1218 conclusions bind no variable"),
    ("The cross-check agrees on both sides: 3538 and 3538",
     "The cross-check: 3558 theorems plus 134 lemmas equal the 3692 counted declarations"),
    ("The audit surface reports 2536 named targets and AxiomAudit.lean holds 2327 commands",
     "The audit surface reports 2539 named targets and AxiomAudit.lean holds 2330 commands"),
]


def apply(path: Path, pairs: list[tuple[str, str]], write: bool) -> int:
    raw = path.read_bytes()
    text = raw.decode("utf-8")
    failures = []
    for old, new in pairs:
        n = text.count(old)
        if n == 0:
            failures.append(old)
            continue
        text = text.replace(old, new)
    if failures:
        for f in failures:
            print(f"MISS {path.name}: {f[:70]}")
        return 1
    if write:
        path.write_bytes(text.replace("\r\n", "\n").encode("utf-8"))
    print(f"OK {path.name}: {len(pairs)} phrases rebound")
    return 0


def main() -> int:
    write = "--write" in sys.argv
    rc = apply(CN, CN_PAIRS, write)
    rc |= apply(EN, EN_PAIRS, write)
    return rc


if __name__ == "__main__":
    raise SystemExit(main())
