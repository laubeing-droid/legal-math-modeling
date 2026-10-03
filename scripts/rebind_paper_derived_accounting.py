"""Rewrite the paper drafts' derived-accounting figures straight from the artifacts.

Both drafts carry a "derived accounting" section whose own heading says a generator writes it
from the artifacts. Until 2026-10-03 it did not: every proof that landed moved four groups of
numbers, and each time they were retyped by hand from a terminal reading -- the handwritten
ledger this repository bans elsewhere, and it had already produced one stale reading the guard
tests caught late.

So this script *is* that generator. It reads `theorem_inventory_v3.json`,
`trivial_proof_census.json`, `declaration_shape_report.json` and `AxiomAudit.lean`, recomputes
every figure, and rewrites each phrase by matching its **template** rather than a remembered
old value. A phrase whose template no longer matches is reported, never skipped in silence.

    python scripts/rebind_paper_derived_accounting.py           # report only
    python scripts/rebind_paper_derived_accounting.py --write   # rewrite both drafts
"""

from __future__ import annotations

import json
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
INVENTORY = ROOT / "docs" / "formal-release" / "theorem_inventory_v3.json"
CENSUS = ROOT / "docs" / "formal-release" / "trivial_proof_census.json"
SHAPE = ROOT / "docs" / "formal-release" / "declaration_shape_report.json"
AUDIT = ROOT / "proofs" / "lean" / "juris_lean" / "JurisLean" / "AxiomAudit.lean"
DRAFTS = {
    "cn": ROOT / "docs" / "paper-rewrite" / "paper_cn.md",
    "en": ROOT / "docs" / "paper-rewrite" / "paper_en.md",
}


def figures() -> dict[str, object]:
    """Every number the derived-accounting prose may state, recomputed from source."""
    inv = json.loads(INVENTORY.read_text(encoding="utf-8"))
    cen = json.loads(CENSUS.read_text(encoding="utf-8"))
    shape = json.loads(SHAPE.read_text(encoding="utf-8"))
    pkg = inv["scope_summary"]["juris_lean_package"]
    tracked = inv["scope_summary"]["all_tracked_lean"]
    counts = cen["closure_counts"]
    lines = AUDIT.read_text(encoding="utf-8").splitlines()
    audit_cmds = sum(1 for line in lines if line.startswith("#print axioms"))
    audit_mandate = sum(1 for line in lines if line.startswith("#print axioms JurisLean.Mandate."))
    out: dict[str, object] = {
        "pkg_theorems": pkg["theorem_count"],
        "pkg_lemmas": pkg["lemma_count"],
        "pkg_counted": pkg["counted_declaration_count"],
        "pkg_files": pkg["file_count"],
        "tracked_theorems": tracked["theorem_count"],
        "tracked_files": tracked["file_count"],
        "cmds": pkg["print_axioms_command_count"],
        "targets": pkg["print_axioms_distinct_targets"],
        "audit_cmds": audit_cmds,
        "audit_mandate": audit_mandate,
        "outside_audit": pkg["print_axioms_command_count"] - audit_cmds,
        "trivial": counts["TRIVIAL_TERM"],
        "decide": counts["DECIDE_CLOSED"],
        "tactic": counts["TACTIC"],
        "total": cen["theorem_declarations"],
        "alias": shape["scope"]["counts"]["ALIAS_ONE_LINER"],
        "closed": shape["scope"]["counts"]["CLOSED_NO_BINDERS"],
    }
    assert out["trivial"] + out["decide"] + out["tactic"] == out["total"], (
        "the closure classes do not partition the total"
    )
    assert out["pkg_theorems"] + out["pkg_lemmas"] == out["pkg_counted"], (
        "counted declarations are not theorems plus lemmas"
    )
    return out


def cn_specs(f: dict[str, object]) -> list[tuple[str, str]]:
    n = {k: str(v) for k, v in f.items()}
    return [
        (r"## 派生记账段（\d+ 口径，[^）]*）",
         f"## 派生记账段（{n['pkg_counted']} 口径，生成器直读工件重算，勿手改）"),
        (r"`juris_lean_package` \d+ 条定理声明、\d+ 个文件",
         f"`juris_lean_package` {n['pkg_theorems']} 条定理声明、{n['pkg_files']} 个文件"),
        (r"`all_tracked_lean` \d+ 条、\d+ 文件",
         f"`all_tracked_lean` {n['tracked_theorems']} 条、{n['tracked_files']} 文件"),
        (r"在源上是 \d+ 行 `#print axioms`", f"在源上是 {n['cmds']} 行 `#print axioms`"),
        (r"去重后 \d+ 个具名目标", f"去重后 {n['targets']} 个具名目标"),
        (r"全仓侧与包内同读数：\d+ 行、\d+ 个具名目标",
         f"全仓侧与包内同读数：{n['cmds']} 行、{n['targets']} 个具名目标"),
        (r"`AxiomAudit\.lean` 独占 \d+ 行", f"`AxiomAudit.lean` 独占 {n['audit_cmds']} 行"),
        (r"军令层现由 \d+ 条", f"军令层现由 {n['audit_mandate']} 条"),
        (r"\d+ 条命令去重得 \d+ 个具名目标（同一目标可在多处被点名），"
         r"其中 \d+ 条来自 `AxiomAudit\.lean`，余下 \d+ 条在别的驱动里",
         f"{n['cmds']} 条命令去重得 {n['targets']} 个具名目标（同一目标可在多处被点名），"
         f"其中 {n['audit_cmds']} 条来自 `AxiomAudit.lean`，"
         f"余下 {n['outside_audit']} 条在别的驱动里"),
        (r"全仓 \d+ 条定理声明中", f"全仓 {n['total']} 条定理声明中"),
        (r"\d+ 条由单一反射项闭合", f"{n['trivial']} 条由单一反射项闭合"),
        (r"\d+ 条由纯 decide 闭合", f"{n['decide']} 条由纯 decide 闭合"),
        (r"其余 \d+ 条含 tactic 过程", f"其余 {n['tactic']} 条含 tactic 过程"),
        (r"一行式契约搬运 \d+ 条", f"一行式契约搬运 {n['alias']} 条"),
        (r"结句中不绑定变量的 \d+ 条", f"结句中不绑定变量的 {n['closed']} 条"),
        (r"交叉核对：包内 \d+ 条定理加 \d+ 条 lemma，恰等于计入声明总数 \d+",
         f"交叉核对：包内 {n['pkg_theorems']} 条定理加 {n['pkg_lemmas']} 条 lemma，"
         f"恰等于计入声明总数 {n['pkg_counted']}"),
    ]


def en_specs(f: dict[str, object]) -> list[tuple[str, str]]:
    n = {k: str(v) for k, v in f.items()}
    return [
        (r"## Derived accounting section \(\d+ basis,[^)]*\)",
         f"## Derived accounting section ({n['pkg_counted']} basis, recomputed by the "
         f"generator from the artifacts - do not edit by hand)"),
        (r"\d+ theorem declarations in scope `juris_lean_package` across \d+ files",
         f"{n['pkg_theorems']} theorem declarations in scope `juris_lean_package` "
         f"across {n['pkg_files']} files"),
        (r"\d+ in scope `all_tracked_lean` across \d+ files",
         f"{n['tracked_theorems']} in scope `all_tracked_lean` across "
         f"{n['tracked_files']} files"),
        (r"carries \d+ `#print axioms` commands",
         f"carries {n['cmds']} `#print axioms` commands"),
        (r"with \d+ distinct targets", f"with {n['targets']} distinct targets"),
        (r"the tracked scope reads the same: \d+ commands and \d+ distinct targets",
         f"the tracked scope reads the same: {n['cmds']} commands and "
         f"{n['targets']} distinct targets"),
        (r"AxiomAudit\.lean alone owns \d+ `#print axioms` commands",
         f"AxiomAudit.lean alone owns {n['audit_cmds']} `#print axioms` commands"),
        (r"the mandate layer is \d+ named targets",
         f"the mandate layer is {n['audit_mandate']} named targets"),
        (r"so \d+ commands resolve to \d+ distinct targets; \d+ of them live in "
         r"AxiomAudit\.lean and \d+ in other drivers",
         f"so {n['cmds']} commands resolve to {n['targets']} distinct targets; "
         f"{n['audit_cmds']} of them live in AxiomAudit.lean and {n['outside_audit']} "
         f"in other drivers"),
        (r"of the \d+ declarations", f"of the {n['total']} declarations"),
        (r"\d+ close on a single reflexivity term",
         f"{n['trivial']} close on a single reflexivity term"),
        (r"\d+ close on `decide` alone", f"{n['decide']} close on `decide` alone"),
        (r"and \d+ carry a tactic proof", f"and {n['tactic']} carry a tactic proof"),
        (r"and \d+ conclusions bind no variable",
         f"and {n['closed']} conclusions bind no variable"),
        (r"The cross-check: \d+ theorems plus \d+ lemmas equal the \d+ counted declarations",
         f"The cross-check: {n['pkg_theorems']} theorems plus {n['pkg_lemmas']} lemmas "
         f"equal the {n['pkg_counted']} counted declarations"),
        (r"The audit surface reports \d+ named targets and AxiomAudit\.lean holds \d+ commands",
         f"The audit surface reports {n['targets']} named targets and AxiomAudit.lean "
         f"holds {n['audit_cmds']} commands"),
    ]


def apply(path: Path, specs: list[tuple[str, str]], write: bool) -> int:
    text = path.read_text(encoding="utf-8")
    missed: list[str] = []
    for pattern, replacement in specs:
        text, hits = re.subn(pattern, replacement, text)
        if hits == 0:
            missed.append(pattern)
    for pattern in missed:
        print(f"MISS {path.name}: {pattern[:72]}")
    if write and not missed:
        path.write_bytes(text.replace("\r\n", "\n").encode("utf-8"))
        print(f"OK {path.name}: {len(specs)} phrases rewritten")
    elif not missed:
        print(f"OK {path.name}: {len(specs)} phrases match (dry run)")
    return 1 if missed else 0


def main() -> int:
    f = figures()
    write = "--write" in sys.argv
    rc = apply(DRAFTS["cn"], cn_specs(f), write)
    rc |= apply(DRAFTS["en"], en_specs(f), write)
    print("figures:", {k: v for k, v in f.items() if isinstance(v, int)})
    return rc


if __name__ == "__main__":
    raise SystemExit(main())
