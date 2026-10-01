#!/usr/bin/env python3
"""Emit two derived accounts that the repository previously only asserted.

1. `docs/formal-release/kernel_reuse_report.json` — measures whether the corpus
   is unified by a shared mathematical kernel, which Qoder audit judgement 1
   found it is not (Genealogy is a linear import chain with ~1 hand-rolled
   carrier per theorem and one Mathlib import). Numbers here are recomputed
   from source, so "同构统一" becomes a claim with a floor rather than a
   rhetorical description.

2. `docs/master-plan/基线/T谱/卷覆盖账.jsonl` — the volume plan (V01..V11) had no
   per-file manifest at all (audit D12: the plan's `registry/*.json` artifacts
   were never created). Each volume row now derives from the T-spectrum ledger,
   so a volume can no longer be reported "done" while its T slots carry
   record-field projections.

Both are generated artifacts: regenerate, never hand-edit.
"""

from __future__ import annotations

import json
import re
import sys
from collections import Counter, defaultdict
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
LEAN_BASE_PKG = ROOT / "proofs" / "lean" / "juris_lean"
LEAN_PKG = ROOT / "proofs" / "lean" / "juris_lean" / "JurisLean"
PLAN = ROOT / "docs" / "master-plan" / "基线" / "T谱" / "R20附件_分卷计划PLAN.md"
PLAN_V11 = ROOT / "docs" / "master-plan" / "基线" / "T谱" / "排卷回执_T112_T127.md"
LEDGER = ROOT / "theory" / "spec" / "lh_alignment" / "t_p_coverage.jsonl"
KERNEL_OUT = ROOT / "docs" / "formal-release" / "kernel_reuse_report.json"
VOLUME_OUT = PLAN.parent / "卷覆盖账.jsonl"

DECL_RE = re.compile(r"^(?:@\[[^\]]*\][ \t]*)*(theorem|lemma|def|structure|inductive)\s+([^\s(:{]+)", re.M)
IMPORT_RE = re.compile(r"^import\s+(\S+)", re.M)


def lean_files() -> list[Path]:
    return sorted(LEAN_PKG.rglob("*.lean"))


def module_of(path: Path) -> str:
    return str(path.relative_to(LEAN_PKG.parent)).replace("\\", "/")[:-5].replace("/", ".")


def kernel_report() -> dict:
    importers: dict[str, set[str]] = defaultdict(set)
    decl_count: Counter[str] = Counter()
    carrier_count: Counter[str] = Counter()
    mathlib_importers: set[str] = set()
    genealogy_chain: list[tuple[str, list[str]]] = []

    for path in lean_files():
        text = path.read_text(encoding="utf-8", errors="replace")
        mod = module_of(path)
        imports = IMPORT_RE.findall(text)
        for target in imports:
            importers[target].add(mod)
        if any(t.startswith("Mathlib") for t in imports):
            mathlib_importers.add(mod)
        kinds = DECL_RE.findall(text)
        decl_count[mod] = sum(1 for k, _ in kinds if k in ("theorem", "lemma"))
        carrier_count[mod] = sum(1 for k, _ in kinds if k in ("def", "structure", "inductive"))
        if "/Genealogy/" in str(path).replace("\\", "/"):
            genealogy_chain.append((mod, [i for i in imports if i.startswith("JurisLean.Genealogy")]))

    shared = {m: len(users) for m, users in importers.items() if len(users) >= 5}
    mandate = [m for m in decl_count if m.startswith("JurisLean.Mandate.")]
    genealogy = [m for m in decl_count if m.startswith("JurisLean.Genealogy")]
    genealogy_theorems = sum(decl_count[m] for m in genealogy)
    genealogy_carriers = sum(carrier_count[m] for m in genealogy)
    genealogy_mathlib = [m for m in genealogy if m in mathlib_importers]

    return {
        "schema_version": "kernel-reuse-v1",
        "authority_note": (
            "Static import-graph measurement over the JurisLean package. It says "
            "nothing about correctness; it says how much mathematics is shared."
        ),
        "package_files": len(list(lean_files())),
        "modules_imported_by_5_or_more": dict(sorted(shared.items(), key=lambda kv: -kv[1])),
        "genealogy": {
            "modules": len(genealogy),
            "theorem_declarations": genealogy_theorems,
            "hand_rolled_carriers": genealogy_carriers,
            "carriers_per_theorem": round(genealogy_carriers / genealogy_theorems, 2)
            if genealogy_theorems
            else None,
            "modules_importing_mathlib": sorted(genealogy_mathlib),
            "intra_genealogy_import_edges": [
                {"module": m, "imports_genealogy_modules": sorted(deps)} for m, deps in sorted(genealogy_chain)
            ],
        },
        "mandate": {
            "modules": len(mandate),
            "theorem_declarations": sum(decl_count[m] for m in mandate),
            "carriers": sum(carrier_count[m] for m in mandate),
            "carriers_per_theorem": round(
                sum(carrier_count[m] for m in mandate) / max(1, sum(decl_count[m] for m in mandate)), 2
            ),
            "modules_importing_kernel": sum(
                1 for m in mandate
                if "JurisLean.Mandate.Kernel" in IMPORT_RE.findall(
                    (LEAN_BASE_PKG / (m.replace(".", "/") + ".lean")).read_text(
                        encoding="utf-8", errors="replace"))
            ),
            "note": (
                "The mandate line is the kernel-first experiment: one shared algebra "
                "in Mandate/Kernel, consumed by the modules that need rates, selection "
                "and signatures. It is quoted next to the Genealogy ratio precisely so "
                "the contrast is measurable rather than rhetorical."
            ),
        },
        "counts": {
            "theorem_declarations_in_package": sum(decl_count.values()),
            "carriers_in_package": sum(carrier_count.values()),
        },
    }


def parse_volumes() -> dict[str, dict]:
    text = PLAN.read_text(encoding="utf-8")
    volumes: dict[str, dict] = {}
    for line in text.splitlines():
        cells = line.split("\t")
        if len(cells) < 3 or not re.fullmatch(r"V\d{2}", cells[0].strip()):
            continue
        vid = cells[0].strip()
        tids = re.findall(r"T\d+", cells[2])
        volumes[vid] = {"id": vid, "title": cells[1].strip(), "t_targets": tids}
    # V11 is created by the follow-up filing receipt, not the plan table.
    receipt = PLAN_V11.read_text(encoding="utf-8")
    # The receipt redistributes the 16 new T targets by *count* only
    # ("V02新增3项…V11承接7项"); the per-item list lives in a 修订版计划 that was
    # never filed into the repo. Inventing the identities would be the same
    # disease as a hand-written coverage ledger, so the counts are recorded and
    # the targets stay UNFILED until the real list lands.
    increments = {
        m.group(1): int(m.group(2))
        for m in re.finditer(r"(V\d{2})新增(\d+)项", receipt)
    }
    v11 = re.search(r"V11承接(\d+)项", receipt)
    if v11:
        increments["V11"] = int(v11.group(1))
    volumes.setdefault(
        "V11",
        {
            "id": "V11",
            "title": "行为主义卷（由 排卷回执_T112_T127.md 增立）",
            "t_targets": [],
            "declared_in": "docs/master-plan/基线/T谱/排卷回执_T112_T127.md",
        },
    )
    for vid, n in increments.items():
        if vid in volumes:
            volumes[vid]["declared_increment"] = n
    return volumes


def volume_rows() -> list[dict]:
    ledger = {
        json.loads(line)["t_id"]: json.loads(line)
        for line in LEDGER.read_text(encoding="utf-8").splitlines()
        if line.strip()
    }
    volumes = parse_volumes()
    all_t = {t for v in volumes.values() for t in v["t_targets"]}
    unfiled = sorted(set(ledger) - all_t, key=lambda s: int(s[1:]))
    rows = []
    for vid in sorted(volumes):
        v = volumes[vid]
        targets = [t for t in v["t_targets"] if t in ledger]
        grades = Counter(
            c["proof_grade"]
            for t in targets
            for c in ledger[t]["p_coverage"]
            if c["relation"] == "EXACT"
        )
        closed = sum(
            1
            for t in targets
            if all(c["coverage"] == "FULL" for c in ledger[t]["p_coverage"] if c["relation"] == "EXACT")
        )
        # `general_form_closed` cannot move on its own: the ledger grades a target FULL only
        # when every EXACT anchor is GENERAL *and* the source block carries no 降级注, and
        # every block currently carries one. So the count of targets that already have a
        # general proof is published separately, otherwise a real GENERAL carrier reads as 0
        # and the number describes the bookkeeping rather than the mathematics.
        general_carriers = sum(
            1
            for t in targets
            if any(
                c["proof_grade"] == "GENERAL"
                for c in ledger[t]["p_coverage"]
                if c["relation"] == "EXACT"
            )
        )
        rows.append(
            {
                "schema_version": "volume-account-v1",
                "volume": vid,
                "title": v["title"],
                "declared_in": v.get("declared_in", "R20附件_分卷计划PLAN.md"),
                "t_targets": len(targets),
                "declared_increment": v.get("declared_increment"),
                "t_targets_unmatched_in_ledger": sorted(set(v["t_targets"]) - set(ledger)),
                "carriers_present": len(targets),
                "carrier_grades": dict(grades),
                "general_form_closed": closed,
                "general_form_carriers": general_carriers,
                "completion": "EMPTY" if not targets else ("CLOSED" if closed == len(targets) else "CARRIED_ONLY"),
                "status_note": (
                    "Two different questions, two columns. general_form_carriers counts T "
                    "slots with at least one EXACT anchor whose proved statement binds "
                    "variables and closes on a HEAVY_PROOF tactic -- a general proof exists. "
                    "general_form_closed counts slots whose ledger coverage is FULL, which "
                    "additionally requires every EXACT anchor to be GENERAL and the source "
                    "block to carry no 降级注; while a block still records 完整陈述仍缺 the "
                    "slot is not closed no matter how strong its carrier is. CARRIED_ONLY "
                    "means every T slot has an anchored theorem. Neither column says the "
                    "declared target is met, and no general proof may be read as a closure."
                ),
            }
        )
    rows.append(
        {
            "schema_version": "volume-account-v1",
            "volume": "UNFILED",
            "title": "T targets with no volume assignment",
            "declared_in": "derived",
            "t_targets": len(unfiled),
            "t_targets_unmatched_in_ledger": [],
            "carriers_present": len(unfiled),
            "carrier_grades": dict(
                Counter(
                    c["proof_grade"]
                    for t in unfiled
                    for c in ledger[t]["p_coverage"]
                    if c["relation"] == "EXACT"
                )
            ),
            "general_form_closed": sum(
                1
                for t in unfiled
                if all(
                    c["coverage"] == "FULL"
                    for c in ledger[t]["p_coverage"]
                    if c["relation"] == "EXACT"
                )
            ),
            "general_form_carriers": sum(
                1
                for t in unfiled
                if any(
                    c["proof_grade"] == "GENERAL"
                    for c in ledger[t]["p_coverage"]
                    if c["relation"] == "EXACT"
                )
            ),
            "completion": "EMPTY" if not unfiled else "UNFILED",
            "status_note": (
                "must be zero for the plan to be whole; the 16 T112-T127 targets are "
                "unfiled because 排卷回执 records only per-volume counts (V02+3/V03+3/"
                "V05+3/V11+7) and the itemised revised plan is not in the repo"
            ),
        }
    )
    return rows


def main() -> int:
    check = "--check" in sys.argv
    kernel = kernel_report()
    rows = volume_rows()
    kernel_text = json.dumps(kernel, ensure_ascii=False, indent=1, sort_keys=True) + "\n"
    volume_text = "".join(json.dumps(r, ensure_ascii=False) + "\n" for r in rows)
    if check:
        ok = True
        if KERNEL_OUT.read_text(encoding="utf-8") != kernel_text:
            print("kernel_reuse_report.json is stale", file=sys.stderr)
            ok = False
        if VOLUME_OUT.read_text(encoding="utf-8") != volume_text:
            print("卷覆盖账.jsonl is stale", file=sys.stderr)
            ok = False
        return 0 if ok else 1
    KERNEL_OUT.write_text(kernel_text, encoding="utf-8", newline="\n")
    VOLUME_OUT.write_text(volume_text, encoding="utf-8", newline="\n")
    print(f"wrote {KERNEL_OUT.name} and {VOLUME_OUT.name}")
    g = kernel["genealogy"]
    print(f"  genealogy: {g['theorem_declarations']} theorems / {g['hand_rolled_carriers']} carriers "
          f"= {g['carriers_per_theorem']} per theorem; Mathlib-importing modules: {len(g['modules_importing_mathlib'])}")
    for r in rows:
        print(f"  {r['volume']:8s} targets={r['t_targets']:3d} general_closed={r['general_form_closed']:3d} {r['completion']}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
