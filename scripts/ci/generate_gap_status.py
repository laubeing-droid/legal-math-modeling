#!/usr/bin/env python3
"""Generate the ten-gap closure status from source-side evidence (round-2 F7).

Origin: the ledger's closing line "十大缺口全部执行完毕" was hand-written and
was refuted twice -- by its own WBS-1 entry and by theorems that exist only on
fixtures. From now on the closure claim is a GENERATED artifact: each gap gets
a status derived from what actually exists in the source tree, never from
prose. If a declared witness disappears (rename, deletion), the status for that
gap degrades to WITNESS_MISSING instead of silently staying green -- the
artifact cannot drift ahead of the sources.

Rules (all evidence re-scanned on every run):
  CLOSED  -- every declared witness for the gap is present in the sources;
  PARTIAL -- the gap's own partial-rule fires (see PARTIAL_RULES);
  OPEN    -- the gap's open-rule fires (a registered refutation exists);
  WITNESS_MISSING -- a witness the mapping names is gone.

    python scripts/ci/generate_gap_status.py           # report only
    python scripts/ci/generate_gap_status.py --write   # rewrite the artifact
    python scripts/ci/generate_gap_status.py --check   # exit 1 if stale
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from datetime import date
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
SEAMS = ROOT / "proofs" / "lean" / "juris_lean" / "JurisLean"
ARTIFACT = ROOT / "docs" / "formal-release" / "gap_status.json"


def _read(path: Path) -> str:
    return path.read_text(encoding="utf-8")


def _has_theorem(text: str, name: str) -> bool:
    return re.search(rf"^theorem {re.escape(name)}\b", text, re.MULTILINE) is not None


def _seam(name: str) -> str:
    return _read(SEAMS / "Seams" / name)


def gap1_case_input() -> tuple[str, str]:
    """PARTIAL while the case-input layer has no downstream consumer.

    Consumption means a file OTHER than CaseInput.lean references `CaseFile` or
    `hornOfCase` in code (comments stripped). The audit driver printing axioms
    of the case-input theorems is NOT consumption -- it inspects, it does not
    feed the adjudication chain.
    """
    caseinput = _seam("CaseInput.lean")
    consumers = []
    for path in sorted(SEAMS.rglob("*.lean")):
        if path.name == "CaseInput.lean":
            continue
        text = re.sub(r"/-[-!]?.*?-/", "", _read(path), flags=re.DOTALL)
        text = re.sub(r"--[^\n]*", "", text)
        if re.search(r"\b(CaseFile|hornOfCase)\b", text):
            consumers.append(str(path.relative_to(SEAMS)))
    skeleton = _has_theorem(caseinput, "case_closure_sound")
    if not skeleton:
        return "WITNESS_MISSING", "case_closure_sound not found in CaseInput.lean"
    if consumers:
        return "CLOSED", f"downstream consumers exist: {consumers}"
    return "PARTIAL", (
        "case_closure_sound present (HornSystem skeleton); no downstream consumer "
        "of CaseFile/hornOfCase in the package -- adjudication chain not connected"
    )


def gap3_engine_consistency() -> tuple[str, str]:
    """OPEN while the registered refutation stands; CLOSED only if a positive
    instanceM consistency theorem appears AND the refutation is gone."""
    chain = _seam("StatuteChain.lean")
    trans = _seam("Transitions.lean")
    refutation = _has_theorem(chain, "instanceM_pol_not_adopted_consistent")
    positive = re.search(r"^theorem instanceM_\w*adopted_consistent\b", chain, re.MULTILINE)
    fixture = _has_theorem(trans, "art64_policy_is_adopted_consistent")
    if refutation:
        return "OPEN", (
            "instanceM_pol_not_adopted_consistent registered: AdoptedConsistent holds "
            + ("on the art64Policy fixture only" if fixture else "nowhere (fixture witness missing)")
        )
    if positive:
        return "CLOSED", "a positive instanceM consistency theorem exists and no refutation"
    return "WITNESS_MISSING", "neither the refutation nor a positive theorem found"


def _witness_gap(file: str, witnesses: list[str], closed_note: str,
                 missing_status: str = "WITNESS_MISSING") -> tuple[str, str]:
    text = _seam(file)
    missing = [w for w in witnesses if not _has_theorem(text, w)]
    if missing:
        return missing_status, f"missing witnesses in {file}: {missing}"
    return "CLOSED", closed_note


def gap6_limitation() -> tuple[str, str]:
    text = _seam("Limitation.lean")
    missing = [w for w in ("suspension_only_delays", "interruption_restarts_the_clock")
               if not _has_theorem(text, w)]
    if missing:
        return "WITNESS_MISSING", f"missing {missing}"
    blind = _has_theorem(text, "clarification_duty_is_level_blind")
    return "PARTIAL", (
        "limitation clock theorems present; clarification duty is a constant-Bool "
        "skeleton (level-blind blind-spot registered)"
        if blind else
        "limitation clock theorems present; clarification witness missing"
    )


def gap8_sanction() -> tuple[str, str]:
    text = _seam("SanctionInterest.lean")
    if not _has_theorem(text, "doubleInterest"):
        # fall back: any theorem in the module at all
        if not re.search(r"^theorem ", text, re.MULTILINE):
            return "WITNESS_MISSING", "no theorem in SanctionInterest.lean"
    return "PARTIAL", (
        "sanction field is loaded as data (definition-level read); no theorem states a "
        "legal effect of doubled interest -- registration is not closure"
    )


GAP_RULES = {
    1: ("案卷→载体输入层", gap1_case_input),
    2: ("逐案举证状态栏", lambda: _witness_gap(
        "StatuteChain.lean", ["chain_art90_two_readings_coherent"],
        "caseBurden field coherent-reading theorem present")),
    3: ("90 条不利后果/引擎自洽", gap3_engine_consistency),
    4: ("证明标准↔事实通道", lambda: _witness_gap(
        "BurdenStatutes.lean", ["art109_all_five_use_the_stricter_tier"],
        "109-tier bridge theorems present (factMatterClass fixture mapping noted)")),
    5: ("驳回/不予支持结论类型", lambda: _witness_gap(
        "Transitions.lean", ["art64_no_adjustment_rejected_at_round1"],
        "rejection outcome theorem present on the art64 carrier")),
    6: ("时效与审级", gap6_limitation),
    7: ("请求地位面→采纳面单向观测", lambda: _witness_gap(
        "StatuteChain.lean", ["observation_does_not_touch_adoption"],
        "one-way observation theorem present; reverse dictionary remains a permanent red line")),
    8: ("制裁层孤岛", gap8_sanction),
    9: ("损失基础", lambda: _witness_gap(
        "Probability.lean", ["netRecoverable_may_be_negative"],
        "loss-basis negative-readout honestly registered")),
    10: ("命名唯一性", lambda: _witness_gap(
        "StatuteChain.lean", ["chain_naming_uniqueness"],
        "naming uniqueness theorem present")),
}


def build() -> dict:
    gaps = []
    for gid, (title, rule) in sorted(GAP_RULES.items()):
        status, evidence = rule()
        gaps.append({"gap": gid, "title": title, "status": status, "evidence": evidence})
    summary: dict[str, int] = {}
    for g in gaps:
        summary[g["status"]] = summary.get(g["status"], 0) + 1
    return {
        "generated_by": "scripts/ci/generate_gap_status.py",
        "generated_on": str(date.today()),
        "rule": "status is derived from source-side witnesses; hand-written closure claims are void",
        "gaps": gaps,
        "summary": summary,
    }


def _strip_volatile(doc: dict) -> dict:
    """generated_on is a wall-clock fact, not a freshness fact (same precedent as
    rehearse_regeneration stripping the manifest's subject fields): a correct
    regeneration on another date or in another timezone must not read as stale."""
    return {k: v for k, v in doc.items() if k != "generated_on"}


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--write", action="store_true")
    ap.add_argument("--check", action="store_true")
    args = ap.parse_args()
    doc = build()
    rendered = json.dumps(doc, ensure_ascii=False, indent=2) + "\n"
    if args.check:
        if not ARTIFACT.is_file():
            print("gap_status.json is missing")
            return 1
        current = json.loads(ARTIFACT.read_text(encoding="utf-8"))
        if _strip_volatile(current) != _strip_volatile(doc):
            print("gap_status.json is stale (compared with generated_on stripped)")
            return 1
        print("gap_status.json is fresh")
        return 0
    if args.write:
        # newline="\n": text-mode writes on Windows would otherwise store CRLF, and
        # a Linux CI regeneration would then read the committed artifact as stale.
        ARTIFACT.write_text(rendered, encoding="utf-8", newline="\n")
    counts = ", ".join(f"{k}={v}" for k, v in sorted(doc["summary"].items()))
    print(f"gap status: {counts}")
    for g in doc["gaps"]:
        print(f"  gap {g['gap']:>2} {g['status']:<16} {g['title']}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
