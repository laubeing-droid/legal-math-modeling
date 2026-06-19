#!/usr/bin/env python3
"""
Extended adversarial tests for 5 additional modules.
"""
from __future__ import annotations
import json, os, sys, time
from datetime import date
from pathlib import Path

_PROJECT_ROOT = Path(__file__).resolve().parent.parent.parent.parent
if str(_PROJECT_ROOT) not in sys.path:
    sys.path.insert(0, str(_PROJECT_ROOT))

results = []

def record(test_id, category, desc, passed, reason, details=None):
    results.append({"test_id": test_id, "category": category, "description": desc,
                     "passed": passed, "reason": reason, "details": details or {}})
    tag = "PASS" if passed else "FAIL"
    print(f"  [{tag}] {test_id}: {desc}")


def test_burden_of_proof():
    print("\n=== Burden of Proof Tracker ===")
    from theory.burden_of_proof_tracker import (
        BurdenHolder, EvidenceStandard, BurdenOfProof, BurdenOfProofTracker,
    )
    tracker = BurdenOfProofTracker()
    w1 = tracker.create_world("w1", None, "trial")
    record("EXT-001", "burden", "Initial world has empty burdens",
           len(w1.burdens) == 0, f"burdens={len(w1.burdens)}")

    tracker.set_burden("w1", "claim1", BurdenHolder.PLAINTIFF,
                       EvidenceStandard.PREPONDERANCE, source_rule="Art. 65")
    w2 = tracker.create_world("w2", "w1", "appeal")
    record("EXT-002", "burden", "Burden inherited on fork",
           "claim1" in w2.burdens, f"w2 burdens: {list(w2.burdens.keys())}")

    if "claim1" in w2.burdens:
        record("EXT-003", "burden", "Inherited burden preserves holder",
               w2.burdens["claim1"].holder == BurdenHolder.PLAINTIFF,
               f"holder={w2.burdens['claim1'].holder}")

    try:
        tracker.reverse_burden("w2", "claim1", BurdenHolder.DEFENDANT, "new evidence")
        record("EXT-004", "burden", "Burden reversal changes holder",
               w2.burdens.get("claim1") and w2.burdens["claim1"].holder == BurdenHolder.DEFENDANT,
               f"holder={w2.burdens.get('claim1', {}).holder if 'claim1' in w2.burdens else 'N/A'}")
    except Exception as e:
        record("EXT-004", "burden", "Burden reversal", False, str(e)[:100])


def test_evidence_dependency():
    print("\n=== Evidence Dependency Manager ===")
    from theory.evidence_dependency_manager import EvidenceDependencyManager, ClaimNode
    from theory.model_status import EvidenceStatus
    mgr = EvidenceDependencyManager()
    try:
        mgr.add_node(ClaimNode("T1", EvidenceStatus.PROVED_BY_EXHAUSTIVE_ENUMERATION))
        mgr.add_node(ClaimNode("T2", EvidenceStatus.PROVED_BY_EXHAUSTIVE_ENUMERATION, ["T1"]))
        record("EXT-005", "dependency", "Add nodes without crash", True, "T1+T2 added")
        report = mgr.propagate_status_change("T1", EvidenceStatus.REFUTED_BY_COUNTEREXAMPLE)
        record("EXT-006", "dependency", "Propagate status change",
               isinstance(report, dict), f"report keys={list(report.keys())[:3]}")
    except Exception as e:
        record("EXT-005", "dependency", "Add nodes", False, str(e)[:100])
        record("EXT-006", "dependency", "Propagate", False, str(e)[:100])


def test_temporal_law_engine():
    print("\n=== Temporal Law Engine ===")
    from theory.temporal_law_engine import TemporalLawEngine, LegalRule, LawType
    engine = TemporalLawEngine()
    try:
        engine.add_rule(LegalRule(
            id="contract_1999", statute="Contract Law", article="Art. 1",
            content="Contract formation", law_type=LawType.SUBSTANTIVE,
            effective_date=date(1999, 10, 1), expiry_date=date(2021, 1, 1),
        ))
        engine.add_rule(LegalRule(
            id="civil_code_2021", statute="Civil Code", article="Art. 463",
            content="Contract formation", law_type=LawType.SUBSTANTIVE,
            effective_date=date(2021, 1, 1),
        ))
        record("EXT-007", "temporal", "Add temporal rules without crash", True, "2 rules added")
        result = engine.snapshot(date(2020, 6, 1))
        record("EXT-008", "temporal", "Snapshot returns list",
               isinstance(result, list), f"n={len(result)}")
    except Exception as e:
        record("EXT-007", "temporal", "Add rules", False, str(e)[:100])
        record("EXT-008", "temporal", "Snapshot", False, str(e)[:100])


def test_deontic_procedural():
    print("\n=== Deontic Procedural Justice ===")
    from theory.deontic_procedural_justice import DeonticOperator, DeonticRule
    record("EXT-009", "deontic", "DeonticOperator has OB/PER/FOR",
           all(hasattr(DeonticOperator, a) for a in ['OB', 'PER', 'FOR']),
           f"members: {[m.name for m in DeonticOperator]}")
    try:
        rule = DeonticRule(id="DP-001", condition="before deadline",
                           operator=DeonticOperator.OB, consequence="timely filing",
                           authority="Art. 65")
        record("EXT-010", "deontic", "DeonticRule constructs correctly",
               rule is not None and rule.id == "DP-001", f"id={rule.id}")
    except Exception as e:
        record("EXT-010", "deontic", "DeonticRule construct", False, str(e)[:100])


def test_rough_set():
    print("\n=== Rough Set Discretionary ===")
    from theory.rough_set_discretionary import RoughConcept
    try:
        concept = RoughConcept(name="damages_amount",
                               positive_examples={"high_damage", "severe_injury"},
                               negative_examples={"minor_damage"},
                               relevant_attributes=["injury_severity", "fault_degree"])
        record("EXT-011", "rough_set", "RoughConcept constructs correctly",
               concept is not None and concept.name == "damages_amount",
               f"name={concept.name}, pos={len(concept.positive_examples)}")
    except Exception as e:
        record("EXT-011", "rough_set", "RoughConcept construct", False, str(e)[:100])


def main():
    start = time.time()
    print("=" * 60)
    print("Extended Adversarial Tests — 5 Additional Modules")
    print("=" * 60)
    test_burden_of_proof()
    test_evidence_dependency()
    test_temporal_law_engine()
    test_deontic_procedural()
    test_rough_set()
    elapsed = time.time() - start
    passed = sum(1 for r in results if r["passed"])
    failed = sum(1 for r in results if not r["passed"])
    print(f"\n{'=' * 60}")
    print(f"SUMMARY: {passed}/{len(results)} passed, {failed} failed, {elapsed:.2f}s")
    if failed:
        print("\nFAILED:")
        for r in results:
            if not r["passed"]:
                print(f"  [{r['test_id']}] {r['description']}: {r['reason']}")
    print("=" * 60)
    out_path = _PROJECT_ROOT / "proofs" / "engineering_proof_artifacts" / "adversarial" / "extended_adversarial_results.json"
    with open(out_path, "w", encoding="utf-8") as f:
        json.dump({"total": len(results), "passed": passed, "failed": failed,
                    "runtime_seconds": round(elapsed, 2), "results": results},
                   f, indent=2, ensure_ascii=False)
    print(f"\nResults: {out_path}")
    return 0 if failed == 0 else 1

if __name__ == "__main__":
    sys.exit(main())
