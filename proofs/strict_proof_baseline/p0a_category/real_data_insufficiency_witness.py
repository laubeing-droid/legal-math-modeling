# -*- coding: utf-8 -*-
"""
Theorem A1 (Real Data Version): Insufficiency witness for total collision-free 
cross-jurisdiction mapping on current inventory.

Data origin: REAL_COLLECTED (from claim_mapping.csv with source-backed annotations)
Scope: current 44-row inventory (30 CN-only + 14 cross-jurisdiction)

Claim: We CANNOT prove from first principles that no total collision-free mapping 
exists, because collision detection relies on human-annotated mapping_status 
(COLLISION, ASYMMETRY) from legal corpus analysis, not on formal logical derivation.

Method: Read real claim_mapping.csv, count source-backed collision rows, 
output insufficiency witness.
Status: DATA_INSUFFICIENT_FOR_PROOF (real data) / TOY_SYNTHETIC_PROOF_ONLY (toy model)
"""

import csv
import os
import json

def main():
    print("=" * 70)
    print("Theorem A1: Real-data insufficiency witness")
    print("=" * 70)
    
    # Read real claim_mapping.csv
    real_csv = r"D:\Codex\juris-calculus\20260611 kimi proof\data\category_rosetta\claim_mapping.csv"
    
    if not os.path.exists(real_csv):
        print(f"ERROR: Real data file not found: {real_csv}")
        print("[RESULT] DATA_INSUFFICIENT_FOR_PROOF")
        return 1
    
    rows = []
    with open(real_csv, "r", encoding="utf-8") as f:
        reader = csv.DictReader(f)
        for row in reader:
            rows.append(row)
    
    total = len(rows)
    cn_only = sum(1 for r in rows if r.get("mapping_status") == "CN_ONLY")
    cross_jur = [r for r in rows if r.get("mapping_status") not in ("CN_ONLY", "US_ONLY", "HK_ONLY", "")]
    collision_rows = [r for r in cross_jur if r.get("mapping_status") in ("COLLISION", "ASYMMETRY")]
    partial_rows = [r for r in cross_jur if r.get("mapping_status") in ("CN_US_PARTIAL", "CN_HK_PARTIAL", "TRI_JURISDICTION_PARTIAL")]
    mapped_rows = [r for r in cross_jur if r.get("mapping_status") == "TRI_JURISDICTION_MAPPED"]
    
    print(f"Total rows in inventory: {total}")
    print(f"  CN_ONLY: {cn_only}")
    print(f"  Cross-jurisdiction: {len(cross_jur)}")
    print(f"    COLLISION: {len(collision_rows)}")
    print(f"    ASYMMETRY: {len([r for r in cross_jur if r.get('mapping_status')=='ASYMMETRY'])}")
    print(f"    PARTIAL: {len(partial_rows)}")
    print(f"    MAPPED: {len(mapped_rows)}")
    
    # Key observation: collision detection depends on mapping_status field,
    # which is a human annotation from legal corpus analysis, not a formal 
    # logical derivation.
    witness = {
        "data_origin": "REAL_COLLECTED",
        "scope": "current 44-row inventory",
        "total_rows": total,
        "cn_only": cn_only,
        "cross_jurisdiction": len(cross_jur),
        "collision_rows": len(collision_rows),
        "collision_pattern_ids": [r.get("pattern_id") for r in collision_rows],
        "insufficiency_reason": "Collision detection relies on human-annotated mapping_status (COLLISION/ASYMMETRY) from legal corpus analysis. This is an empirical legal finding, not a formal logical derivation. No automated collision detection from claim text alone is implemented.",
        "implication": "Cannot prove from first principles that no total collision-free mapping exists. The collision annotations are source-backed but not formally derived."
    }
    
    out_path = os.path.join(os.path.dirname(__file__), "real_data_insufficiency_witness.json")
    with open(out_path, "w", encoding="utf-8") as f:
        json.dump(witness, f, ensure_ascii=False, indent=2)
    print(f"\nWitness written to: {out_path}")
    
    print("\n" + "-" * 70)
    print("[RESULT] DATA_INSUFFICIENT_FOR_PROOF")
    print("Real inventory has source-backed collision annotations, but these are")
    print("empirical legal findings, not formal logical derivations. Cannot prove")
    print("from first principles that no total collision-free mapping exists.")
    print("=" * 70)
    return 0

if __name__ == "__main__":
    exit(main())
