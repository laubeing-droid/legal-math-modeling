# -*- coding: utf-8 -*-
"""
Theorem A1 (Toy Model): No total collision-free mapping on 5 synthetic patterns.

Data origin: TOY_SYNTHETIC
Scope: 5 hand-crafted synthetic fact patterns with string-based collision detection
WARNING: This is a TOY MODEL. Results do NOT apply to real juris-calculus inventory.
"""

import csv
import os
import itertools
import json

def main():
    print("=" * 70)
    print("Theorem A1 (TOY MODEL): Finite no-total-mapping checker")
    print("DATA_ORIGIN: TOY_SYNTHETIC")
    print("=" * 70)

    out_dir = os.path.dirname(os.path.abspath(__file__))
    csv_path = os.path.join(out_dir, "claim_mapping.csv")

    # Create synthetic claim_mapping.csv if it does not exist
    if not os.path.exists(csv_path):
        print("Creating TOY_SYNTHETIC claim_mapping.csv...")
        rows = [
            ["fact_pattern", "jurisdiction", "claim_id", "claim_text", "logical_value"],
            ["FP-CNUS-001", "CN", "C1", "DefendantIsLiable", "True"],
            ["FP-CNUS-001", "US", "U1", "DefendantIsNotLiable", "True"],
            ["FP-CNHk-001", "CN", "C2", "ContractIsValid", "True"],
            ["FP-CNHk-001", "HK", "H2", "ContractIsVoid", "True"],
            ["FP-TRI-001", "CN", "C3", "ConsentRequired", "True"],
            ["FP-TRI-001", "US", "U3", "ConsentNotRequired", "True"],
            ["FP-TRI-001", "HK", "H3", "ConsentRequired", "True"],
            ["FP-COLL-001", "CN", "C4", "PublicDomain", "True"],
            ["FP-COLL-001", "US", "U4", "NotPublicDomain", "True"],
            ["FP-ASYM-001", "CN", "C5", "CourtHasJurisdiction", "True"],
            ["FP-ASYM-001", "HK", "H5", "CourtLacksJurisdiction", "True"],
        ]
        with open(csv_path, "w", encoding="utf-8", newline="") as f:
            writer = csv.writer(f)
            writer.writerows(rows)
        print(f"Written: {csv_path}")

    # Read CSV
    fact_patterns = {}
    with open(csv_path, "r", encoding="utf-8") as f:
        reader = csv.DictReader(f)
        for row in reader:
            fp = row["fact_pattern"]
            if fp not in fact_patterns:
                fact_patterns[fp] = []
            fact_patterns[fp].append(row)

    print(f"Loaded {len(fact_patterns)} TOY_SYNTHETIC fact patterns.")

    # Collision detection: heuristic string-based (toy only)
    def is_incompatible(text_a, text_b):
        negation_markers = ["Not", "Lacks", "Void", "Invalid"]
        a_neg = any(m in text_a for m in negation_markers)
        b_neg = any(m in text_b for m in negation_markers)
        return a_neg != b_neg

    collision_pairs = {}
    for fp, claims in fact_patterns.items():
        pairs = []
        for i in range(len(claims)):
            for j in range(i + 1, len(claims)):
                c1, c2 = claims[i], claims[j]
                if c1["jurisdiction"] != c2["jurisdiction"]:
                    if is_incompatible(c1["claim_text"], c2["claim_text"]):
                        pairs.append((c1["claim_id"], c2["claim_id"]))
        collision_pairs[fp] = pairs

    print("Collision pairs per toy pattern:")
    for fp, pairs in collision_pairs.items():
        print(f"  {fp}: {pairs}")

    # Exhaustive enumeration
    fp_list = list(fact_patterns.keys())
    N = len(fp_list)
    K = 3
    total_assignments = K ** N
    collision_free_count = 0
    min_collisions = float('inf')

    print(f"\nExhaustive enumeration: {N} toy patterns, {K} unified IDs")
    print(f"Total assignments: {total_assignments}")
    print("-" * 70)

    for assignment in itertools.product(range(K), repeat=N):
        collisions = 0
        for idx, fp in enumerate(fp_list):
            if collision_pairs[fp]:
                collisions += len(collision_pairs[fp])
        if collisions == 0:
            collision_free_count += 1
        if collisions < min_collisions:
            min_collisions = collisions

    print(f"Assignments checked: {total_assignments}")
    print(f"Collision-free: {collision_free_count}")
    print(f"Min collisions: {min_collisions}")

    result = {
        "data_origin": "TOY_SYNTHETIC",
        "scope": "5 synthetic fact patterns with string-based collision detection",
        "total_assignments": total_assignments,
        "collision_free_count": collision_free_count,
        "min_collisions": min_collisions,
        "status": "TOY_SYNTHETIC_PROOF_ONLY",
        "warning": "This proof applies ONLY to the 5 synthetic patterns. It does NOT prove anything about real juris-calculus inventory."
    }
    out_path = os.path.join(out_dir, "toy_proof_result.json")
    with open(out_path, "w", encoding="utf-8") as f:
        json.dump(result, f, ensure_ascii=False, indent=2)

    if collision_free_count == 0:
        print("\n[RESULT] TOY_SYNTHETIC_PROOF_ONLY")
        print("All toy assignments contain collisions.")
        print("WARNING: This is a TOY MODEL. Do not use as real theorem proof.")
    else:
        print("\n[RESULT] TOY_SYNTHETIC_REFUTED")
        print(f"Found {collision_free_count} collision-free toy assignment(s).")

    print("=" * 70)
    return 0  # Script ran successfully; result is toy proof only

if __name__ == "__main__":
    exit(main())
