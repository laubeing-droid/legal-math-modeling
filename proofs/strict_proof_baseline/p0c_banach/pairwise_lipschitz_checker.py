# -*- coding: utf-8 -*-
"""
Theorem C2 (Toy Model): Pairwise Lipschitz ratio check on synthetic pricing data.

Data origin: TOY_SYNTHETIC
Scope: 15 hand-crafted synthetic items with linear pricing map f(T,e)=0.6T+0.4e
WARNING: This is a TOY MODEL. Results do NOT apply to real legal pricing.
"""

import math
import json
import os

def main():
    print("=" * 70)
    print("Theorem C2 (TOY MODEL): Pairwise Lipschitz checker")
    print("DATA_ORIGIN: TOY_SYNTHETIC")
    print("=" * 70)

    # TOY_SYNTHETIC dataset: 15 hand-crafted items
    dataset = [
        ("item_01",  8.0,  3), ("item_02", 12.0,  5), ("item_03",  6.0,  2),
        ("item_04", 10.0,  4), ("item_05", 15.0,  7), ("item_06",  4.0,  1),
        ("item_07", 20.0,  9), ("item_08",  9.0,  4), ("item_09", 11.0,  5),
        ("item_10",  7.0,  2), ("item_11", 14.0,  6), ("item_12", 18.0,  8),
        ("item_13",  5.0,  2), ("item_14", 16.0,  7), ("item_15", 13.0,  6),
    ]

    beta = 0.6

    def pricing_map(T, e):
        return beta * T + (1.0 - beta) * e

    def metric(T1, e1, T2, e2):
        return abs(T1 - T2) + abs(e1 - e2)

    n = len(dataset)
    max_ratio = 0.0
    max_pair = None
    skipped = 0
    total_pairs = 0

    print(f"TOY dataset size: {n} items")
    print(f"Beta = {beta}")
    print(f"Pricing map: f(T, e) = {beta}*T + {1-beta}*e")
    print(f"Metric: d = |T1-T2| + |e1-e2|")
    print("-" * 70)

    for i in range(n):
        for j in range(i + 1, n):
            total_pairs += 1
            _, Ti, ei = dataset[i]
            _, Tj, ej = dataset[j]
            fi = pricing_map(Ti, ei)
            fj = pricing_map(Tj, ej)
            d = metric(Ti, ei, Tj, ej)
            if d == 0:
                skipped += 1
                continue
            ratio = abs(fi - fj) / d
            if ratio > max_ratio:
                max_ratio = ratio
                max_pair = (dataset[i], dataset[j], ratio)

    print(f"Total pairs: {total_pairs}")
    print(f"Skipped (d=0): {skipped}")
    print(f"Supremum ratio: {max_ratio:.6f}")
    if max_pair:
        a, b, r = max_pair
        print(f"Max pair: {a} vs {b}, ratio = {r:.6f}")

    theoretical = max(beta, 1.0 - beta)
    print(f"Theoretical bound: {theoretical:.6f}")

    result = {
        "data_origin": "TOY_SYNTHETIC",
        "scope": "15 synthetic items, linear pricing map, L1 metric",
        "total_pairs": total_pairs,
        "supremum_ratio": max_ratio,
        "theoretical_bound": theoretical,
        "status": "TOY_SYNTHETIC_PROOF_ONLY",
        "warning": "This proof applies ONLY to the synthetic toy model. Real legal pricing data is DATA_INSUFFICIENT_FOR_PROOF."
    }
    out_path = os.path.join(os.path.dirname(__file__), "toy_proof_result.json")
    with open(out_path, "w", encoding="utf-8") as f:
        json.dump(result, f, ensure_ascii=False, indent=2)

    if max_ratio < 1.0:
        print("\n[RESULT] TOY_SYNTHETIC_PROOF_ONLY")
        print(f"All pairs have ratio < 1 (sup = {max_ratio:.6f}).")
        print("WARNING: This is a TOY MODEL. Do not use as real theorem proof.")
    else:
        print("\n[RESULT] TOY_SYNTHETIC_REFUTED")
        print(f"Found pair with ratio >= 1: {max_ratio:.6f}")

    print("=" * 70)
    return 0  # Script ran successfully; result is toy proof only

if __name__ == "__main__":
    exit(main())
