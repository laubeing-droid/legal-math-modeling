#!/usr/bin/env python3
"""
#93: Cross-Jurisdiction Obstruction Checker
===========================================

Constructs finite sample mappings from claim_mapping.csv and checks
whether collision-free cross-jurisdiction mapping exists.

Outputs: TOY_SYNTHETIC_ONLY (collision found in sample)
         DATA_INSUFFICIENT (sample too small for universal claim)
"""

from __future__ import annotations

import csv
import json
import os
import sys
import time
from collections import defaultdict
from pathlib import Path

_PROJECT_ROOT = Path(__file__).resolve().parent.parent.parent.parent
if str(_PROJECT_ROOT) not in sys.path:
    sys.path.insert(0, str(_PROJECT_ROOT))


def load_claims():
    claims = []
    path = _PROJECT_ROOT / "data" / "category_rosetta" / "claim_mapping.csv"
    with open(path, encoding="utf-8") as f:
        for row in csv.DictReader(f):
            claims.append(row)
    return claims


def load_obstructions():
    path = _PROJECT_ROOT / "data" / "category_rosetta" / "obstruction_analysis.json"
    with open(path, encoding="utf-8") as f:
        return json.load(f)


def check_collision_free(claims):
    """Check if any two claims with different CN claims map to the same foreign claim."""
    collisions = []
    for i, a in enumerate(claims):
        for j, b in enumerate(claims):
            if i >= j:
                continue
            if a["cn_claim"] != b["cn_claim"]:
                # Check if they collide in any foreign jurisdiction
                for jur in ["us_claim", "hk_claim"]:
                    av = a.get(jur, "DATA_UNAVAILABLE")
                    bv = b.get(jur, "DATA_UNAVAILABLE")
                    if av != "DATA_UNAVAILABLE" and bv != "DATA_UNAVAILABLE" and av == bv:
                        collisions.append({
                            "pattern_a": a["pattern_id"],
                            "pattern_b": b["pattern_id"],
                            "jurisdiction": jur.replace("_claim", ""),
                            "cn_a": a["cn_claim"][:60],
                            "cn_b": b["cn_claim"][:60],
                            "shared_foreign": av[:60],
                        })
    return collisions


def main():
    start = time.time()
    print("=" * 60)
    print("Cross-Jurisdiction Obstruction Checker")
    print("=" * 60)

    claims = load_claims()
    obstructions = load_obstructions()

    print(f"\nLoaded {len(claims)} claim mappings")
    print(f"Loaded {len(obstructions.get('obstructions', []))} obstruction types")

    # Status distribution
    status_counts = defaultdict(int)
    for c in claims:
        status_counts[c.get("mapping_status", "UNKNOWN")] += 1
    print(f"\nMapping status distribution:")
    for s, n in sorted(status_counts.items(), key=lambda x: -x[1]):
        print(f"  {s}: {n}")

    # Check for collisions
    print(f"\nChecking for collisions...")
    collisions = check_collision_free(claims)
    print(f"  Found {len(collisions)} collision(s)")

    if collisions:
        print("\n  COLLISION WITNESSES:")
        for c in collisions[:5]:
            print(f"    {c['pattern_a']} vs {c['pattern_b']} in {c['jurisdiction']}")
            print(f"      CN: {c['cn_a']} | {c['cn_b']}")
            print(f"      Shared: {c['shared_foreign']}")

    # Obstruction types
    obs_types = obstructions.get("obstructions", [])
    print(f"\nObstruction types ({len(obs_types)}):")
    for obs in obs_types:
        print(f"  {obs['type']:25s} hard_cases={obs.get('hard_cases', [])}")

    # Verdict
    print(f"\n{'=' * 60}")
    print("VERDICT:")
    if collisions:
        print(f"  TOY_SYNTHETIC_ONLY: {len(collisions)} collision(s) found in {len(claims)}-sample")
        print(f"  Collision-free mapping does NOT exist in this sample.")
    else:
        print(f"  No collisions found in {len(claims)}-sample.")
        print(f"  DATA_INSUFFICIENT: sample too small for universal claim.")

    print(f"\n  NOTE: This is a finite sample check (n={len(claims)}).")
    print(f"  Universal impossibility requires proof over all possible mappings.")
    print(f"  Current result: {'TOY_SYNTHETIC_ONLY' if collisions else 'DATA_INSUFFICIENT'}")
    print("=" * 60)

    # Save witness
    out_dir = _PROJECT_ROOT / "reports" / "obstruction"
    out_dir.mkdir(parents=True, exist_ok=True)
    witness = {
        "sample_size": len(claims),
        "collision_count": len(collisions),
        "collisions": collisions[:10],
        "obstruction_types": len(obs_types),
        "status_distribution": dict(status_counts),
        "verdict": "TOY_SYNTHETIC_ONLY" if collisions else "DATA_INSUFFICIENT",
    }
    out_path = out_dir / "obstruction_witness.json"
    with open(out_path, "w", encoding="utf-8") as f:
        json.dump(witness, f, indent=2, ensure_ascii=False)
    print(f"\nWitness: {out_path}")

    elapsed = time.time() - start
    print(f"Time: {elapsed:.2f}s")


if __name__ == "__main__":
    main()
