#!/usr/bin/env python3
"""
T8.5 + T9.4 Runner: Rosetta + Banach on merged clean data
"""

import csv
import math
import json
import time
from pathlib import Path
from collections import Counter, defaultdict

T85_PATH = "data/category_rosetta/T8.5_merged_clean.csv"
T94_PATH = "data/category_rosetta/T9.4_merged_clean.csv"

OBSTRUCTION_STATUSES = {"COLLISION", "ASYMMETRY", "CN_ONLY"}
PARTIAL_STATUSES = {"CN_US_PARTIAL", "CN_HK_PARTIAL", "US_HK_PARTIAL",
                    "TRI_JURISDICTION_PARTIAL", "TRI_JURISDICTION_MAPPED"}


# ============================================================
# T8.5: Rosetta Obstruction Analysis
# ============================================================

def run_t85():
    print("=" * 60)
    print("T8.5: Rosetta Obstruction Analysis")
    print("=" * 60)

    with open(T85_PATH, encoding="utf-8-sig") as f:
        rows = list(csv.DictReader(f))

    total = len(rows)
    print(f"\n  Total rows: {total}")

    # Status distribution
    statuses = Counter(r["mapping_status"] for r in rows)
    print(f"\n  Mapping status:")
    for s, c in statuses.most_common():
        pct = c / max(total, 1) * 100
        print(f"    {s}: {c} ({pct:.1f}%)")

    # Obstruction analysis
    obstructions = [r for r in rows if r["mapping_status"] in OBSTRUCTION_STATUSES]
    partials = [r for r in rows if r["mapping_status"] in PARTIAL_STATUSES]

    obstruction_count = len(obstructions)
    obstruction_density = obstruction_count / max(total, 1)

    print(f"\n  Obstructions (COLLISION + ASYMMETRY + CN_ONLY): {obstruction_count}")
    print(f"  Obstruction density: {obstruction_density:.4f} ({obstruction_density*100:.1f}%)")
    print(f"  Mappable (partial or full): {len(partials)} ({len(partials)/max(total,1)*100:.1f}%)")

    # Domain-level obstruction
    domain_obs = defaultdict(lambda: {"total": 0, "obstruction": 0})
    for r in rows:
        d = r["domain"]
        domain_obs[d]["total"] += 1
        if r["mapping_status"] in OBSTRUCTION_STATUSES:
            domain_obs[d]["obstruction"] += 1

    print(f"\n  Obstruction by domain:")
    for d in sorted(domain_obs, key=lambda x: -domain_obs[x]["obstruction"]/max(domain_obs[x]["total"],1)):
        info = domain_obs[d]
        rate = info["obstruction"] / max(info["total"], 1) * 100
        print(f"    {d}: {info['obstruction']}/{info['total']} ({rate:.1f}%)")

    # COLLISION details
    collisions = [r for r in rows if r["mapping_status"] == "COLLISION"]
    print(f"\n  COLLISION witnesses: {len(collisions)}")
    for c in collisions[:3]:
        print(f"    [{c['domain']}] {c['fact_summary'][:80]}...")

    # Rosetta theorem verdict
    print(f"\n  {'='*50}")
    if obstruction_density > 0.1:
        verdict = "OBSERVED: obstruction density > 10% — no universal total functor"
        print(f"  VERDICT: {verdict}")
    else:
        verdict = "LOW: obstruction density < 10% — universal claim weakened"
        print(f"  VERDICT: {verdict}")

    results = {
        "total": total,
        "obstruction_count": obstruction_count,
        "obstruction_density": round(obstruction_density, 4),
        "mappable_count": len(partials),
        "collision_count": len(collisions),
        "status_distribution": dict(statuses),
        "domain_obstruction": {d: dict(v) for d, v in domain_obs.items()},
        "verdict": verdict,
    }

    return results


# ============================================================
# T9.4: Banach Contraction Analysis
# ============================================================

def run_t94():
    print("\n" + "=" * 60)
    print("T9.4: Banach Contraction Analysis")
    print("=" * 60)

    with open(T94_PATH, encoding="utf-8-sig") as f:
        rows = list(csv.DictReader(f))

    total = len(rows)
    print(f"\n  Total rows: {total}")

    # Parse amounts
    parsed = []
    for r in rows:
        try:
            initial = float(r.get("initial_claim", 0) or 0)
            final = float(r.get("final_award", 0) or 0)
            iterations = int(r.get("iterations", 1) or 1)
            converged = r.get("converged", "").strip().lower() == "true"
            gap = float(r.get("convergence_gap", 0) or 0)
            if final > 0:
                # Filter CN ratio > 1: OCR extraction error (处分原则: award ≤ claim)
                juris = r.get("jurisdiction", "CN")
                ratio = final / max(initial, 1)
                if juris == "CN" and ratio > 1.0:
                    continue
                parsed.append({
                    "jurisdiction": juris,
                    "domain": r["domain"],
                    "damage_type": r["damage_type"],
                    "initial": initial,
                    "final": final,
                    "iterations": iterations,
                    "converged": converged,
                    "gap": gap,
                })
        except (ValueError, KeyError):
            continue

    print(f"  Parsed with amounts: {len(parsed)}")

    # Jurisdiction breakdown
    juris = Counter(r["jurisdiction"] for r in parsed)
    print(f"\n  By jurisdiction:")
    for j, c in juris.most_common():
        print(f"    {j}: {c}")

    # Convergence analysis
    with_iterations = [r for r in parsed if r["iterations"] >= 2]
    converged = [r for r in with_iterations if r["converged"]]
    print(f"\n  Multi-iteration cases: {len(with_iterations)}")
    print(f"  Converged (gap < 10%): {len(converged)}")
    if with_iterations:
        print(f"  Convergence rate: {len(converged)/len(with_iterations)*100:.1f}%")

    # Contraction ratio analysis
    # For cases with initial_claim and final_award, compute beta = final/initial
    banach_verdict = "INSUFFICIENT"
    ratios = []
    with_initial = [r for r in parsed if r["initial"] > 0 and r["final"] > 0]
    if with_initial:
        ratios = []
        for r in with_initial:
            ratio = r["final"] / r["initial"]
            if ratio <= 10:  # filter outliers
                ratios.append(ratio)

        if ratios:
            mean_ratio = sum(ratios) / len(ratios)
            sorted_ratios = sorted(ratios)
            median_ratio = sorted_ratios[len(sorted_ratios) // 2]
            print(f"\n  Contraction ratio (final/initial):")
            print(f"    Cases: {len(ratios)}")
            print(f"    Mean: {mean_ratio:.4f}")
            print(f"    Median: {median_ratio:.4f}")
            print(f"    Range: [{sorted_ratios[0]:.4f}, {sorted_ratios[-1]:.4f}]")

            # Estimate contraction factor beta
            # If price_{n+1} = beta * target + (1-beta) * price_n
            # After 1 iteration: ratio = beta * target/initial + (1-beta)
            # For converged cases, ratio < 1 means contraction
            under_one = sum(1 for r in ratios if r < 1.0)
            over_one = sum(1 for r in ratios if r > 1.0)
            exactly_one = sum(1 for r in ratios if r == 1.0)
            print(f"    < 1.0 (claim reduced): {under_one} ({under_one/len(ratios)*100:.1f}%)")
            print(f"    > 1.0 (claim increased): {over_one} ({over_one/len(ratios)*100:.1f}%)")
            print(f"    = 1.0 (no change): {exactly_one} ({exactly_one/len(ratios)*100:.1f}%)")

            # Per-jurisdiction contraction
            print(f"\n  Contraction by jurisdiction:")
            for juris_name in ["CN", "US", "HK"]:
                juris_ratios = [r["final"]/r["initial"] for r in with_initial
                               if r["jurisdiction"] == juris_name and r["initial"] > 0
                               and r["final"]/r["initial"] <= 10]
                if juris_ratios:
                    mean_r = sum(juris_ratios) / len(juris_ratios)
                    med_r = sorted(juris_ratios)[len(juris_ratios)//2]
                    print(f"    {juris_name}: n={len(juris_ratios)}, mean={mean_r:.4f}, median={med_r:.4f}")

            # Banach contraction check
            # A contraction mapping has beta < 1
            if median_ratio < 1.0:
                banach_verdict = "OBSERVED: median ratio < 1.0 — empirical contraction signal"
            else:
                banach_verdict = "NOT OBSERVED: median ratio >= 1.0 — no empirical contraction"
            print(f"\n  {'='*50}")
            print(f"  VERDICT: {banach_verdict}")
    else:
        banach_verdict = "INSUFFICIENT: no cases with both initial and final amounts"
        ratios = []
        print(f"\n  {'='*50}")
        print(f"  VERDICT: {banach_verdict}")

    results = {
        "total": total,
        "parsed": len(parsed),
        "multi_iteration": len(with_iterations),
        "converged": len(converged),
        "convergence_rate": round(len(converged)/max(len(with_iterations),1), 4),
        "with_initial": len(with_initial) if with_initial else 0,
        "mean_ratio": round(sum(ratios)/len(ratios), 4) if ratios else None,
        "median_ratio": round(sorted(ratios)[len(ratios)//2], 4) if ratios else None,
        "jurisdiction_breakdown": dict(juris),
        "verdict": banach_verdict if with_initial else "INSUFFICIENT",
    }

    return results


# ============================================================
# Main
# ============================================================

def main():
    start = time.time()

    t85 = run_t85()
    t94 = run_t94()

    elapsed = time.time() - start

    # Save results
    out_dir = Path("reports/verification")
    out_dir.mkdir(parents=True, exist_ok=True)
    out_path = out_dir / "t85_t94_results.json"
    with open(out_path, "w", encoding="utf-8") as f:
        json.dump({"T8.5": t85, "T9.4": t94, "runtime_seconds": round(elapsed, 2)},
                  f, indent=2, ensure_ascii=False)

    print(f"\n{'=' * 60}")
    print(f"Results: {out_path}")
    print(f"Runtime: {elapsed:.2f}s")
    print(f"{'=' * 60}")


if __name__ == "__main__":
    main()
