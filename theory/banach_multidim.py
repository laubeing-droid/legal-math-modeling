#!/usr/bin/env python3
"""
Banach Multi-Dimensional Contraction
=====================================

Extends the scalar Banach contraction to vector-valued pricing:
  price_{n+1} = beta * target + (1 - beta) * price_n

where beta ∈ (0,1) is the contraction factor and operations are vectorized.

Validates against T9.4 damages data (1,091 cases across CN/US/HK).
"""

import json
import csv
import math
from pathlib import Path
from typing import List, Dict, Tuple, Optional

try:
    import numpy as np
    HAS_NUMPY = True
except ImportError:
    HAS_NUMPY = False


def banach_iterate_vec(price: 'np.ndarray', target: 'np.ndarray',
                       beta: float, n: int) -> 'np.ndarray':
    """Multi-dimensional Banach contraction iteration.

    price_{k+1} = beta * target + (1 - beta) * price_k

    Args:
        price: Initial price vector (d-dimensional)
        target: Target price vector (d-dimensional)
        beta: Contraction factor in (0, 1)
        n: Number of iterations

    Returns:
        Price vector after n iterations
    """
    if not HAS_NUMPY:
        raise ImportError("numpy required for vector operations")
    p = np.array(price, dtype=float)
    t = np.array(target, dtype=float)
    for _ in range(n):
        p = beta * t + (1 - beta) * p
    return p


def convergence_rate(beta: float, n: int) -> float:
    """Compute theoretical convergence rate: beta^n."""
    return beta ** n


def estimate_beta_from_data(ratios: List[float]) -> Tuple[float, float]:
    """Estimate contraction factor beta from observed final/initial ratios.

    If final = beta * target + (1 - beta) * initial, and target ≈ 0
    (claims tend toward zero), then ratio ≈ (1 - beta).

    Returns: (beta_estimate, std_error)
    """
    if not HAS_NUMPY:
        raise ImportError("numpy required")
    r = np.array(ratios)
    # beta = 1 - mean(ratio) when target ≈ 0
    beta_est = 1.0 - np.mean(r)
    # Bootstrap standard error
    n_bootstrap = 1000
    betas = []
    for _ in range(n_bootstrap):
        sample = np.random.choice(r, size=len(r), replace=True)
        betas.append(1.0 - np.mean(sample))
    std_err = np.std(betas)
    return float(beta_est), float(std_err)


def multi_jurisdiction_contraction(data_path: str) -> dict:
    """Analyze multi-dimensional Banach contraction across jurisdictions.

    Each jurisdiction (CN/US/HK) is a dimension. The contraction mapping
    operates on the vector [price_CN, price_US, price_HK].

    Args:
        data_path: Path to T9.4_merged_clean.csv

    Returns:
        Analysis results dict
    """
    if not HAS_NUMPY:
        return {"error": "numpy not installed"}

    # Load data
    with open(data_path, encoding="utf-8-sig") as f:
        rows = list(csv.DictReader(f))

    # Group by jurisdiction
    # CN filtering: 处分原则 applies to civil (contract/tort) but NOT to
    # IP (punitive damages allowed) or criminal/admin (different rules).
    CIVIL_DOMAINS = {"contract", "tort"}
    PROCEDURE_DOMAINS = {"procedure"}
    juris_data = {"CN": [], "US": [], "HK": []}
    for r in rows:
        juris = r.get("jurisdiction", "CN")
        domain = r.get("domain", "")
        try:
            initial = float(r.get("initial_claim", 0) or 0)
            final = float(r.get("final_award", 0) or 0)
            if initial > 0 and final > 0:
                ratio = final / initial
                # CN civil: filter ratio > 1 (处分原则)
                if juris == "CN" and domain in CIVIL_DOMAINS and ratio > 1.0:
                    continue
                # CN procedure: exclude
                if juris == "CN" and domain in PROCEDURE_DOMAINS:
                    continue
                if ratio <= 10:  # filter extreme outliers
                    juris_data.setdefault(juris, []).append(ratio)
        except (ValueError, KeyError):
            continue

    # Estimate beta per jurisdiction
    results = {}
    for juris, ratios in juris_data.items():
        if len(ratios) < 5:
            continue
        beta, se = estimate_beta_from_data(ratios)
        r = np.array(ratios)
        results[juris] = {
            "n": len(ratios),
            "mean_ratio": float(np.mean(r)),
            "median_ratio": float(np.median(r)),
            "beta_estimate": round(beta, 4),
            "beta_std_error": round(se, 4),
            "convergence_to_zero": bool(beta > 0),
        }

    # Multi-dimensional contraction
    if len(results) >= 2:
        betas = [results[j]["beta_estimate"] for j in results]
        avg_beta = np.mean(betas)
        # Convergence rate: after 10 iterations, distance reduced by beta^10
        rate_10 = avg_beta ** 10
        results["multi_dim"] = {
            "dimensions": len(results),
            "avg_beta": round(float(avg_beta), 4),
            "convergence_rate_10_iter": round(float(rate_10), 6),
            "contractive": bool(avg_beta < 1.0),
        }

    return results


def main():
    import argparse
    parser = argparse.ArgumentParser(description="Banach Multi-Dimensional Contraction Analysis")
    parser.add_argument("--data", default="data/category_rosetta/T9.4_merged_clean.csv",
                        help="Path to T9.4 data CSV")
    args = parser.parse_args()

    print("=" * 60)
    print("Banach Multi-Dimensional Contraction Analysis")
    print("=" * 60)

    results = multi_jurisdiction_contraction(args.data)

    for juris, info in results.items():
        if juris == "multi_dim":
            print(f"\n{'='*50}")
            print(f"Multi-Dimensional:")
            for k, v in info.items():
                print(f"  {k}: {v}")
        else:
            print(f"\n{juris}: n={info['n']}")
            print(f"  mean_ratio: {info['mean_ratio']:.4f}")
            print(f"  median_ratio: {info['median_ratio']:.4f}")
            print(f"  beta_estimate: {info['beta_estimate']:.4f} ± {info['beta_std_error']:.4f}")
            print(f"  contractive: {info['convergence_to_zero']}")

    # Save results
    out_dir = Path("reports/verification")
    out_dir.mkdir(parents=True, exist_ok=True)
    out_path = out_dir / "banach_multidim_results.json"
    with open(out_path, "w", encoding="utf-8") as f:
        json.dump(results, f, indent=2, ensure_ascii=False)
    print(f"\nResults: {out_path}")


if __name__ == "__main__":
    main()
