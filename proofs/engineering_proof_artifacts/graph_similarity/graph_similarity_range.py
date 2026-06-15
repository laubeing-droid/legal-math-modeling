#!/usr/bin/env python3
"""
graph_similarity_range.py

Prove: score = 0.6*jaccard + 0.4*size_ratio ∈ [0,1]
       where size_ratio = 0.5*vertex_ratio + 0.5*edge_ratio

Methods:
  1. Symbolic proof via SymPy (exact arithmetic)
  2. Exhaustive enumeration over fine-grained grid

Author: Auto-generated proof artifact
"""

# Encoding safety for Windows GBK consoles
import sys
if hasattr(sys.stdout, "reconfigure"):
    sys.stdout.reconfigure(encoding="utf-8", errors="replace")
if hasattr(sys.stderr, "reconfigure"):
    sys.stderr.reconfigure(encoding="utf-8", errors="replace")


from sympy import symbols, Rational, simplify, And, Q
from sympy import ask, Interval
from itertools import product

# ============================================================
# 1. SYMBOLIC PROOF
# ============================================================

def symbolic_range_proof():
    """
    Symbolic proof that score ∈ [0,1] given all inputs ∈ [0,1].
    Uses exact rational arithmetic via SymPy.
    """
    print("=" * 60)
    print("PART 1: SYMBOLIC RANGE PROOF")
    print("=" * 60)

    # Define symbolic variables
    jaccard, vertex_ratio, edge_ratio = symbols(
        'jaccard vertex_ratio edge_ratio', real=True
    )

    # Define the score formula with exact Rational coefficients
    w_j = Rational(6, 10)   # 0.6
    w_v = Rational(4, 10) * Rational(1, 2)  # 0.4 * 0.5 = 0.2
    w_e = Rational(4, 10) * Rational(1, 2)  # 0.4 * 0.5 = 0.2

    score = w_j * jaccard + w_v * vertex_ratio + w_e * edge_ratio

    print(f"Score formula:")
    print(f"  score = {w_j}*jaccard + {w_v}*vertex_ratio + {w_e}*edge_ratio")
    print(f"  score = {simplify(score)}")

    # Weights sum to 1
    total_weight = w_j + w_v + w_e
    print(f"\nTotal weight = {total_weight} = {float(total_weight)}")
    assert total_weight == 1, "Weights must sum to 1"

    # Proof that score ∈ [0,1]:
    # Since all weights are non-negative and sum to 1,
    # score is a convex combination of jaccard, vertex_ratio, edge_ratio.
    # If each variable ∈ [0,1], then:
    #   min(score) = 0 (when all vars = 0)
    #   max(score) = 1 (when all vars = 1)

    print("\n--- Proof Structure ---")
    print("score = 0.6*jaccard + 0.2*vertex_ratio + 0.2*edge_ratio")
    print("All weights (0.6, 0.2, 0.2) are non-negative and sum to 1.0")
    print("Therefore score is a CONVEX COMBINATION of the three ratios.")
    print("\nFor any convex combination with all inputs in [0,1]:")
    print("  - Minimum value = 0 (achieved when all inputs = 0)")
    print("  - Maximum value = 1 (achieved when all inputs = 1)")

    # Verify with SymPy
    score_min = score.subs([(jaccard, 0), (vertex_ratio, 0), (edge_ratio, 0)])
    score_max = score.subs([(jaccard, 1), (vertex_ratio, 1), (edge_ratio, 1)])

    print(f"\n--- SymPy Verification ---")
    print(f"score(0,0,0) = {score_min} = {float(score_min)}")
    print(f"score(1,1,1) = {score_max} = {float(score_max)}")

    # Check partial derivatives to confirm monotonicity
    d_score_dj = simplify(score.diff(jaccard))
    d_score_dv = simplify(score.diff(vertex_ratio))
    d_score_de = simplify(score.diff(edge_ratio))

    print(f"\n--- Partial Derivatives (Monotonicity) ---")
    print(f"∂score/∂jaccard      = {d_score_dj}  (non-negative: {float(d_score_dj) >= 0})")
    print(f"∂score/∂vertex_ratio = {d_score_dv}  (non-negative: {float(d_score_dv) >= 0})")
    print(f"∂score/∂edge_ratio   = {d_score_de}  (non-negative: {float(d_score_de) >= 0})")

    all_nonneg = all(float(d) >= 0 for d in [d_score_dj, d_score_dv, d_score_de])
    assert all_nonneg, "All partial derivatives must be non-negative"

    print("\n*** SYMBOLIC PROOF CONCLUSION ***")
    print("Since score is monotonically increasing in each variable")
    print("(all partial derivatives ≥ 0), and each variable ∈ [0,1],")
    print("the range of score is [0, 1].  QED.")
    print("=" * 60)

    return True


# ============================================================
# 2. EXHAUSTIVE ENUMERATION PROOF
# ============================================================

def exhaustive_range_proof(steps=21):
    """
    Exhaustive enumeration over a fine grid.
    steps=21 means grid points at 0.0, 0.05, 0.10, ..., 1.0
    """
    print("\n" + "=" * 60)
    print("PART 2: EXHAUSTIVE ENUMERATION PROOF")
    print("=" * 60)
    print(f"Grid resolution: {steps} points per dimension")
    print(f"Total combinations: {steps**3}")

    grid = [i / (steps - 1) for i in range(steps)]

    min_score = float('inf')
    max_score = float('-inf')
    min_config = None
    max_config = None

    for j, v, e in product(grid, repeat=3):
        score = 0.6 * j + 0.4 * (0.5 * v + 0.5 * e)

        if score < min_score:
            min_score = score
            min_config = (j, v, e)
        if score > max_score:
            max_score = score
            max_config = (j, v, e)

    print(f"\n--- Results ---")
    print(f"Minimum score: {min_score:.10f} at (j,v,e) = {min_config}")
    print(f"Maximum score: {max_score:.10f} at (j,v,e) = {max_config}")

    eps = 1e-10
    assert -eps <= min_score <= eps, f"Min score should be ~0, got {min_score}"
    assert 1 - eps <= max_score <= 1 + eps, f"Max score should be ~1, got {max_score}"

    print("\n*** EXHAUSTIVE PROOF CONCLUSION ***")
    print(f"All {steps**3} grid combinations produce score ∈ [0, 1]")
    print("Range [0, 1] VERIFIED.  QED.")
    print("=" * 60)

    return min_score, max_score


# ============================================================
# 3. BOUNDARY CASE ANALYSIS
# ============================================================

def boundary_analysis():
    """
    Analyze extreme/boundary cases of the score formula.
    """
    print("\n" + "=" * 60)
    print("PART 3: BOUNDARY CASE ANALYSIS")
    print("=" * 60)

    cases = [
        ("All zero", 0, 0, 0),
        ("All one", 1, 1, 1),
        ("Only jaccard", 1, 0, 0),
        ("Only vertex_ratio", 0, 1, 0),
        ("Only edge_ratio", 0, 0, 1),
        ("Mixed: j=0.5, v=0.5, e=0.5", 0.5, 0.5, 0.5),
        ("Mixed: j=1, v=0, e=1", 1, 0, 1),
        ("Mixed: j=0, v=1, e=0", 0, 1, 0),
    ]

    print(f"{'Case':<30} {'Score':>10}")
    print("-" * 45)
    for name, j, v, e in cases:
        score = 0.6 * j + 0.4 * (0.5 * v + 0.5 * e)
        print(f"{name:<30} {score:>10.4f}")

    print("\n" + "=" * 60)


# ============================================================
# MAIN
# ============================================================

if __name__ == "__main__":
    print("\n" + "#" * 60)
    print("# GRAPH SIMILARITY SCORE RANGE PROOF")
    print("# score = 0.6*jaccard + 0.4*size_ratio")
    print("#         where size_ratio = 0.5*vertex_ratio + 0.5*edge_ratio")
    print("#" * 60 + "\n")

    # Run all proofs
    symbolic_range_proof()
    exhaustive_range_proof(steps=21)
    boundary_analysis()

    print("\n" + "#" * 60)
    print("# FINAL RESULT: score ∈ [0, 1]  --  PROVEN")
    print("#" * 60)
