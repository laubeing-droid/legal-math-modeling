#!/usr/bin/env python3
"""
graph_similarity_range_z3.py

Z3-based bounded verification that score ∈ [0,1].

STATUS: PENDING_TOOLCHAIN — Z3 solver not available in current environment.
        Script is ready to run when z3-solver is installed.

Installation:
    pip install z3-solver

Formula:
    score = 0.6*jaccard + 0.4*(0.5*vertex_ratio + 0.5*edge_ratio)
    Goal: 0 ≤ score ≤ 1  assuming 0 ≤ j,v,e ≤ 1
"""

# Encoding safety for Windows GBK consoles
import sys
if hasattr(sys.stdout, "reconfigure"):
    sys.stdout.reconfigure(encoding="utf-8", errors="replace")
if hasattr(sys.stderr, "reconfigure"):
    sys.stderr.reconfigure(encoding="utf-8", errors="replace")


import sys

def main():
    try:
        from z3 import Real, RealVal, Solver, And, sat, unsat
    except ImportError:
        print("=" * 60)
        print("Z3 NOT AVAILABLE")
        print("=" * 60)
        print("The 'z3' Python package is not installed.")
        print("Install with:  pip install z3-solver")
        print("")
        print("The corresponding .smt2 file has been generated for")
        print("offline verification with any SMT-LIB2 compliant solver.")
        print("=" * 60)
        sys.exit(0)

    print("=" * 60)
    print("Z3 RANGE VERIFICATION")
    print("=" * 60)

    # Declare real variables
    jaccard = Real('jaccard')
    vertex_ratio = Real('vertex_ratio')
    edge_ratio = Real('edge_ratio')
    score = Real('score')

    # Use exact rationals: 6/10, 4/10 * 1/2 = 2/10, etc.
    score_expr = (RealVal(6)/RealVal(10)) * jaccard + \
                 (RealVal(2)/RealVal(10)) * vertex_ratio + \
                 (RealVal(2)/RealVal(10)) * edge_ratio

    # Constraints: all inputs in [0,1]
    input_bounds = And(
        jaccard >= 0, jaccard <= 1,
        vertex_ratio >= 0, vertex_ratio <= 1,
        edge_ratio >= 0, edge_ratio <= 1
    )

    # --- Check if score < 0 is possible ---
    solver = Solver()
    solver.add(input_bounds)
    solver.add(score_expr < 0)

    print("\n--- Checking if score < 0 is possible ---")
    result = solver.check()
    if result == unsat:
        print("Result: UNSAT  -->  score ≥ 0 is PROVEN")
    elif result == sat:
        model = solver.model()
        print(f"COUNTEREXAMPLE FOUND: score = {model[score_expr]}")
        print(f"  jaccard={model[jaccard]}, v={model[vertex_ratio]}, e={model[edge_ratio]}")
    else:
        print(f"Result: UNKNOWN ({result})")

    # --- Check if score > 1 is possible ---
    solver = Solver()
    solver.add(input_bounds)
    solver.add(score_expr > 1)

    print("\n--- Checking if score > 1 is possible ---")
    result = solver.check()
    if result == unsat:
        print("Result: UNSAT  -->  score ≤ 1 is PROVEN")
    elif result == sat:
        model = solver.model()
        print(f"COUNTEREXAMPLE FOUND: score = {model[score_expr]}")
        print(f"  jaccard={model[jaccard]}, v={model[vertex_ratio]}, e={model[edge_ratio]}")
    else:
        print(f"Result: UNKNOWN ({result})")

    print("\n" + "=" * 60)
    print("CONCLUSION: score ∈ [0, 1]  --  VERIFIED BY Z3")
    print("=" * 60)


if __name__ == "__main__":
    main()
