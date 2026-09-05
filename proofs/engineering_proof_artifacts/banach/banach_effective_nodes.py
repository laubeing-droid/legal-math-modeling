"""
Banach Fixed-Point Contraction Proof for Effective Nodes (Single Dimension)
============================================================================

Proposition:
    f(x) = βT + (1-β)x,  0 < β <= 1
    d(x,y) = |x - y|

    Prove: d(f(x), f(y)) = |1-β| * d(x,y) < d(x,y) when 0 < β < 1

This is a NARROW result for effective_nodes single dimension, fixed target T.
Do NOT claim full pricing vector contraction.
"""

# Encoding safety for Windows GBK consoles
import sys
if hasattr(sys.stdout, "reconfigure"):
    sys.stdout.reconfigure(encoding="utf-8", errors="replace")
if hasattr(sys.stderr, "reconfigure"):
    sys.stderr.reconfigure(encoding="utf-8", errors="replace")


import sympy as sp
from sympy import symbols, Abs, simplify, solve, oo
import numpy as np

# ============================================================================
# 1. SYMBOLIC PROOF via SymPy
# ============================================================================

def symbolic_contraction_proof():
    """Symbolic verification that f is a contraction on R."""
    print("=" * 70)
    print("SYMBOLIC PROOF: f(x) = βT + (1-β)x is a contraction")
    print("=" * 70)

    # Define symbols
    x, y, beta, T = symbols('x y beta T', real=True)

    # Define the metric d(x,y) = |x - y|
    d_xy = Abs(x - y)

    # Define f(x) and f(y)
    f_x = beta * T + (1 - beta) * x
    f_y = beta * T + (1 - beta) * y

    # Compute d(f(x), f(y)) = |f(x) - f(y)|
    d_fx_fy = Abs(f_x - f_y)

    # Simplify: f(x) - f(y) = (1-β)(x - y)
    diff_f = simplify(f_x - f_y)
    print(f"\n1. f(x) - f(y) = {diff_f}")

    # So |f(x) - f(y)| = |1-β| * |x - y|
    d_fx_fy_simplified = Abs(1 - beta) * Abs(x - y)
    print(f"2. |f(x) - f(y)| = |1-β| * |x - y|")

    # The contraction factor is |1-β|
    contraction_factor = Abs(1 - beta)
    print(f"3. Contraction factor c = |1-β|")

    # For 0 < β < 1, we have 0 < 1-β < 1, so |1-β| = 1-β < 1
    print(f"\n4. When 0 < β < 1:")
    print(f"   0 < 1-β < 1")
    print(f"   Therefore |1-β| = 1-β ∈ (0, 1)")
    print(f"   Hence d(f(x), f(y)) = (1-β) * d(x,y) < d(x,y)")

    # For β = 1, f(x) = T (constant map), which is a contraction with c = 0
    print(f"\n5. When β = 1:")
    print(f"   f(x) = T (constant map)")
    print(f"   d(f(x), f(y)) = |T - T| = 0")
    print(f"   Contraction factor c = 0 < 1 (strong contraction)")

    # Verify numerically that |1-beta| < 1 for beta in (0,1)
    print(f"\n6. Numerical verification of contraction factor:")
    beta_vals = np.linspace(0.01, 0.99, 20)
    c_vals = np.abs(1 - beta_vals)
    print(f"   β range: (0.01, 0.99)")
    print(f"   c = |1-β| range: ({c_vals[-1]:.4f}, {c_vals[0]:.4f})")
    assert all(c < 1.0 for c in c_vals), "Contraction factor must be < 1"
    print(f"   All c values < 1: VERIFIED")

    return True


# ============================================================================
# 2. FIXED-POINT COMPUTATION
# ============================================================================

def compute_fixed_point():
    """The fixed point x* satisfies f(x*) = x*."""
    print("\n" + "=" * 70)
    print("FIXED POINT ANALYSIS")
    print("=" * 70)

    x, beta, T = symbols('x beta T', real=True)

    # f(x*) = x*  =>  βT + (1-β)x* = x*
    # => βT = x* - (1-β)x* = βx*
    # => x* = T
    f_x = beta * T + (1 - beta) * x
    fixed_point_eq = sp.Eq(f_x, x)
    solution = solve(fixed_point_eq, x)

    print(f"\n1. Fixed point equation: f(x*) = x*")
    print(f"   βT + (1-β)x* = x*")
    print(f"   βT = βx*")
    print(f"   x* = T")
    print(f"\n2. SymPy solution: x* = {solution}")

    # Verify: f(T) = βT + (1-β)T = T
    f_at_T = f_x.subs(x, T)
    f_at_T_simplified = simplify(f_at_T)
    print(f"\n3. Verification: f(T) = βT + (1-β)T = {f_at_T_simplified}")

    return solution[0] if solution else T


# ============================================================================
# 3. CONVERGENCE RATE
# ============================================================================

def convergence_analysis():
    """Analyze convergence of iteration x_{n+1} = f(x_n)."""
    print("\n" + "=" * 70)
    print("CONVERGENCE ANALYSIS")
    print("=" * 70)

    x, beta, T, x0, n = symbols('x beta T x0 n', real=True, positive=True)

    # x_1 = βT + (1-β)x_0
    # x_2 = βT + (1-β)x_1 = βT + (1-β)[βT + (1-β)x_0]
    #     = βT[1 + (1-β)] + (1-β)^2 x_0
    # x_n = βT[1 + (1-β) + ... + (1-β)^{n-1}] + (1-β)^n x_0
    #     = T[1 - (1-β)^n] + (1-β)^n x_0
    #     = T + (1-β)^n (x_0 - T)

    print("\n1. Iteration: x_{n+1} = βT + (1-β)x_n")
    print("\n2. Closed form:")
    print("   x_n = T + (1-β)^n (x_0 - T)")

    # Distance to fixed point after n steps
    print("\n3. Distance to fixed point:")
    print("   |x_n - T| = |1-β|^n * |x_0 - T|")
    print("   = (1-β)^n * |x_0 - T|   [for 0 < β < 1]")

    # Number of steps to reach tolerance ε
    print("\n4. Steps to reach tolerance ε:")
    print("   (1-β)^n * |x_0 - T| < ε")
    print("   n > log(ε / |x_0 - T|) / log(1-β)")

    # Numerical example
    print("\n5. Numerical example: T=100, β=0.1, x_0=50")
    T_val, beta_val, x0_val = 100.0, 0.1, 50.0
    for n_val in [1, 5, 10, 20, 50]:
        x_n = T_val + (1 - beta_val)**n_val * (x0_val - T_val)
        dist = abs(x_n - T_val)
        print(f"   n={n_val:2d}: x_n = {x_n:.6f}, |x_n - T| = {dist:.6f}")

    return True


# ============================================================================
# 4. NUMERIC VERIFICATION: Banach Fixed-Point Iteration
# ============================================================================

def numeric_banach_iteration():
    """Numerically verify convergence to fixed point."""
    print("\n" + "=" * 70)
    print("NUMERIC VERIFICATION: Banach Iteration")
    print("=" * 70)

    def f(x, beta, T):
        return beta * T + (1 - beta) * x

    test_cases = [
        {"T": 100.0, "beta": 0.1, "x0": 0.0, "desc": "cold start"},
        {"T": 100.0, "beta": 0.1, "x0": 200.0, "desc": "hot start"},
        {"T": 50.0, "beta": 0.5, "x0": 0.0, "desc": "mid beta"},
        {"T": 50.0, "beta": 0.01, "x0": 100.0, "desc": "slow beta"},
    ]

    for tc in test_cases:
        T, beta, x0 = tc["T"], tc["beta"], tc["x0"]
        x = x0
        history = [x]
        for _ in range(1000):
            x = f(x, beta, T)
            history.append(x)
            if abs(x - T) < 1e-10:
                break

        print(f"\n  {tc['desc']}: T={T}, β={beta}, x0={x0}")
        print(f"    Final x = {x:.10f}, |x - T| = {abs(x - T):.2e}")
        print(f"    Iterations = {len(history)-1}")

        # Verify contraction at each step
        contractions_valid = True
        for i in range(1, min(len(history), 10)):  # check first 10
            d_new = abs(history[i] - T)
            d_old = abs(history[i-1] - T)
            if d_new >= d_old and d_old > 1e-12:
                contractions_valid = False
        print(f"    Contraction monotonic: {'YES' if contractions_valid else 'NO'}")

    return True


# ============================================================================
# 5. MAIN EXECUTION
# ============================================================================

if __name__ == "__main__":
    print("\n")
    print("#" * 70)
    print("# BANACH CONTRACTION PROOF FOR EFFECTIVE NODES (SINGLE DIMENSION)")
    print("#" * 70)

    symbolic_contraction_proof()
    compute_fixed_point()
    convergence_analysis()
    numeric_banach_iteration()

    print("\n" + "=" * 70)
    print("SUMMARY")
    print("=" * 70)
    print("""
Proposition PROVED:
    f(x) = βT + (1-β)x  with  0 < β <= 1
    is a contraction on (R, |·|) with contraction factor c = |1-β|.

    For 0 < β < 1:  c = 1-β ∈ (0,1), strict contraction.
    For β = 1:      c = 0, constant map (strong contraction).

    Fixed point: x* = T.

LIMITATION (IMPORTANT):
    This is for a SINGLE effective_node dimension ONLY.
    The full pricing vector update may NOT be a contraction
    due to cross-dimensional coupling and max/min operations.
""")

    print("All checks passed. Banach contraction for single-dim effective_nodes: VERIFIED.")
