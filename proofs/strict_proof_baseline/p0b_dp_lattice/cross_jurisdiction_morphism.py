# -*- coding: utf-8 -*-
"""
Theorem B2: No cross-jurisdiction privilege-to-epsilon order-preserving morphism

Claim: There exists no strictly order-preserving map φ from the union of
CN, US, and HK privilege levels to ℝ that respects semantic correspondence,
because CN and US have incompatible order structures (ascending vs descending)
for semantically equivalent levels.

Status target: REFUTED_BY_COUNTEREXAMPLE (non-existence proved)
"""

from z3 import Solver, Real, sat, unsat, unknown

def main():
    print("=" * 60)
    print("Theorem B2: Cross-jurisdiction privilege morphism")
    print("=" * 60)

    n = 10

    # CN privilege levels: c0 < c1 < ... < c9 (ascending chain)
    # US privilege levels: u0 > u1 > ... > u9 (descending chain)
    # HK privilege levels: h0 < h1 < ... < h9 (ascending chain)

    # phi values for all 30 levels (mapped to Real)
    phi_cn = [Real(f'phi_cn_{i}') for i in range(n)]
    phi_us = [Real(f'phi_us_{i}') for i in range(n)]
    phi_hk = [Real(f'phi_hk_{i}') for i in range(n)]

    s = Solver()

    # --- Semantic correspondence: same privilege level maps to same real value ---
    for i in range(n):
        s.add(phi_cn[i] == phi_us[i])
        s.add(phi_cn[i] == phi_hk[i])

    # --- Strict order preservation within each jurisdiction ---
    # CN: c_i < c_{i+1}  =>  phi(c_i) < phi(c_{i+1})
    for i in range(n - 1):
        s.add(phi_cn[i] < phi_cn[i + 1])

    # US: u_i > u_{i+1}  =>  phi(u_i) > phi(u_{i+1})
    # (strict order preservation requires strict inequality)
    for i in range(n - 1):
        s.add(phi_us[i] > phi_us[i + 1])

    # HK: h_i < h_{i+1}  =>  phi(h_i) < phi(h_{i+1})
    for i in range(n - 1):
        s.add(phi_hk[i] < phi_hk[i + 1])

    # --- Check satisfiability ---
    result = s.check()
    print(f"Z3 result: {result}")

    if result == unsat:
        print("\n[RESULT] REFUTED_BY_COUNTEREXAMPLE")
        print("No strictly order-preserving cross-jurisdiction morphism exists.")
        print("Reason: CN and US have opposite order directions for")
        print("semantically equivalent levels, forcing phi(c0) < phi(c1)")
        print("and simultaneously phi(c0) > phi(c1).")
    elif result == sat:
        print("\n[RESULT] PROVED_SMT_FINITE")
        print("Unexpected: Z3 found a model. Printing model...")
        m = s.model()
        for i in range(n):
            print(f"  phi(CN_{i}) = {m[phi_cn[i]]}")
    else:
        print(f"\n[RESULT] OPEN_CONJECTURE")
        print("Z3 returned unknown.")

    print("=" * 60)
    return result

if __name__ == "__main__":
    main()
