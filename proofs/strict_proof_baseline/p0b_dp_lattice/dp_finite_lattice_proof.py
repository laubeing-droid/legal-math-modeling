# -*- coding: utf-8 -*-
"""
Theorem B1: Galois connection on CN finite bounded lattice

Claim: No Galois connection (α, γ) exists between a finite bounded lattice
(with bottom ⊥ and top ⊤) and the real numbers ℝ (with standard order),
because ℝ lacks a bottom element, making α(⊥) undefined in ℝ.

Status target: REFUTED_BY_COUNTEREXAMPLE (non-existence proved)
"""

from z3 import Solver, Real, Int, ForAll, Implies, And, Or, sat, unsat, unknown

def main():
    print("=" * 60)
    print("Theorem B1: Galois connection on CN finite bounded lattice")
    print("=" * 60)

    # 10 CN privilege levels, represented as integers 0..9
    # We model them as a chain (total order) for simplicity.
    # The impossibility result holds for ANY bounded lattice.
    n = 10
    levels = list(range(n))

    # alpha: Level -> Real (one real variable per level)
    alpha = [Real(f'alpha_{i}') for i in levels]

    # gamma at witness real points (we only need one witness)
    r_bot = Real('r_bot')
    gamma_bot = Int('gamma_bot')

    s = Solver()

    # --- Lattice structure: chain 0 < 1 < ... < 9 ---
    # Monotonicity of alpha: i <= j implies alpha_i <= alpha_j
    for i in levels:
        for j in levels:
            if i <= j:
                s.add(alpha[i] <= alpha[j])

    # --- Bounded lattice axioms ---
    # Level 0 is the bottom element: forall p, 0 <= p (in lattice order)
    # Level 9 is the top element: forall p, p <= 9 (in lattice order)
    # For our chain encoding, these are tautologically true (0 <= i <= 9).
    # We encode the bottom property explicitly for the Galois proof.

    # --- Galois connection condition (partial instantiation) ---
    # The full condition is: forall p, r. alpha(p) <= r  <->  p <= gamma(r)
    # We instantiate at p = 0 (bottom) and r = r_bot.
    # Because 0 is bottom, 0 <= gamma_bot is TRUE for any gamma_bot.
    # Therefore alpha_0 <= r_bot must be TRUE.
    s.add(0 <= gamma_bot)          # bottom property: 0 <= anything
    s.add(alpha[0] <= r_bot)       # follows from Galois condition

    # --- Witness construction ---
    # Let r_bot = alpha_0 - 1. Then alpha_0 <= alpha_0 - 1 is false in ℝ,
    # yielding a contradiction.
    s.add(r_bot == alpha[0] - 1)

    # --- Check satisfiability ---
    result = s.check()
    print(f"Z3 result: {result}")

    if result == unsat:
        print("\n[RESULT] REFUTED_BY_COUNTEREXAMPLE")
        print("No Galois connection exists between a finite bounded lattice and Real.")
        print("Reason: Real has no bottom element, so alpha(bottom) cannot be defined.")
        print("The witness r = alpha(bottom) - 1 violates the Galois condition.")
    elif result == sat:
        print("\n[RESULT] PROVED_SMT_FINITE")
        print("Unexpected: Z3 found a model. Printing model...")
        m = s.model()
        for i in levels:
            print(f"  alpha({i}) = {m[alpha[i]]}")
        print(f"  r_bot = {m[r_bot]}")
        print(f"  gamma_bot = {m[gamma_bot]}")
    else:
        print(f"\n[RESULT] OPEN_CONJECTURE")
        print("Z3 returned unknown.")

    print("=" * 60)
    return result

if __name__ == "__main__":
    main()
