#!/usr/bin/env python3
"""
finite_galois_adjunction.py

Exhaustive finite-domain verification of the reverse-index incidence Galois connection.

Author: Proof Agent
Date: 2025-06-11

PROBLEM STATEMENT:
------------------
Given finite sets D (domain) and Atom, and an arbitrary function
    alpha_one: D -> P(Atom)

Define:
    gamma_one(a) = { d ∈ D | a ∈ alpha_one(d) }
    Alpha(S)     = ⋃ { alpha_one(d) | d ∈ S }     for S ⊆ D
    Gamma(B)     = { d ∈ D | alpha_one(d) ⊆ B }   for B ⊆ Atom

THEOREMS TO PROVE:
1. Incidence Theorem:
       ∀ d ∈ D, ∀ a ∈ Atom:  a ∈ alpha_one(d)  ⇔  d ∈ gamma_one(a)

2. Powerset Galois Connection:
       ∀ S ⊆ D, ∀ B ⊆ Atom:  Alpha(S) ⊆ B  ⇔  S ⊆ Gamma(B)

VERIFICATION STRATEGY:
----------------------
For each (|D|, |Atom|) pair with |D| ≤ MAX_D and |Atom| ≤ MAX_ATOM:
  1. Label D = {0, ..., |D|-1}, Atom = {0, ..., |Atom|-1}.
  2. Enumerate ALL possible alpha_one functions.
     Total count = (2^|Atom|)^|D| = 2^(|D|·|Atom|).
  3. For each alpha_one:
       a. Compute gamma_one.
       b. Verify Theorem 1 (incidence) for every (d, a) pair.
       c. Compute Alpha and Gamma.
       d. Verify Theorem 2 (Galois connection) for every (S, B) pair.
  4. Report: total fixtures checked, per-size breakdown.

If ANY assertion fails, script exits with non-zero status.

LIMITATIONS:
- Exhaustive only for the stated finite bounds.
- NOT a proof for infinite domains.
- Domain elements are abstract integers (0, 1, 2, ...).
"""

# Encoding safety for Windows GBK consoles
import sys
if hasattr(sys.stdout, "reconfigure"):
    sys.stdout.reconfigure(encoding="utf-8", errors="replace")
if hasattr(sys.stderr, "reconfigure"):
    sys.stderr.reconfigure(encoding="utf-8", errors="replace")


import sys
from itertools import product, combinations

# ============================================================
# CONFIGURATION
# ============================================================
MAX_D = 4       # maximum |D| (domain size)
MAX_ATOM = 4    # maximum |Atom| (atom set size)

# ============================================================
# SET UTILITIES (treating sets as frozensets for hashing)
# ============================================================

def all_subsets(universe):
    """Return list of all subsets of `universe` (a set of ints)."""
    elems = sorted(universe)
    result = []
    for r in range(len(elems) + 1):
        for combo in combinations(elems, r):
            result.append(frozenset(combo))
    return result


def powerset_list(universe):
    """Return list of all subsets as frozensets."""
    return all_subsets(universe)


# ============================================================
# CORE DEFINITIONS
# ============================================================

def compute_gamma_one(alpha_one, D_set, Atom_set):
    """
    Given alpha_one: D -> P(Atom), compute gamma_one: Atom -> P(D).
    gamma_one(a) = { d ∈ D | a ∈ alpha_one(d) }
    """
    gamma = {}
    for a in Atom_set:
        gamma[a] = frozenset({d for d in D_set if a in alpha_one[d]})
    return gamma


def compute_Alpha(alpha_one, S):
    """
    Alpha(S) = ⋃ { alpha_one(d) | d ∈ S }
    """
    result = set()
    for d in S:
        result |= alpha_one[d]
    return frozenset(result)


def compute_Gamma(alpha_one, B, D_set):
    """
    Gamma(B) = { d ∈ D | alpha_one(d) ⊆ B }
    """
    return frozenset({d for d in D_set if alpha_one[d] <= B})


# ============================================================
# ENUMERATION HELPERS
# ============================================================

def enumerate_all_alpha_one(D_set, Atom_set):
    """
    Enumerate ALL possible functions alpha_one: D -> P(Atom).
    Yield dictionaries {d: frozenset_of_atoms}.
    """
    D_list = sorted(D_set)
    Atom_list = sorted(Atom_set)
    all_atom_subsets = all_subsets(Atom_set)
    # For each d in D, pick one subset of Atom
    for assignment in product(all_atom_subsets, repeat=len(D_list)):
        yield {d: subset for d, subset in zip(D_list, assignment)}


# ============================================================
# THEOREM VERIFICATION
# ============================================================

def verify_incidence_theorem(alpha_one, gamma_one, D_set, Atom_set):
    """
    Theorem 1: ∀ d ∈ D, ∀ a ∈ Atom:
        a ∈ alpha_one(d)  ⇔  d ∈ gamma_one(a)
    Returns True if holds, False otherwise.
    """
    for d in D_set:
        for a in Atom_set:
            left = a in alpha_one[d]
            right = d in gamma_one[a]
            if left != right:
                print(f"  [FAIL] Incidence: d={d}, a={a}, "
                      f"a∈alpha(d)={left}, d∈gamma(a)={right}",
                      file=sys.stderr)
                return False
    return True


def verify_galois_connection(alpha_one, D_set, Atom_set):
    """
    Theorem 2: ∀ S ⊆ D, ∀ B ⊆ Atom:
        Alpha(S) ⊆ B  ⇔  S ⊆ Gamma(B)
    Returns True if holds, False otherwise.
    """
    all_D_subsets = powerset_list(D_set)
    all_Atom_subsets = powerset_list(Atom_set)

    for S in all_D_subsets:
        alpha_S = compute_Alpha(alpha_one, S)
        for B in all_Atom_subsets:
            left = alpha_S <= B
            gamma_B = compute_Gamma(alpha_one, B, D_set)
            right = S <= gamma_B
            if left != right:
                print(f"  [FAIL] Galois: S={set(S)}, B={set(B)}, "
                      f"Alpha(S)={set(alpha_S)}, "
                      f"Alpha(S)⊆B={left}, "
                      f"Gamma(B)={set(gamma_B)}, "
                      f"S⊆Gamma(B)={right}",
                      file=sys.stderr)
                return False
    return True


# ============================================================
# MAIN VERIFICATION LOOP
# ============================================================

def main():
    print("=" * 70)
    print("FINITE-DOMAIN GALOIS CONNECTION EXHAUSTIVE VERIFICATION")
    print("=" * 70)
    print(f"Max |D|    = {MAX_D}")
    print(f"Max |Atom| = {MAX_ATOM}")
    print()

    total_fixtures = 0
    all_passed = True
    results = []

    for n_d in range(1, MAX_D + 1):
        for n_atom in range(1, MAX_ATOM + 1):
            D_set = frozenset(range(n_d))
            Atom_set = frozenset(range(n_atom))

            count_alpha = (2 ** n_atom) ** n_d  # = 2^(n_d * n_atom)
            fixtures_checked = 0
            passed = True

            print(f"--- |D|={n_d}, |Atom|={n_atom} "
                  f"(alpha_one count = 2^{n_d*n_atom} = {count_alpha}) ---")

            for alpha_one in enumerate_all_alpha_one(D_set, Atom_set):
                fixtures_checked += 1

                # 1. Compute gamma_one
                gamma_one = compute_gamma_one(alpha_one, D_set, Atom_set)

                # 2. Verify incidence theorem
                if not verify_incidence_theorem(alpha_one, gamma_one,
                                                 D_set, Atom_set):
                    all_passed = False
                    passed = False
                    break

                # 3. Verify powerset Galois connection
                if not verify_galois_connection(alpha_one, D_set, Atom_set):
                    all_passed = False
                    passed = False
                    break

            total_fixtures += fixtures_checked
            results.append((n_d, n_atom, fixtures_checked, passed))

            status = "PASS" if passed else "FAIL"
            print(f"  Fixtures checked: {fixtures_checked}")
            print(f"  Status: {status}")
            print()

            if not passed:
                break

        if not all_passed:
            break

    # ============================================================
    # SUMMARY REPORT
    # ============================================================
    print("=" * 70)
    print("SUMMARY")
    print("=" * 70)
    print(f"{'|D|':>3} | {'|Atom|':>6} | {'Fixtures':>10} | {'Status':>6}")
    print("-" * 35)
    for n_d, n_atom, fc, passed in results:
        status = "PASS" if passed else "FAIL"
        print(f"{n_d:>3} | {n_atom:>6} | {fc:>10} | {status:>6}")
    print("-" * 35)
    print(f"TOTAL fixtures checked: {total_fixtures}")
    print()

    if all_passed:
        print("RESULT: ALL THEOREMS VERIFIED for all enumerated fixtures.")
        print("Status: EXHAUSTIVE_FINITE_PROOF")
        print()
        print("NOTE: This is an exhaustive check over all finite domains")
        print("      with |D| ≤ {} and |Atom| ≤ {}.".format(MAX_D, MAX_ATOM))
        print("      It does NOT constitute a proof for infinite domains.")
        sys.exit(0)
    else:
        print("RESULT: VERIFICATION FAILED for at least one fixture.",
              file=sys.stderr)
        sys.exit(1)


if __name__ == "__main__":
    main()
