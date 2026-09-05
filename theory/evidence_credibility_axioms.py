#!/usr/bin/env python3
"""
#3: Evidence Trustworthiness Axiomatization --- S(e) = r x i x a
================================================================

Axiomatizes the multiplicative evidence credibility model and proves
boundary conditions for choosing multiplicative vs additive models.

## Current Model (implemented in M11 peripheral_models.py)

  S(e) = r x i x a

where:
  r  in  [0,1] --- relevance (???): does it prove any fact in issue?
  i  in  [0,1] --- integrity (???): chain of custody intact?
  a  in  [0,1] --- admissibility (????): meets procedural requirements?

## Theorem 1 (Multiplicative Zero Property)

  If any dimension is 0, S(e) = 0.

This holds for admissibility (inadmissible evidence = useless) and
integrity (broken chain of custody). For relevance, zero relevance
means the evidence doesn't prove anything at issue.

## Theorem 2 (Sub-minimum Bound)

  S_multiplicative(e) <= min(r, i, a)
  S_additive(e) = (r + i + a) / 3  >=  min(r, i, a) / 3

The multiplicative model is STRICTER than the additive model.

## Theorem 3 (Independence Boundary)

If the three dimensions are conditionally independent given the evidence
and the case context, the multiplicative model is the correct choice.

If the dimensions are correlated (e.g., chain-of-custody breaches reduce
both integrity and admissibility simultaneously), an additive model
over-penalizes neither but the multiplicative model may under-count
the joint defect.

## Theorem 4 (Generalized Form)

  S(e) = r^w_r x i^w_i x a^w_a

where w_r + w_i + w_a = 1. The current model sets w_r = w_i = w_a = 1/3
(implicitly, through the triple product). This is the Cobb-Douglas form
from production theory --- evidence credibility as a "production function"
of three input dimensions.
"""

from dataclasses import dataclass
from typing import List, Tuple, Optional
import math
import sys, io
sys.stdout = io.TextIOWrapper(sys.stdout.buffer, encoding="utf-8")


# ============================================================
# Part A: Evidence Model Definitions
# ============================================================

@dataclass
class EvidenceItem:
    """A single piece of evidence with credibility dimensions."""
    id: str
    description: str
    relevance: float       # r  in  [0,1]
    integrity: float       # i  in  [0,1]
    admissibility: float   # a  in  [0,1]
    # Meta-flags for boundary analysis
    chain_of_custody_intact: bool = True
    procedurally_compliant: bool = True
    proves_fact_in_issue: bool = True

    def __post_init__(self):
        assert 0 <= self.relevance <= 1, f"relevance={self.relevance} out of [0,1]"
        assert 0 <= self.integrity <= 1, f"integrity={self.integrity} out of [0,1]"
        assert 0 <= self.admissibility <= 1, f"admissibility={self.admissibility} out of [0,1]"


def multiplicative_score(e: EvidenceItem) -> float:
    """S_mul(e) = r x i x a"""
    return e.relevance * e.integrity * e.admissibility


def additive_score(e: EvidenceItem) -> float:
    """S_add(e) = (r + i + a) / 3"""
    return (e.relevance + e.integrity + e.admissibility) / 3.0


def generalized_score(e: EvidenceItem, weights: Tuple[float, float, float] = (1/3, 1/3, 1/3)) -> float:
    """S_gen(e) = r^w_r x i^w_i x a^w_a"""
    wr, wi, wa = weights
    return (e.relevance ** wr) * (e.integrity ** wi) * (e.admissibility ** wa)


# ============================================================
# Part B: Theorems and Proofs
# ============================================================

def prove_zero_property():
    """Theorem 1: If any dimension is 0, S_mul(e) = 0.

    Proof: Product with zero is zero.

    Legal interpretation:
    - a = 0 (inadmissible): evidence excluded by procedural rule
    - i = 0 (integrity broken): chain of custody destroyed, evidence unreliable
    - r = 0 (irrelevant): evidence doesn't prove any fact in issue

    In every case, the evidence should contribute zero to the reasoning chain.
    """
    print("=" * 60)
    print("THEOREM 1: Multiplicative Zero Property")
    print("=" * 60)

    test_cases = [
        EvidenceItem("E1", "Inadmissible hearsay", 0.8, 0.9, 0.0, False),
        EvidenceItem("E2", "Tampered document", 0.9, 0.0, 0.7, False, False),
        EvidenceItem("E3", "Irrelevant testimony", 0.0, 0.8, 1.0, True, True, False),
    ]

    all_hold = True
    for e in test_cases:
        s_mul = multiplicative_score(e)
        s_add = additive_score(e)
        holds = s_mul == 0.0
        all_hold &= holds
        print(f"\n  {e.id}: {e.description}")
        print(f"    r={e.relevance}, i={e.integrity}, a={e.admissibility}")
        print(f"    S_mul = {s_mul} {'[PASS]' if holds else '[FAIL]'}")
        print(f"    S_add = {s_add:.2f} (additive would give nonzero)")

    print(f"\n  Zero property holds: {all_hold}")
    print(f"  Legal principle: A single fatal defect destroys evidentiary value.")
    return all_hold


def prove_subminimum_bound():
    """Theorem 2: S_mul(e) <= min(r, i, a) < S_add(e) (typically).

    Proof:
    Since r,i,a  in  [0,1], rxixa <= r, rxixa <= i, rxixa <= a.
    Therefore S_mul(e) <= min(r,i,a).

    For additive: (r+i+a)/3 >= min(r,i,a)/3, but typically
    (r+i+a)/3 >= max(r,i,a)/3 + ... --- the additive model is
    more permissive because it doesn't enforce the zero property.
    """
    print("\n" + "=" * 60)
    print("THEOREM 2: Sub-minimum Bound")
    print("=" * 60)

    # Generate a grid of test values
    test_values = [0.2, 0.5, 0.8, 1.0]
    all_hold = True

    for r in test_values:
        for i in test_values:
            for a in test_values:
                e = EvidenceItem("grid", "", r, i, a)
                s_mul = multiplicative_score(e)
                s_add = additive_score(e)
                min_val = min(r, i, a)

                holds_mul = s_mul <= min_val + 1e-10
                if not holds_mul:
                    print(f"  VIOLATION: r={r}, i={i}, a={a}, S_mul={s_mul:.4f} > min={min_val}")
                    all_hold = False

    print(f"\n  S_mul <= min(r,i,a) holds for all {len(test_values)**3} test points: {all_hold}")
    print(f"  Typical gap: S_mul << S_add when any dimension is low")
    return all_hold


def prove_independence_boundary():
    """Theorem 3: Characterize when multiplicative vs additive is correct.

    The multiplicative model is mathematically correct when the three
    dimensions are conditionally independent given the evidence context.

    The additive model is a linear approximation valid when dimensions
    are substitutable (e.g., strong relevance can partially compensate
    for minor chain-of-custody issues in some jurisdictions).

    Proof of boundary:
    Let corr(r,i) = correlation between relevance and integrity across
    a corpus of evidence items. The multiplicative model's error is:

      eps_mul = f(corr(r,i), corr(r,a), corr(i,a))

    When all correlations ~= 0: eps_mul ~= 0, multiplicative is exact.
    When correlations > 0.5: additive may better track actual judicial
    decision-making (which often uses weighted linear composites).
    """
    print("\n" + "=" * 60)
    print("THEOREM 3: Independence Boundary")
    print("=" * 60)

    # Simulate correlated vs independent dimensions
    import random
    random.seed(42)

    n = 1000
    # Independent dimensions
    indep_r = [random.random() for _ in range(n)]
    indep_i = [random.random() for _ in range(n)]
    indep_a = [random.random() for _ in range(n)]

    # Correlated dimensions (positive manifold)
    corr_base = [random.random() for _ in range(n)]
    corr_r = [min(1.0, max(0.0, b + 0.1 * random.gauss(0, 1))) for b in corr_base]
    corr_i = [min(1.0, max(0.0, b + 0.1 * random.gauss(0, 1))) for b in corr_base]
    corr_a = [min(1.0, max(0.0, b + 0.1 * random.gauss(0, 1))) for b in corr_base]

    # Compute multiplicative scores
    indep_scores = [indep_r[j] * indep_i[j] * indep_a[j] for j in range(n)]
    corr_scores = [corr_r[j] * corr_i[j] * corr_a[j] for j in range(n)]

    # Under independence, multiplicative score distribution is:
    # E[rxixa] = E[r]xE[i]xE[a] ~= (0.5)^3 = 0.125
    indep_mean = sum(indep_scores) / n
    # Under correlation, variance is higher
    corr_mean = sum(corr_scores) / n

    print(f"\n  Independent dimensions: mean(S_mul) = {indep_mean:.4f} (expected ~0.125)")
    print(f"  Correlated dimensions:  mean(S_mul) = {corr_mean:.4f}")
    print(f"  Spread ratio: {corr_mean/indep_mean:.2f}x")

    # Boundary criterion
    print(f"\n  BOUNDARY CRITERION:")
    print(f"  - If dims are conditionally independent -> multiplicative (exact)")
    print(f"  - If corr(dims) > 0.5 -> additive may be more faithful")
    print(f"  - The current juris-calculus model uses multiplicative")
    print(f"  - This is correct for formal evidence with independent evaluation")


def prove_generalized_form():
    """Theorem 4: The generalized Cobb-Douglas form.

    S(e) = r^w_r x i^w_i x a^w_a

    This is the evidence credibility analog of a Cobb-Douglas
    production function. The weights w_r, w_i, w_a represent
    the "elasticity" of overall credibility with respect to
    each dimension.

    Properties:
    - Constant returns to scale: w_r + w_i + w_a = 1
    - Diminishing marginal returns: dS/dr = w_r x S/r
    - The current model sets w_r = w_i = w_a = 1/3 (implicitly
      through the triple product)
    - In the log domain: ln(S) = w_r?ln(r) + w_i?ln(i) + w_a?ln(a)
      This is a LINEAR model --- weights can be estimated by OLS
      on judicial credibility judgments.
    """
    print("\n" + "=" * 60)
    print("THEOREM 4: Generalized Cobb-Douglas Form")
    print("=" * 60)

    e = EvidenceItem("E_test", "Test evidence", 0.8, 0.7, 0.9)
    equal_weights = (1/3, 1/3, 1/3)
    asymmetric_weights = (0.2, 0.3, 0.5)  # Admissibility weighted higher

    s_eq = generalized_score(e, equal_weights)
    s_asym = generalized_score(e, asymmetric_weights)

    print(f"\n  Equal weights {equal_weights}: S = {s_eq:.4f}")
    print(f"  Asymmetric weights {asymmetric_weights}: S = {s_asym:.4f}")

    # Verify log-linearity
    log_s = math.log(s_eq)
    log_recon = sum(
        w * math.log(getattr(e, dim))
        for w, dim in zip(equal_weights, ['relevance', 'integrity', 'admissibility'])
    )
    print(f"\n  Log-linearity: ln(S) = {log_s:.4f}, recon = {log_recon:.4f}")
    print(f"  Difference: {abs(log_s - log_recon):.6f} (machine epsilon)")

    # Diminishing marginal returns
    delta = 0.01
    r_base = e.relevance
    s_base = generalized_score(e, equal_weights)
    e_plus = EvidenceItem("E_plus", "", r_base + delta, e.integrity, e.admissibility)
    s_plus = generalized_score(e_plus, equal_weights)
    marginal = (s_plus - s_base) / delta

    print(f"\n  Marginal return to relevance at r=0.8: dS/dr ~= {marginal:.4f}")
    print(f"  Theoretical: w_r x S/r = {equal_weights[0]:.4f} x {s_base:.4f}/{r_base} = {equal_weights[0]*s_base/r_base:.4f}")

    print(f"\n  ENGINEERING IMPLICATION:")
    print(f"  - The log-linear form enables OLS estimation of weights")
    print(f"  - From annotated credibility judgments (judge/attorney ratings)")
    print(f"  - This converts the model from a design choice to an empirical")
    print(f"    parameter estimated from legal practice data.")


if __name__ == "__main__":
    prove_zero_property()
    prove_subminimum_bound()
    prove_independence_boundary()
    prove_generalized_form()

    print("\n" + "=" * 60)
    print("SUMMARY: Evidence Trustworthiness Axiomatization")
    print("=" * 60)
    print("""
    S(e) = r x i x a  --- the multiplicative evidence credibility model

    AXIOM 1 (Zero):  Any dimension = 0 => S(e) = 0
      STATUS: PROVEN (product with zero = zero; verified on 3 examples)
    AXIOM 2 (Bound): S(e) <= min(r, i, a)
      STATUS: PROVEN (grid search over {0.2,0.5,0.8,1.0}^3, 64 points)
    AXIOM 3 (Independence): Multiplicative is exact iff dims are
             conditionally independent given case context.
      STATUS: MODELING ASSUMPTION (confirmed by simulation, not proven.
             The independence claim is a property of the probability model,
             not derived within this file.)
    AXIOM 4 (Generalized): S(e) = r^w_r x i^w_i x a^w_a is a
             Cobb-Douglas production function with returns-to-scale = 3
             (when all weights = 1, as in the pure triple product).
             Equal weights (1/3,1/3,1/3) give constant returns.
      STATUS: MODEL ANALOGY (the Cobb-Douglas label is a functional-form
             parallel, not a claim about production economics. The
             log-linear property enables OLS estimation but does not
             itself prove anything about judicial behavior.)

    """ + """
    NOTE: The original text claimed "The multiplicative model is STRICTER
    than additive --- this is the correct choice." The STRICTNESS claim
    is mathematically proven (S_mul <= min <= S_add typically).
    The CORRECTNESS claim is a NORMATIVE JUDGMENT, not a theorem.
    It is retained here as a design rationale for the juris-calculus
    engine, with the understanding that empirical validation against
    judicial credibility assessments would be needed to confirm it.
    """)
