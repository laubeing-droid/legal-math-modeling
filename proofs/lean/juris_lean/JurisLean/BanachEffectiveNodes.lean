-- BanachEffectiveNodes.lean
-- Formal verification that the effective-nodes pricing function
--   f(x) = β·T + (1−β)·x
-- is a Banach contraction on ℝ with contraction constant (1−β), where β ∈ (0,1).
--
-- Build: lake env lean proofs/lean/BanachEffectiveNodes.lean
-- Mathlib dependency: Mathlib.Data.Real.Basic, Mathlib.Topology.MetricSpace.Basic
--
-- Sorry boundaries are marked with `-- SORRY BOUNDARY` comments.

import Mathlib.Data.Real.Basic
import Mathlib.Topology.MetricSpace.Basic

namespace EffectiveNodesPricing

/-!
## Pricing function definition

The effective-nodes pricing function for legal reasoning networks:
  f(x, β, T) = β * T + (1 - β) * x

where:
  - x : current valuation (ℝ)
  - β : damping/influence coefficient in (0, 1)
  - T : target/reference value (ℝ)
-/

/-- The effective-nodes pricing function. -/
def pricingFn (x beta T : ℝ) : ℝ :=
  beta * T + (1 - beta) * x

/-!
## Contraction proof

A function f : ℝ → ℝ is a Banach contraction with constant k ∈ [0,1) if
  ∀ x y, |f(x) - f(y)| ≤ k * |x - y|

We prove this for f(x) = β·T + (1−β)·x with k = (1−β).
-/

/-- Auxiliary lemma: the pricing function is affine with slope (1 - beta). -/
lemma pricingFn_sub (x y beta T : ℝ) :
    pricingFn x beta T - pricingFn y beta T = (1 - beta) * (x - y) := by
  -- Expand both sides using the definition.
  simp only [pricingFn]
  -- After expansion:
  --   (beta * T + (1 - beta) * x) - (beta * T + (1 - beta) * y)
  -- = (1 - beta) * x - (1 - beta) * y
  -- = (1 - beta) * (x - y)
  ring

/-- The absolute-value form: |f(x) - f(y)| = |1 - beta| * |x - y|. -/
lemma abs_pricingFn_sub (x y beta T : ℝ) :
    abs (pricingFn x beta T - pricingFn y beta T) = abs (1 - beta) * abs (x - y) := by
  rw [pricingFn_sub x y beta T, abs_mul]

-- SORRY BOUNDARY: The following uses `abs_of_pos` and `abs_of_nonneg` which are
-- in Mathlib.Analysis.Normed.Field.Basic (not imported above).
-- If the import is available, the incomplete-proof-token can be replaced with `abs_of_pos (sub_pos.mpr hbeta)`.

/-- For beta ∈ (0,1), we have |1 - beta| = 1 - beta. -/
lemma abs_one_sub_beta_of_pos_lt_one {beta : ℝ} (hbeta : 0 < beta ∧ beta < 1) :
    abs (1 - beta) = 1 - beta := by
  -- Since beta < 1, we have 1 - beta > 0, so |1 - beta| = 1 - beta.
  apply abs_of_nonneg
  linarith [hbeta.2]

/-- For beta ∈ (0,1), 1 - beta ∈ (0,1). -/
lemma one_sub_beta_lt_one {beta : ℝ} (hbeta : 0 < beta ∧ beta < 1) :
    1 - beta < 1 := by
  linarith [hbeta.1]

lemma one_sub_beta_nonneg {beta : ℝ} (hbeta : 0 < beta ∧ beta < 1) :
    0 ≤ 1 - beta := by
  linarith [hbeta.2]

/-- Main contraction lemma.

    For beta ∈ (0,1), the pricing function is Lipschitz with constant (1 - beta) < 1,
    hence a Banach contraction on the metric space (ℝ, d) where d(x,y) = |x - y|. -/
theorem pricingFn_contraction
    (beta T : ℝ)
    (hbeta : 0 < beta ∧ beta < 1) :
    ∀ x y : ℝ,
      abs (pricingFn x beta T - pricingFn y beta T) ≤ (1 - beta) * abs (x - y) := by
  intro x y
  -- Step 1: Rewrite the LHS using the affine structure.
  rw [pricingFn_sub]
  -- Step 2: Rewrite abs using the fact that 1 - beta > 0.
  rw [abs_mul, abs_one_sub_beta_of_pos_lt_one hbeta]

/-!
## Fixed-point existence

By the Banach fixed-point theorem, the contraction mapping f has a unique fixed point x*
in any complete metric space. For our pricing function:

  x* = β·T + (1−β)·x*
  ⟹  x* − (1−β)·x* = β·T
  ⟹  β·x* = β·T
  ⟹  x* = T

We compute this directly.
-/

/-- The fixed point of the pricing function is T itself. -/
theorem pricingFn_fixed_point
    (beta T : ℝ)
    (hbeta : 0 < beta ∧ beta < 1) :
    pricingFn T beta T = T := by
  -- f(T) = β·T + (1−β)·T = (β + 1 − β)·T = T
  simp only [pricingFn]
  ring

/-- The fixed point is unique. -/
-- SORRY BOUNDARY: Uniqueness follows from the Banach fixed-point theorem
-- (which lives in Mathlib.Topology.MetricSpace.CauSeqFilter or similar).
-- We state the property but leave the proof as incomplete-proof-token since the
-- full fixed-point machinery requires additional Mathlib imports.
theorem pricingFn_unique_fixed_point
    (beta T : ℝ)
    (hbeta : 0 < beta ∧ beta < 1)
    (x : ℝ)
    (hx : pricingFn x beta T = x) :
    x = T := by
  -- From hx: β·T + (1−β)·x = x
  -- β·T = x − (1−β)·x = β·x
  -- Since β > 0: T = x
  have h1 : beta * T + (1 - beta) * x = x := hx
  have h2 : beta * T = beta * x := by linarith
  have h3 : beta * (T - x) = 0 := by linarith
  have h4 : T - x = 0 := by
    apply (mul_eq_zero.mp h3).resolve_left
    linarith [hbeta.1]
  linarith [h4]

/-!
## Metatheoretic note

This file establishes the Banach contraction property for the effective-nodes
pricing function used in legal reasoning networks (Chapter 5, Theorem 5.2.1).

The contraction guarantees that iterating f from any initial valuation converges
to the unique equilibrium valuation T, with geometric convergence rate (1−β)^n.
-/

end EffectiveNodesPricing
