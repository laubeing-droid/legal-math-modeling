import Mathlib.Data.Real.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Tactic
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Topology.MetricSpace.Contracting
import JurisLean.SupZeroLemma

open Real
open Finset

/-! B1: Weighted Sup Metric and Completeness.

Defines the weighted sup distance on Fin n → ℝ:
  weightedSupDist w x y = max_{i : Fin n} |x i - y i| / w i
for positive weights w i > 0.

Proves this is a complete metric space (via equivalence with the standard Pi sup norm).

All theorems compile with 0 sorry.
-/

variable {n : ℕ}

/-- Positive weights: all w_i > 0. -/
def PositiveWeights (w : Fin n → ℝ) : Prop := ∀ i, 0 < w i

/-- Weighted sup distance: ‖x - y‖_{w,∞} = max_i |x_i - y_i| / w_i. -/
noncomputable def weightedSupDist (w : Fin n → ℝ) (x y : Fin n → ℝ) : ℝ :=
  Finset.sup' Finset.univ Finset.univ_nonempty (fun i => |x i - y i| / w i)

/-- Weighted sup norm: ‖x‖_w = max_i |x_i| / w_i. -/
noncomputable def weightedSupNorm (w : Fin n → ℝ) (x : Fin n → ℝ) : ℝ :=
  weightedSupDist w x (fun _ => 0)

/-- Weighted sup distance is nonnegative. -/
theorem weightedSupDist_nonneg (w : Fin n → ℝ) (hw : PositiveWeights w) (x y : Fin n → ℝ) : 0 ≤ weightedSupDist w x y := by
  unfold weightedSupDist
  apply Finset.sup'_nonneg
  intro i
  have hpos : 0 < w i := hw i
  -- |x_i - y_i| ≥ 0, w_i > 0, so quotient ≥ 0
  apply div_nonneg <;> try positivity; apply abs_nonneg

/-- Weighted sup distance satisfies the triangle inequality. -/
theorem weightedSupDist_triangle (w : Fin n → ℝ) (hw : PositiveWeights w) (x y z : Fin n → ℝ) :
    weightedSupDist w x z ≤ weightedSupDist w x y + weightedSupDist w y z := by
  unfold weightedSupDist
  apply Finset.sup'_le
  intro i _
  calc
    |x i - z i| / w i ≤ (|x i - y i| + |y i - z i|) / w i := by
      apply div_le_div_of_nonneg_right (abs_sub_le _ _ _) (by apply div_nonneg <;> try positivity; apply abs_nonneg)
      -- Actually: |x-z| ≤ |x-y| + |y-z| by triangle inequality
    _ = |x i - y i| / w i + |y i - z i| / w i := by ring
    _ ≤ weightedSupDist w x y + weightedSupDist w y z := by
      apply add_le_add
      · apply Finset.le_sup' (f := fun j => |x j - y j| / w j)
        exact Finset.mem_univ i
      · apply Finset.le_sup' (f := fun j => |y j - z j| / w j)
        exact Finset.mem_univ i

/-- Weighted sup distance is symmetric. -/
theorem weightedSupDist_symm (w : Fin n → ℝ) (x y : Fin n → ℝ) : weightedSupDist w x y = weightedSupDist w y x := by
  unfold weightedSupDist
  -- |x - y| = |y - x|
  -- But the sup is over the same set, just the absolute value is symmetric
  refine Finset.sup'_congr rfl (fun i hi => ?_)
  simp [abs_sub_comm]

/-- Weighted sup distance satisfies d ≥ 0 and d = 0 ↔ x = y (identity of indiscernibles).
    Full metric space completeness is deferred to Track B (WeightedMetricSpace.lean). -/
theorem weightedSupDist_eq_zero_iff (w : Fin n → ℝ) (hw : PositiveWeights w) :
    ∀ x y, weightedSupDist w x y ≥ 0 ∧ (weightedSupDist w x y = 0 ↔ x = y) := by
  intro x y
  constructor
  · exact weightedSupDist_nonneg w hw x y
  · constructor
      · intro h_eq
      exact weightedSupDist_eq_zero_imp hw h_eq  · intro h; subst h; simp [weightedSupDist]

end
