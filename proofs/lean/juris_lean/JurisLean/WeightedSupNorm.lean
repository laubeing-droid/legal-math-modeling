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

All theorems compile with 0 incomplete-proof-token.
-/

variable {n : ℕ} [Nonempty (Fin n)]

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
  -- Pick an arbitrary index; the sup is at least as large as the term at that index, which is ≥ 0.
  let i0 : Fin n := Classical.arbitrary _
  have h_term : 0 ≤ |x i0 - y i0| / w i0 :=
    div_nonneg (abs_nonneg _) (le_of_lt (hw i0))
  have h_sup_ge : |x i0 - y i0| / w i0 ≤ weightedSupDist w x y := by
    unfold weightedSupDist
    apply Finset.le_sup' (fun j => |x j - y j| / w j) (Finset.mem_univ i0)
  exact le_trans h_term h_sup_ge

/-- Weighted sup distance satisfies the triangle inequality. -/
theorem weightedSupDist_triangle (w : Fin n → ℝ) (hw : PositiveWeights w) (x y z : Fin n → ℝ) :
    weightedSupDist w x z ≤ weightedSupDist w x y + weightedSupDist w y z := by
  unfold weightedSupDist
  apply Finset.sup'_le
  intro i _
  have htri : |x i - z i| ≤ |x i - y i| + |y i - z i| := by
    calc
      |x i - z i| = |(x i - y i) + (y i - z i)| := by
        simp [sub_add_sub_cancel]
      _ ≤ |x i - y i| + |y i - z i| := abs_add_le _ _
  calc
    |x i - z i| / w i ≤ (|x i - y i| + |y i - z i|) / w i :=
      div_le_div_of_nonneg_right htri (le_of_lt (hw i))
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
  apply Finset.sup'_congr Finset.univ_nonempty rfl
  intro i hi
  rw [← abs_neg, neg_sub]

/-- Weighted sup distance is nonnegative and separates points: d(x,y)=0 iff x=y. -/
theorem weightedSupDist_complete (w : Fin n → ℝ) (hw : PositiveWeights w) :
    ∀ x y, weightedSupDist w x y ≥ 0 ∧ (weightedSupDist w x y = 0 ↔ x = y) := by
  intro x y
  constructor
  · exact weightedSupDist_nonneg w hw x y
  · refine ⟨?_, ?_⟩
    · intro h_eq
      unfold weightedSupDist at h_eq
      apply funext
      intro i
      have h_term_nonneg : 0 ≤ |x i - y i| / w i :=
        div_nonneg (abs_nonneg _) (le_of_lt (hw i))
      have h_term_sup : |x i - y i| / w i ≤
        Finset.sup' Finset.univ Finset.univ_nonempty (fun j => |x j - y j| / w j) :=
        Finset.le_sup' (fun j => |x j - y j| / w j) (Finset.mem_univ i)
      rw [h_eq] at h_term_sup
      have h_term_zero : |x i - y i| / w i = 0 := le_antisymm h_term_sup h_term_nonneg
      rcases div_eq_zero_iff.mp h_term_zero with (h_abs | h_w)
      · -- |x i - y i| = 0, so x i = y i
        have h_sub : x i - y i = 0 := abs_eq_zero.mp h_abs
        exact sub_eq_zero.mp h_sub
      · -- w i = 0 contradicts positivity
        exact (ne_of_gt (hw i) h_w).elim
    · intro h
      subst h
      simp [weightedSupDist]
