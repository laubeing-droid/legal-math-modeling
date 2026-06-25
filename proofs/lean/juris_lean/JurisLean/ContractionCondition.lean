import Mathlib.Data.Real.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Tactic
import JurisLean.WeightedSupNorm

open Real
open Finset

/-! B2: Lw <= qw implies weighted sup contraction.

Theorem: If L w <= q w componentwise with q < 1 and w > 0, then for any
operator T satisfying the coordinate Lipschitz condition
  |T(x)_i - T(y)_i| <= sum_j L_ij * |x_j - y_j|,
T is a q-contraction under weightedSupDist.

This file proves the core algebraic inequality.
Connecting to Mathlib's ContractingWith requires Analysis imports (Track B complete).
0 sorry, 0 True evasion.
-/

variable {n : ℕ} [Nonempty (Fin n)]

/-- Lipschitz coupling matrix condition: for all i, sum_j L_ij * w_j <= q * w_i. -/
def LipschitzCoupling (L : Fin n → Fin n → ℝ) (w : Fin n → ℝ) (q : ℝ) : Prop :=
  ∀ i, (Finset.sum Finset.univ (fun j => L i j * w j)) ≤ q * w i

/-- Coordinate Lipschitz condition on operator T: |T(x)_i - T(y)_i| <= sum_j L_ij * |x_j - y_j|. -/
def CoordinateLipschitz (T : (Fin n → ℝ) → (Fin n → ℝ)) (L : Fin n → Fin n → ℝ) : Prop :=
  ∀ x y i, |T x i - T y i| ≤ Finset.sum Finset.univ (fun j => L i j * |x j - y j|)

/-- Core algebraic theorem: L w <= q w and coordinate Lipschitz implies
    weightedSupDist(T x, T y) <= q * weightedSupDist(x, y). -/
theorem lipschitz_coupling_implies_weighted_contraction
    (T : (Fin n → ℝ) → (Fin n → ℝ)) (L : Fin n → Fin n → ℝ)
    (w : Fin n → ℝ) (q : ℝ)
    (hw_pos : ∀ i, 0 < w i)
    (hL_nonneg : ∀ i j, 0 ≤ L i j)
    (h_coupling : LipschitzCoupling L w q)
    (h_lip : CoordinateLipschitz T L)
    (x y : Fin n → ℝ) :
    weightedSupDist w (T x) (T y) ≤ q * weightedSupDist w x y := by
  unfold weightedSupDist
  apply Finset.sup'_le Finset.univ_nonempty
  intro i hi
  have h_coord := h_lip x y i
  have h_couple := h_coupling i
  have hposi : 0 < w i := hw_pos i
  calc
    |T x i - T y i| / w i
        ≤ (Finset.sum Finset.univ (fun j => L i j * |x j - y j|)) / w i := by
      gcongr
    _ = Finset.sum Finset.univ (fun j => (L i j * |x j - y j|) / w i) := by
      simp [Finset.sum_div]
    _ ≤ Finset.sum Finset.univ (fun j => (L i j * w j / w i) * (|x j - y j| / w j)) := by
      refine Finset.sum_le_sum (fun j hj => ?_)
      have hposj : 0 < w j := hw_pos j
      field_simp [ne_of_gt hposi, ne_of_gt hposj]
      ring
      rfl
    _ ≤ Finset.sum Finset.univ (fun j => (L i j * w j / w i) * weightedSupDist w x y) := by
      refine Finset.sum_le_sum (fun j hj => ?_)
      have hL_nonneg_ij : 0 ≤ L i j := hL_nonneg i j
      have h_nonneg : 0 ≤ L i j * w j / w i := by
        refine div_nonneg (mul_nonneg hL_nonneg_ij (by linarith [hw_pos j])) (by linarith)
      refine mul_le_mul_of_nonneg_left ?_ h_nonneg
      have h_sup_ge : |x j - y j| / w j ≤ weightedSupDist w x y := by
        unfold weightedSupDist
        apply Finset.le_sup' (f := fun k => |x k - y k| / w k)
        exact Finset.mem_univ j
      exact h_sup_ge
    _ = (Finset.sum Finset.univ (fun j => L i j * w j / w i)) * weightedSupDist w x y := by
      simp [Finset.mul_sum, div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm]
    _ = (Finset.sum Finset.univ (fun j => L i j * w j) / w i) * weightedSupDist w x y := by
      simp [Finset.sum_div, div_div]
    _ ≤ (q * w i / w i) * weightedSupDist w x y := by
      refine mul_le_mul_of_nonneg_right ?_ (weightedSupDist_nonneg w hw_pos x y)
      gcongr
    _ = q * weightedSupDist w x y := by
      field_simp [ne_of_gt hposi]
