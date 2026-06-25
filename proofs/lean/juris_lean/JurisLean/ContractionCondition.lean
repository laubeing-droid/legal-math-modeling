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

variable {n : Nat} [Nonempty (Fin n)]

/-- Lipschitz coupling matrix condition: for all i, sum_j L_ij * w_j <= q * w_i. -/
def LipschitzCoupling (L : Fin n -> Fin n -> Real) (w : Fin n -> Real) (q : Real) : Prop :=
  forall i, (Finset.sum Finset.univ (fun j => L i j * w j)) <= q * w i

/-- Coordinate Lipschitz condition on operator T: |T(x)_i - T(y)_i| <= sum_j L_ij * |x_j - y_j|. -/
def CoordinateLipschitz (T : (Fin n -> Real) -> (Fin n -> Real)) (L : Fin n -> Fin n -> Real) : Prop :=
  forall x y i, |T x i - T y i| <= Finset.sum Finset.univ (fun j => L i j * |x j - y j|)

/-- Core algebraic theorem: L w <= q w and coordinate Lipschitz implies
    weightedSupDist(T x, T y) <= q * weightedSupDist(x, y). -/
theorem lipschitz_coupling_implies_weighted_contraction
    (T : (Fin n -> Real) -> (Fin n -> Real)) (L : Fin n -> Fin n -> Real)
    (w : Fin n -> Real) (q : Real)
    (hw_pos : forall i, 0 < w i)
    (h_coupling : LipschitzCoupling L w q)
    (h_lip : CoordinateLipschitz T L)
    (x y : Fin n -> Real) :
    weightedSupDist w (T x) (T y) <= q * weightedSupDist w x y := by
  unfold weightedSupDist
  -- Goal: sup_i |T(x)_i - T(y)_i| / w_i <= q * sup_j |x_j - y_j| / w_j
  apply Finset.sup'_le
  intro i hi
  have h_coord := h_lip x y i
  -- |T(x)_i - T(y)_i| / w_i <= (sum_j L_ij * |x_j - y_j|) / w_i
  calc
    |T x i - T y i| / w i
        <= (Finset.sum Finset.univ (fun j => L i j * |x j - y j|)) / w i := by
      refine (div_le_div_right (by positivity)).mpr h_coord
    _ = Finset.sum Finset.univ (fun j => L i j * |x j - y j| / w i) := by
      simp [Finset.sum_div, Finset.mul_div_assoc]
    _ = Finset.sum Finset.univ (fun j => (L i j * w j / w i) * (|x j - y j| / w j)) := by
      apply Finset.sum_congr rfl (fun j _ => ?_)
      field_simp [ne_of_gt (hw_pos i), ne_of_gt (hw_pos j)]
      ring
    _ <= Finset.sum Finset.univ (fun j => (L i j * w j / w i) * weightedSupDist w x y) := by
      refine Finset.sum_le_sum (fun j _ => ?_)
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      -- |x_j - y_j| / w_j <= sup_k |x_k - y_k| / w_k = weightedSupDist w x y
      unfold weightedSupDist
      apply Finset.le_sup' (f := fun k => |x k - y k| / w k)
      exact Finset.mem_univ j
    _ = (Finset.sum Finset.univ (fun j => L i j * w j) / w i) * weightedSupDist w x y := by
      simp [Finset.sum_div, Finset.mul_div_assoc, div_div]
      ring
    _ <= (q * w i / w i) * weightedSupDist w x y := by
      refine mul_le_mul_of_nonneg_right ?_ (by
        unfold weightedSupDist
        apply Finset.sup'_nonneg
        intro k
        positivity)
      refine (div_le_div_right (by positivity)).mpr (h_coupling i)
    _ = q * weightedSupDist w x y := by
      field_simp [ne_of_gt (hw_pos i)]