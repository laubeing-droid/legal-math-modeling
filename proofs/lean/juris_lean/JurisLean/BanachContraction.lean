import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import JurisLean.WeightedSupNorm
import JurisLean.ContractionCondition

/-! B2.5: Weighted Contraction Bound (Track B).

This file records the contraction inequality already proved for the weighted
sup metric. The final bridge to Mathlib's `ContractingWith` API remains
deferred until the weighted metric is connected to a complete-space instance.

0 incomplete-proof-token, 0 True evasion.
-/

open Real

variable {n : Nat} [Nonempty (Fin n)]

/-- The weighted sup metric contracts by factor `q` under the coupling and
coordinate Lipschitz assumptions. -/
theorem weighted_contraction_bound
    (T : (Fin n -> Real) -> (Fin n -> Real)) (L : Fin n -> Fin n -> Real)
    (w : Fin n -> Real) (q : Real)
    (hw_pos : PositiveWeights w)
    (hL_nonneg : forall i j, 0 <= L i j)
    (h_coupling : LipschitzCoupling L w q)
    (h_lip : CoordinateLipschitz T L) :
    forall x y : Fin n -> Real,
      weightedSupDist w (T x) (T y) <= q * weightedSupDist w x y :=
  lipschitz_coupling_implies_weighted_contraction T L w q hw_pos hL_nonneg h_coupling h_lip

/-- The same contraction inequality, rewritten with `Real.toNNReal q` on the
right-hand side for later handoff to Mathlib APIs. -/
theorem weighted_contraction_bound_nnreal
    (T : (Fin n -> Real) -> (Fin n -> Real)) (L : Fin n -> Fin n -> Real)
    (w : Fin n -> Real) (q : Real)
    (hw_pos : PositiveWeights w)
    (hL_nonneg : forall i j, 0 <= L i j)
    (hq_nonneg : 0 <= q)
    (h_coupling : LipschitzCoupling L w q)
    (h_lip : CoordinateLipschitz T L) :
    forall x y : Fin n -> Real,
      weightedSupDist w (T x) (T y) <= (Real.toNNReal q : Real) * weightedSupDist w x y := by
  intro x y
  rw [Real.toNNReal_of_nonneg hq_nonneg]
  exact weighted_contraction_bound T L w q hw_pos hL_nonneg h_coupling h_lip x y
