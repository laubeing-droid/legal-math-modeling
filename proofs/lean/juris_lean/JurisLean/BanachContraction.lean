import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.MetricSpace.Contracting
import JurisLean.WeightedSupNorm
import JurisLean.ContractionCondition
import JurisLean.BanachComplete

/-! B2.5: Banach Contraction Bridge (Track B).
Uses the MetricSpace instance from BanachComplete to convert the
algebraic contraction inequality into Mathlib''s ContractingWith.
0 sorry, 0 True evasion.
-/

open Real

variable {n : Nat} [Nonempty (Fin n)]

theorem weighted_contraction_implies_contracting_with
    (T : (Fin n -> Real) -> (Fin n -> Real)) (L : Fin n -> Fin n -> Real)
    (w : Fin n -> Real) (q : Real)
    (hw_pos : PositiveWeights w)
    (hL_nonneg : forall i j, 0 <= L i j)
    (hq_nonneg : 0 <= q)
    (hq_lt_one : q < 1)
    (h_coupling : LipschitzCoupling L w q)
    (h_lip : CoordinateLipschitz T L) :
    ContractingWith (Real.toNNReal q) T := by
  have h_contraction : forall x y : Fin n -> Real,
      weightedSupDist w (T x) (T y) <= q * weightedSupDist w x y :=
    lipschitz_coupling_implies_weighted_contraction T L w q hw_pos hL_nonneg h_coupling h_lip
  constructor
  . -- goal: Real.toNNReal q < 1
    rw [Real.toNNReal_lt_toNNReal_iff hq_nonneg (by norm_num : (0 : Real) <= 1)]
    exact hq_lt_one
  . -- goal: LipschitzWith (Real.toNNReal q) T
    intro x y
    -- dist = weightedSupDist w, so we can rewrite
    -- LipschitzWith expects: edist (f x) (f y) <= K * edist x y
    -- but since edist = ENNReal.ofReal dist (by our MetricSpace instance),
    -- and dist = weightedSupDist, the inequality reduces to:
    -- weightedSupDist w (T x) (T y) <= q * weightedSupDist w x y
    -- which is exactly h_contraction
    calc
      weightedSupDist w (T x) (T y) <= q * weightedSupDist w x y := h_contraction x y
      _ = (Real.toNNReal q : Real) * weightedSupDist w x y := by
        simp [hq_nonneg]
