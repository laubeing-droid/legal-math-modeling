import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Mathlib.Data.ENNReal.Basic
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.MetricSpace.Contracting
import JurisLean.WeightedSupNorm
import JurisLean.ContractionCondition
import JurisLean.BanachComplete
/-! B2.5: Banach Contraction Bridge (Track B).
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
  letI : MetricSpace (Fin n -> Real) := weightedMetricSpace w hw_pos
  have h_contraction : forall x y : Fin n -> Real,
      weightedSupDist w (T x) (T y) <= q * weightedSupDist w x y :=
    lipschitz_coupling_implies_weighted_contraction T L w q hw_pos hL_nonneg h_coupling h_lip
  apply And.intro
  . apply NNReal.coe_lt_coe.mp
    rw [Real.toNNReal_of_nonneg hq_nonneg]
    exact hq_lt_one
  . intro x y
    have hd_nonneg : 0 <= weightedSupDist w x y := weightedSupDist_nonneg w hw_pos x y
    have hmul : ENNReal.ofReal (q * weightedSupDist w x y) = ENNReal.ofReal q * ENNReal.ofReal (weightedSupDist w x y) := by
      have hprod_nonneg : 0 <= q * weightedSupDist w x y := mul_nonneg hq_nonneg hd_nonneg
      calc
        ENNReal.ofReal (q * weightedSupDist w x y) = (Real.toNNReal (q * weightedSupDist w x y) : ENNReal) := by
          simp [ENNReal.ofReal, hprod_nonneg]
        _ = ((Real.toNNReal q) * (Real.toNNReal (weightedSupDist w x y)) : ENNReal) := by
          -- NNReal multiplication: Real.toNNReal preserves mul for nonnegative args
          simp [Real.toNNReal_of_nonneg hq_nonneg, Real.toNNReal_of_nonneg hd_nonneg, hprod_nonneg]
        _ = ENNReal.ofReal q * ENNReal.ofReal (weightedSupDist w x y) := by
          simp [ENNReal.ofReal, hq_nonneg, hd_nonneg]
    calc
      ENNReal.ofReal (weightedSupDist w (T x) (T y)) <= ENNReal.ofReal (q * weightedSupDist w x y) :=
        ENNReal.ofReal_le_ofReal (h_contraction x y)
      _ = ENNReal.ofReal q * ENNReal.ofReal (weightedSupDist w x y) := hmul
      _ = (Real.toNNReal q : ENNReal) * ENNReal.ofReal (weightedSupDist w x y) := by
        simp [ENNReal.ofReal, hq_nonneg]
