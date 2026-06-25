import Mathlib.Data.Real.Basic
import Mathlib.Tactic
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
  have h_contraction : forall x y : Fin n -> Real,
      weightedSupDist w (T x) (T y) <= q * weightedSupDist w x y :=
    lipschitz_coupling_implies_weighted_contraction T L w q hw_pos hL_nonneg h_coupling h_lip
  have hKlt1 : (Real.toNNReal q : NNReal) < 1 := by
    rw [Real.toNNReal_lt_toNNReal_iff hq_nonneg (show (0 : Real) <= 1 from by norm_num)]
    exact hq_lt_one
  have hLip : LipschitzWith (Real.toNNReal q) T := by
    intro x y
    have hcoeff : (Real.toNNReal q : Real) = q := by simp [hq_nonneg]
    simpa [hcoeff] using h_contraction x y
  exact And.intro hKlt1 hLip
