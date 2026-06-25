import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.MetricSpace.Contracting
import JurisLean.WeightedSupNorm
import JurisLean.ContractionCondition
import JurisLean.BanachComplete

/-! B2.5: Banach Contraction Bridge (Track B).
Uses the MetricSpace instance from BanachComplete to convert the
algebraic contraction inequality already proved in ContractionCondition
into Mathlib''s ContractingWith.
0 sorry, 0 True evasion.
-/

open Real
open Finset

variable {n : Nat} [Nonempty (Fin n)]

/-- Given w > 0, L >= 0, q < 1, and the algebraic inequality,
    T is a q-contraction under the weighted sup metric. -/
theorem weighted_contraction_implies_contracting_with
    (T : (Fin n -> Real) -> (Fin n -> Real)) (L : Fin n -> Fin n -> Real)
    (w : Fin n -> Real) (q : Real)
    (hw_pos : PositiveWeights w)
    (hL_nonneg : forall i j, 0 <= L i j)
    (hq_range : 0 <= q /\ q < 1)
    (h_coupling : LipschitzCoupling L w q)
    (h_lip : CoordinateLipschitz T L) :
    ContractingWith (Real.toNNReal q) T := by
  rcases hq_range with \u27E8hq_nonneg, hq_lt_one\u27E9
  have h_contraction : forall x y : Fin n -> Real,
      weightedSupDist w (T x) (T y) <= q * weightedSupDist w x y :=
    lipschitz_coupling_implies_weighted_contraction T L w q hw_pos hL_nonneg h_coupling h_lip
  have hK_lt_one : (Real.toNNReal q : NNReal) < 1 := by
    rw [Real.toNNReal_lt_toNNReal_iff (by linarith) (by norm_num : (0 : Real) <= 1)]
    exact hq_lt_one
  refine And.intro hK_lt_one ?_
  -- The MetricSpace instance from BanachComplete makes dist = weightedSupDist w
  -- So LipschitzWith follows directly from h_contraction
  intro x y
  simpa using h_contraction x y
