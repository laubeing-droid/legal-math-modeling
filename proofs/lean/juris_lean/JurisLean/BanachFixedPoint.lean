import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import JurisLean.WeightedSupNorm
import JurisLean.ContractionCondition
import JurisLean.BanachContraction

/-! B3: Weighted Contraction Data (Track B).

The fixed-point instantiation is intentionally deferred. What is available at
this stage is the precise contraction data needed for the later Banach bridge:
positive weights, nonnegative contraction factor, strict bound `q < 1`, and
the machine-checked weighted contraction inequality.

0 sorry, 0 True evasion.
-/

open Real

variable {n : Nat} [Nonempty (Fin n)]

/-- Evidence package for a weighted contraction on `Fin n → ℝ`. -/
structure WeightedContractionData
    (T : (Fin n -> Real) -> (Fin n -> Real))
    (w : Fin n -> Real) (q : Real) where
  weightPositivity : PositiveWeights w
  qNonneg : 0 <= q
  qLtOne : q < 1
  contract :
    forall x y : Fin n -> Real,
      weightedSupDist w (T x) (T y) <= (Real.toNNReal q : Real) * weightedSupDist w x y

/-- The coupling and coordinate-Lipschitz hypotheses produce the weighted
contraction data required by the future fixed-point bridge. -/
theorem weightedContractionData_of_coupling
    (T : (Fin n -> Real) -> (Fin n -> Real)) (L : Fin n -> Fin n -> Real)
    (w : Fin n -> Real) (q : Real)
    (hw_pos : PositiveWeights w)
    (hL_nonneg : forall i j, 0 <= L i j)
    (hq_nonneg : 0 <= q)
    (hq_lt_one : q < 1)
    (h_coupling : LipschitzCoupling L w q)
    (h_lip : CoordinateLipschitz T L) :
    WeightedContractionData T w q where
  weightPositivity := hw_pos
  qNonneg := hq_nonneg
  qLtOne := hq_lt_one
  contract := weighted_contraction_bound_nnreal T L w q hw_pos hL_nonneg hq_nonneg h_coupling h_lip
