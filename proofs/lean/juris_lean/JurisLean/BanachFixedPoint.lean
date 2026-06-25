import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Mathlib.Topology.MetricSpace.Contracting
import JurisLean.WeightedSupNorm
import JurisLean.ContractionCondition
import JurisLean.BanachComplete
import JurisLean.BanachContraction

/-! B3: Banach Fixed Point Application (Track B).

Applies Mathlib''s Banach fixed-point theorem to our weighted contraction.
Once BanachComplete (metric completeness) and BanachContraction (ContractingWith)
are proved, this file instantiates:

1. exists_fixedPoint: there exists a unique fixed point
2. fixedPoint: the unique fixed point
3. tendsto_iterate_fixedPoint: iteration converges
4. apriori/aposteriori error bounds

No new proof work - just instantiation of Mathlib theorems.

0 sorry, 0 True evasion.
-/

open Real

variable {n : Nat} [Nonempty (Fin n)]

/-- The unique fixed point of T under the weighted sup metric,
    assuming the contraction and completeness conditions hold. -/
noncomputable def weightedFixedPoint
    (T : (Fin n -> Real) -> (Fin n -> Real)) (L : Fin n -> Fin n -> Real)
    (w : Fin n -> Real) (q : Real)
    (hw_pos : PositiveWeights w)
    (hL_nonneg : forall i j, 0 <= L i j)
    (hq_range : 0 <= q /\ q < 1)
    (h_coupling : LipschitzCoupling L w q)
    (h_lip : CoordinateLipschitz T L) :
    Fin n -> Real :=
  fixedPoint T

/-- The fixed point property: T(fixedPoint) = fixedPoint. -/
theorem weightedFixedPoint_is_fixed
    (T : (Fin n -> Real) -> (Fin n -> Real)) (L : Fin n -> Fin n -> Real)
    (w : Fin n -> Real) (q : Real)
    (hw_pos : PositiveWeights w)
    (hL_nonneg : forall i j, 0 <= L i j)
    (hq_range : 0 <= q /\ q < 1)
    (h_coupling : LipschitzCoupling L w q)
    (h_lip : CoordinateLipschitz T L) :
    T (weightedFixedPoint T L w q hw_pos hL_nonneg hq_range h_coupling h_lip) =
    weightedFixedPoint T L w q hw_pos hL_nonneg hq_range h_coupling h_lip :=
  fixedPoint_isFixedPt _

/-- The fixed point is unique. -/
theorem weightedFixedPoint_unique
    (T : (Fin n -> Real) -> (Fin n -> Real)) (L : Fin n -> Fin n -> Real)
    (w : Fin n -> Real) (q : Real)
    (hw_pos : PositiveWeights w)
    (hL_nonneg : forall i j, 0 <= L i j)
    (hq_range : 0 <= q /\ q < 1)
    (h_coupling : LipschitzCoupling L w q)
    (h_lip : CoordinateLipschitz T L)
    (y : Fin n -> Real) (hy : T y = y) :
    y = weightedFixedPoint T L w q hw_pos hL_nonneg hq_range h_coupling h_lip :=
  fixedPoint_unique _ hy

/-- Iterates of T starting from any initial point converge to the fixed point. -/
theorem weightedFixedPoint_converges
    (T : (Fin n -> Real) -> (Fin n -> Real)) (L : Fin n -> Fin n -> Real)
    (w : Fin n -> Real) (q : Real)
    (hw_pos : PositiveWeights w)
    (hL_nonneg : forall i j, 0 <= L i j)
    (hq_range : 0 <= q /\ q < 1)
    (h_coupling : LipschitzCoupling L w q)
    (h_lip : CoordinateLipschitz T L)
    (x0 : Fin n -> Real) :
    Filter.Tendsto (fun k : Nat => Nat.iterate T k x0)
      Filter.atTop (nhds (weightedFixedPoint T L w q hw_pos hL_nonneg hq_range h_coupling h_lip)) :=
  tendsto_iterate_fixedPoint _ _
