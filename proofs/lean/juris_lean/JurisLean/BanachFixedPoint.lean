import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Mathlib.Topology.MetricSpace.Contracting
import JurisLean.WeightedSupNorm
import JurisLean.ContractionCondition
import JurisLean.BanachComplete
import JurisLean.BanachContraction
/-! B3: Banach Fixed Point Application (Track B).
0 sorry, 0 True evasion.
-/
open Real
variable {n : Nat} [Nonempty (Fin n)]
theorem weighted_fixed_point_exists
    (T : (Fin n -> Real) -> (Fin n -> Real)) (L : Fin n -> Fin n -> Real)
    (w : Fin n -> Real) (q : Real)
    (hw_pos : PositiveWeights w)
    (hL_nonneg : forall i j, 0 <= L i j)
    (hq_nonneg : 0 <= q)
    (hq_lt_one : q < 1)
    (h_coupling : LipschitzCoupling L w q)
    (h_lip : CoordinateLipschitz T L) :
    exists! x : Fin n -> Real, T x = x := by
  letI : MetricSpace (Fin n -> Real) := weightedMetricSpace w hw_pos
  have h_contracting : ContractingWith (Real.toNNReal q) T :=
    weighted_contraction_implies_contracting_with T L w q hw_pos hL_nonneg hq_nonneg hq_lt_one h_coupling h_lip
  exact exists_fixedPoint T
noncomputable def weightedFixedPoint
    (T : (Fin n -> Real) -> (Fin n -> Real)) (L : Fin n -> Fin n -> Real)
    (w : Fin n -> Real) (q : Real)
    (hw_pos : PositiveWeights w)
    (hL_nonneg : forall i j, 0 <= L i j)
    (hq_nonneg : 0 <= q)
    (hq_lt_one : q < 1)
    (h_coupling : LipschitzCoupling L w q)
    (h_lip : CoordinateLipschitz T L) :
    Fin n -> Real :=
  fixedPoint T
theorem weightedFixedPoint_is_fixed
    (T : (Fin n -> Real) -> (Fin n -> Real)) (L : Fin n -> Fin n -> Real)
    (w : Fin n -> Real) (q : Real)
    (hw_pos : PositiveWeights w)
    (hL_nonneg : forall i j, 0 <= L i j)
    (hq_nonneg : 0 <= q)
    (hq_lt_one : q < 1)
    (h_coupling : LipschitzCoupling L w q)
    (h_lip : CoordinateLipschitz T L) :
    T (weightedFixedPoint T L w q hw_pos hL_nonneg hq_nonneg hq_lt_one h_coupling h_lip) =
    weightedFixedPoint T L w q hw_pos hL_nonneg hq_nonneg hq_lt_one h_coupling h_lip := by
  letI : MetricSpace (Fin n -> Real) := weightedMetricSpace w hw_pos
  have h_contracting : ContractingWith (Real.toNNReal q) T :=
    weighted_contraction_implies_contracting_with T L w q hw_pos hL_nonneg hq_nonneg hq_lt_one h_coupling h_lip
  exact fixedPoint_isFixedPt _
theorem weightedFixedPoint_unique
    (T : (Fin n -> Real) -> (Fin n -> Real)) (L : Fin n -> Fin n -> Real)
    (w : Fin n -> Real) (q : Real)
    (hw_pos : PositiveWeights w)
    (hL_nonneg : forall i j, 0 <= L i j)
    (hq_nonneg : 0 <= q)
    (hq_lt_one : q < 1)
    (h_coupling : LipschitzCoupling L w q)
    (h_lip : CoordinateLipschitz T L)
    (y : Fin n -> Real) (hy : T y = y) :
    y = weightedFixedPoint T L w q hw_pos hL_nonneg hq_nonneg hq_lt_one h_coupling h_lip := by
  letI : MetricSpace (Fin n -> Real) := weightedMetricSpace w hw_pos
  have h_contracting : ContractingWith (Real.toNNReal q) T :=
    weighted_contraction_implies_contracting_with T L w q hw_pos hL_nonneg hq_nonneg hq_lt_one h_coupling h_lip
  exact fixedPoint_unique _ hy
theorem weightedFixedPoint_converges
    (T : (Fin n -> Real) -> (Fin n -> Real)) (L : Fin n -> Fin n -> Real)
    (w : Fin n -> Real) (q : Real)
    (hw_pos : PositiveWeights w)
    (hL_nonneg : forall i j, 0 <= L i j)
    (hq_nonneg : 0 <= q)
    (hq_lt_one : q < 1)
    (h_coupling : LipschitzCoupling L w q)
    (h_lip : CoordinateLipschitz T L)
    (x0 : Fin n -> Real) :
    Filter.Tendsto (fun k : Nat => Nat.iterate T k x0)
      Filter.atTop (nhds (weightedFixedPoint T L w q hw_pos hL_nonneg hq_nonneg hq_lt_one h_coupling h_lip)) := by
  letI : MetricSpace (Fin n -> Real) := weightedMetricSpace w hw_pos
  have h_contracting : ContractingWith (Real.toNNReal q) T :=
    weighted_contraction_implies_contracting_with T L w q hw_pos hL_nonneg hq_nonneg hq_lt_one h_coupling h_lip
  exact tendsto_iterate_fixedPoint _ _
