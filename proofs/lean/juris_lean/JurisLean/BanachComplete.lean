import Mathlib.Data.Real.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Tactic
import Mathlib.Data.ENNReal.Basic
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.MetricSpace.Basic
import JurisLean.WeightedSupNorm
/-! B1.5: Weighted Sup Metric Space (Track B).
Generates a MetricSpace instance using weightedSupDist.
0 sorry, 0 True evasion.
-/
open Real
open Finset
variable {n : Nat} [Nonempty (Fin n)]
noncomputable def weightedMetricSpace (w : Fin n -> Real) (hw : PositiveWeights w) : MetricSpace (Fin n -> Real) where
  dist := weightedSupDist w
  edist := fun x y => ENNReal.ofReal (weightedSupDist w x y)
  dist_self x := by
    unfold weightedSupDist
    simp
  dist_comm x y := weightedSupDist_symm w x y
  dist_triangle x y z := weightedSupDist_triangle w hw x y z
  eq_of_dist_eq_zero {x y} h := by
    have hsep := weightedSupDist_complete w hw x y
    exact hsep.2.mp h
  edist_dist x y := rfl
