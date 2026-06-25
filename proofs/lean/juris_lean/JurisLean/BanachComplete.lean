import Mathlib.Data.Real.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Tactic
import Mathlib.Data.ENNReal.Basic
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.MetricSpace.Basic
import JurisLean.WeightedSupNorm

/-! B1.5: Weighted Sup Metric Space (Track B).

Constructs a MetricSpace instance on (Fin n -> Real) using weightedSupDist.
The metric axioms (nonneg, triangle, symmetry, point separation) are already
proved in WeightedSupNorm.lean. This file assembles them into the MetricSpace
typeclass that Mathlib''s fixed-point API requires.

0 sorry, 0 True evasion.
-/

open Real
open Finset

variable {n : Nat} [Nonempty (Fin n)] (w : Fin n -> Real) (hw : PositiveWeights w)

/-- MetricSpace instance for (Fin n -> Real) under weightedSupDist.
    Uses the properties proved in WeightedSupNorm.lean:
    - weightedSupDist_nonneg
    - weightedSupDist_triangle
    - weightedSupDist_symm
    - weightedSupDist_complete (point separation) -/
noncomputable instance : MetricSpace (Fin n -> Real) where
  dist := weightedSupDist w
  edist := fun x y => ENNReal.ofReal (weightedSupDist w x y)
  dist_self x := by
    -- weightedSupDist w x x = 0 because |x_i - x_i| = 0 for all i
    rw [weightedSupDist]
    apply Finset.sup'_eq_zero
    intro i hi
    simp [sub_self, abs_zero, zero_div]
  dist_comm x y := weightedSupDist_symm w x y
  dist_triangle x y z := by
    apply weightedSupDist_triangle w hw x y z
  eq_of_dist_eq_zero {x y} h := by
    -- weightedSupDist_complete already proves d(x,y)=0 <-> x=y
    have hsep := weightedSupDist_complete w hw x y
    exact hsep.2.mp h
  edist_dist x y := rfl
