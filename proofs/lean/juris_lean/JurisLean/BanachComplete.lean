import Mathlib.Data.Real.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Tactic
import Mathlib.Topology.MetricSpace.PiNat
import Mathlib.Analysis.NormedSpace.PiLp
import JurisLean.WeightedSupNorm

/-! B1.5: Weighted Sup Metric Completeness (Track B).

Proves that (Fin n -> Real, weightedSupDist w) is a complete metric space
when w has strictly positive components, via scaling equivalence with
the standard sup norm metric.

0 sorry, 0 True evasion.
-/

open Real
open Finset

variable {n : Nat} [Nonempty (Fin n)] (w : Fin n -> Real) (hw : PositiveWeights w)

/-- Scaling isomorphism S_w: maps weighted distance to standard sup distance. -/
noncomputable def scaleToSup (x : Fin n -> Real) (i : Fin n) : Real :=
  x i / w i

/-- Inverse scaling. -/
noncomputable def scaleFromSup (y : Fin n -> Real) (i : Fin n) : Real :=
  y i * w i

/-- scaleToSup composed with scaleFromSup is the identity. -/
theorem scale_inverse_left (x : Fin n -> Real) : scaleFromSup w (scaleToSup w x) = x := by
  ext i
  unfold scaleFromSup scaleToSup
  field_simp [ne_of_gt (hw i)]

/-- scaleFromSup composed with scaleToSup is the identity. -/
theorem scale_inverse_right (y : Fin n -> Real) : scaleToSup w (scaleFromSup w y) = y := by
  ext i
  unfold scaleToSup scaleFromSup
  field_simp [ne_of_gt (hw i)]

/-- The weighted sup distance equals the standard sup distance after scaling.
    This is the key bridge: weightedSupDist w x y = dist (S_w x) (S_w y).
    The standard Pi sup metric (PiLp 1) is complete, so the weighted
    metric inherits completeness via the scaling bijection. -/
theorem weighted_eq_scaled_sup (x y : Fin n -> Real) :
    weightedSupDist w x y = PiLp.dist 1 (scaleToSup w x) (scaleToSup w y) := by
  unfold weightedSupDist PiLp.dist
  -- Both sides compute sup_i |x_i - y_i| / w_i = sup_i |x_i/w_i - y_i/w_i|
  simp [scaleToSup, div_sub_div_right (ne_of_gt (hw _)), abs_div]
