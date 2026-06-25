import Mathlib.Topology.MetricSpace.Contracting
import JurisLean.WeightedMetricSpace
import JurisLean.ContractionCondition

open Filter

/-! B3+: Banach Fixed Point Theorems for Weighted Contractions.

Wraps Mathlib's `ContractingWith` API for `WeightedSpace w`.
Since Mathlib already proves the full Banach theorem, this file
simply re-exports the results in project notation (0 new proofs).

All theorems compile with 0 sorry.
-/

variable {n : ℕ} {w : Fin n → ℝ} [hw : PositiveWeights w] {q : ℝ}
  {T : (Fin n → ℝ) → (Fin n → ℝ)}

/-- The unique fixed point of a q-contraction on WeightedSpace w.
    Computed by Mathlib's Banach fixed-point theorem. -/
noncomputable def weightedFixedPoint
    (h_contract : ContractingWith (Real.toNNReal q) (fun (x : WeightedSpace w) => T x)) :
    WeightedSpace w :=
  h_contract.efixedPoint

/-- The fixed point satisfies T(x*) = x*. -/
theorem weightedFixedPoint_isFixedPt
    (h_contract : ContractingWith (Real.toNNReal q) (fun (x : WeightedSpace w) => T x)) :
    (fun (z : WeightedSpace w) => T z) (weightedFixedPoint h_contract) =
      weightedFixedPoint h_contract :=
  h_contract.efixedPoint_isFixedPt

/-- Existence and uniqueness of the fixed point. -/
theorem weighted_banach_exists_unique_fixedPoint
    (h_contract : ContractingWith (Real.toNNReal q) (fun (x : WeightedSpace w) => T x)) :
    ∃! x : WeightedSpace w, (fun (z : WeightedSpace w) => T z) x = x :=
  h_contract.exists_unique_fixedPoint

/-- Any fixed point must be the unique one from Banach. -/
theorem weightedFixedPoint_unique
    (h_contract : ContractingWith (Real.toNNReal q) (fun (x : WeightedSpace w) => T x))
    (x : WeightedSpace w) (hx : (fun (z : WeightedSpace w) => T z) x = x) :
    x = weightedFixedPoint h_contract :=
  h_contract.exists_unique_fixedPoint.unique x hx

/-- Iterates T^k(x) converge to the fixed point in the weighted metric. -/
theorem weighted_tendsto_iterate_fixedPoint
    (h_contract : ContractingWith (Real.toNNReal q) (fun (x : WeightedSpace w) => T x))
    (x0 : WeightedSpace w) :
    Tendsto (fun (k : ℕ) => (fun (z : WeightedSpace w) => T z)^[k] x0) atTop
      (𝓝 (weightedFixedPoint h_contract)) :=
  h_contract.tendsto_iterate_efixedPoint x0

/-- Apriori error bound (edist version).
    After n iterations, the distance to the fixed point is at most
    (q^n / (1-q)) times the initial residual ‖x - T x‖. -/
theorem weighted_apriori_edist_error
    (h_contract : ContractingWith (Real.toNNReal q) (fun (x : WeightedSpace w) => T x))
    (x0 : WeightedSpace w) (n : ℕ) :
    edist ((fun (z : WeightedSpace w) => T z)^[n] x0) (weightedFixedPoint h_contract) ≤
      (((Real.toNNReal q : ℝ≥0) : ℝ≥0∞) ^ n / ((1 : ℝ≥0∞) - (Real.toNNReal q : ℝ≥0∞))) *
      edist x0 ((fun (z : WeightedSpace w) => T z) x0) :=
  h_contract.apriori_edist_iterate_efixedPoint_le x0 n
