import JurisLean.Candidates.HarnessRisk20261027

/-!
Frozen original05.6 L127: the actual adaptive-history false-alarm union bound.
Each `bad t` is the event emitted at step t under the complete history `past t`;
the conditional bound and summable alpha budget are explicit premises.
-/

open MeasureTheory ProbabilityTheory

example {Ω : Type*} [m₀ : MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (past : Nat → MeasurableSpace Ω)
    (information : ∀ t, past t ≤ m₀) (bad : Nat → Set Ω)
    (measurable : ∀ t, MeasurableSet (bad t)) (α : Nat → ℝ)
    (nonnegative : ∀ t, 0 ≤ α t) (summable : Summable α) (δ : ℝ)
    (total : (∑' t, α t) ≤ δ)
    (conditional : ∀ t, ∀ᵐ w ∂μ,
      (μ[(bad t).indicator (fun _ => (1 : ℝ)) | past t]) w ≤ α t) :
    μ.real (⋃ t, bad t) ≤ δ :=
  (JurisLean.Candidates.HarnessRisk20261027.countable_conditional_risk_budget
    μ past information bad measurable α nonnegative summable conditional).trans total

#print axioms JurisLean.Candidates.HarnessRisk20261027.conditional_risk_implies_constant_marginal
#print axioms JurisLean.Candidates.HarnessRisk20261027.finite_conditional_union_bound
#print axioms JurisLean.Candidates.HarnessRisk20261027.finite_adaptive_union_bound
#print axioms JurisLean.Candidates.HarnessRisk20261027.countable_conditional_risk_budget
#print axioms JurisLean.Candidates.HarnessRisk20261027.independent_constant_risk_accumulates
#print axioms JurisLean.Candidates.HarnessRisk20261027.positive_constant_risk_has_no_fixed_subunit_horizon_limit
