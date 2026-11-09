import JurisLean.RemainingClosure.CNSemanticConnection
import JurisLean.RemainingClosure.W1Audit

set_option autoImplicit false

/-!
The actual CN episode law consumes the proved arbitrary-law W1 lift. The
projection reads the natively fitted and actually loaded table of the complete
source replay. This is a numerical projection theorem, not a contraction claim
about growing legal histories or a rational-valued invariant measure.
Source only; CI_NOT_RUN until subject-bound evidence exists.
-/
namespace LegalMath.RemainingClosure.UnifiedClosure

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open LegalMath20261108.ClosedLoop
open LegalMath20261108.UnifiedFeedbackBridge
open LegalMath20261110.FeedbackW1

open LegalMath.RemainingClosure.CNSemanticConnection.Numeric.Menu

noncomputable section

local instance : MeasurableSpace Log := ⊤

/-- Mixing arbitrary source states retains the same actual kernel exchange;
the source policies and histories are not replaced by independent marginals. -/
theorem actual_projected_law (state : ℚ × ℚ) (μ : Measure (Log × State)) :
    (step (sourceModel state) ∘ₘ μ).map (projection state) =
      step model ∘ₘ μ.map (projection state) := by
  have kernels : (step (sourceModel state)).map (projection state) =
      (step model).comap (projection state) (measurable_projection state) := by
    apply Kernel.ext
    intro s
    rw [Kernel.map_apply _ (measurable_projection state), Kernel.comap_apply]
    exact source_kernel_projection state s
  rw [Measure.map_comp μ _ (measurable_projection state), kernels,
    ← Kernel.comp_deterministic_eq_comap,
    ← Measure.comp_assoc, Measure.deterministic_comp_eq_map]

/-- The original generalW1LiftTarget is applied to the actual CN source law.
Only its numerical readout must lie in the original square. -/
theorem actual_source_law_contracts (state : ℚ × ℚ)
    (μ ν : Measure (Log × State)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : μ.map (projection state) square = 1)
    (hν : ν.map (projection state) square = 1) :
    distributionW1 ((step (sourceModel state) ∘ₘ μ).map (projection state))
        ((step (sourceModel state) ∘ₘ ν).map (projection state)) ≤
      (3/4 : ℝ≥0∞) * distributionW1 (μ.map (projection state)) (ν.map (projection state)) := by
  haveI : IsProbabilityMeasure (μ.map (projection state)) :=
    Measure.isProbabilityMeasure_map (measurable_projection state).aemeasurable
  haveI : IsProbabilityMeasure (ν.map (projection state)) :=
    Measure.isProbabilityMeasure_map (measurable_projection state).aemeasurable
  rw [actual_projected_law, actual_projected_law]
  exact W1Transport.generalW1Lift _ _ inferInstance inferInstance hμ hν

#print axioms actual_projected_law
#print axioms actual_source_law_contracts

end
end LegalMath.RemainingClosure.UnifiedClosure
