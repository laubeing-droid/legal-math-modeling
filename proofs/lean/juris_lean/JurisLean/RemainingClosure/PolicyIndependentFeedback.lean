import JurisLean.RemainingClosure.W1Transport

set_option autoImplicit false

/-!
For this original response kernel only, changing the permitted Bool policy
does not change the numerical feedback law: the physical outcome kernel and
both numerical updates ignore that action. This permits an actual learned
policy to consume the same contraction theorem. It does not alter the fair
finite-game instance or assert action-independence for other legal kernels.
Source only; CI_NOT_RUN.
-/
namespace LegalMath.RemainingClosure.PolicyIndependentFeedback

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open LegalMath20261108.ClosedLoop
open LegalMath20261108.UnifiedFeedbackBridge
open LegalMath20261110.FeedbackW1
open LegalMath.RemainingClosure.W1Transport

noncomputable section

def withPolicy (κ : Kernel State Bool) : Dynamics ℝ ℝ Bool Bool ℝ :=
  { model with policy := κ }

instance (κ : Kernel State Bool) [IsMarkovKernel κ] : IsMarkovKernel (withPolicy κ).policy := by
  change IsMarkovKernel κ
  infer_instance

instance (κ : Kernel State Bool) : IsMarkovKernel (withPolicy κ).outcome := by
  change IsMarkovKernel model.outcome
  infer_instance

theorem update_same (κ : Kernel State Bool) (s : State) (a y : Bool) :
    update (withPolicy κ) (s,(a,y)) = after s y := rfl

theorem step_atoms (κ : Kernel State Bool) [IsMarkovKernel κ] (s : State) :
    step (withPolicy κ) s =
      ENNReal.ofReal (1-probability s) • Measure.dirac (after s false) +
      ENNReal.ofReal (probability s) • Measure.dirac (after s true) := by
  classical
  ext B hB
  rw [step_apply (withPolicy κ) s hB, joint, Kernel.compProd_apply]
  · change (∫⁻ _a : Bool, coin s ((after s) ⁻¹' B) ∂κ s) = _
    rw [lintegral_const,measure_univ,mul_one]
    simp [coin,Measure.add_apply,smul_eq_mul,Set.indicator_apply]
  · exact ((measurable_update (withPolicy κ)).comp (measurable_const.prodMk measurable_id)) hB

theorem step_independent_of_policy (κ : Kernel State Bool) [IsMarkovKernel κ] :
    step (withPolicy κ) = step model := by
  ext s B hB
  rw [step_atoms,step_two_atoms]

/-- The arbitrary-input probability-law estimate remains the same proved
estimate when the next policy reads the actually updated private parameter. -/
theorem learned_policy_law_contraction (κ : Kernel State Bool) [IsMarkovKernel κ]
    (μ ν : Measure State) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : μ square=1) (hν : ν square=1) :
    distributionW1 (step (withPolicy κ) ∘ₘ μ) (step (withPolicy κ) ∘ₘ ν) ≤
      (3/4:ℝ≥0∞)*distributionW1 μ ν := by
  rw [step_independent_of_policy]
  exact generalW1Lift μ ν inferInstance inferInstance hμ hν

#print axioms update_same
#print axioms step_independent_of_policy
#print axioms learned_policy_law_contraction

end
end LegalMath.RemainingClosure.PolicyIndependentFeedback
