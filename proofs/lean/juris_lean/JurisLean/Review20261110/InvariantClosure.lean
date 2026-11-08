import JurisLean.FeedbackHistoryBridge

namespace LegalMath20261110.InvariantClosure

open MeasureTheory ProbabilityTheory
open LegalMath20261108.ClosedLoop
open scoped ENNReal

noncomputable section

lemma ae_of_mass_one {S : Type*} [MeasurableSpace S] (μ : Measure S) [IsProbabilityMeasure μ]
    (I : Set S) (hI : MeasurableSet I) (mass : μ I = 1) : ∀ᵐ s ∂μ, s ∈ I := by
  rw [ae_iff]
  change μ Iᶜ = 0
  rw [measure_compl hI (measure_ne_top μ I), measure_univ, mass, tsub_self]

variable {H Θ A O M : Type*}
  [MeasurableSpace H] [MeasurableSpace Θ] [MeasurableSpace A]
  [MeasurableSpace O] [MeasurableSpace M]
  (D : Dynamics H Θ A O M) [IsMarkovKernel D.policy] [IsMarkovKernel D.outcome]

theorem ae_invariant_iterations (μ₀ : Measure (H × Θ)) [IsProbabilityMeasure μ₀]
    (I : Set (H × Θ)) (hI : MeasurableSet I) (initial : μ₀ I = 1)
    (closed : ∀ s ∈ I, step D s I = 1) :
    ∀ n, ∀ᵐ s ∂iterationLaw D μ₀ n, s ∈ I := by
  intro n
  induction n with
  | zero => exact ae_of_mass_one μ₀ I hI initial
  | succ n ih =>
      change ∀ᵐ s ∂(step D ∘ₘ iterationLaw D μ₀ n), s ∈ I
      apply Measure.ae_comp_of_ae_ae hI
      filter_upwards [ih] with s hs
      exact ae_of_mass_one (step D s) I hI (closed s hs)

/-- Closure is required at every invariant state, not just almost everywhere
for an unrelated reference distribution. The conclusion uses the same path law. -/
theorem ae_invariant_path (μ₀ : Measure (H × Θ)) [IsProbabilityMeasure μ₀]
    (I : Set (H × Θ)) (hI : MeasurableSet I) (initial : μ₀ I = 1)
    (closed : ∀ s ∈ I, step D s I = 1) :
    ∀ᵐ path ∂pathLaw D μ₀, ∀ n, path n ∈ I := by
  apply ae_all_iff.mpr
  intro n
  have marginal : ∀ᵐ s ∂(pathLaw D μ₀).map (fun path => path n), s ∈ I := by
    rw [pathLaw_marginal]
    exact ae_invariant_iterations D μ₀ I hI initial closed n
  exact (ae_map_iff (measurable_pi_apply n).aemeasurable hI).mp marginal

def counterModel : Dynamics Bool Unit Bool Unit Unit where
  policy := Kernel.const (Bool × Unit) RepaymentExample.fair
  outcome := Kernel.const ((Bool × Unit) × Bool) (Measure.dirac ())
  append := fun _ a _ => a
  measure := fun _ _ _ => ()
  learn := fun _ _ => ()
  measurable_append := measurable_snd.fst
  measurable_measure := measurable_const
  measurable_learn := measurable_const

instance : IsMarkovKernel counterModel.policy := by
  change IsMarkovKernel (Kernel.const (Bool × Unit) RepaymentExample.fair)
  infer_instance

instance : IsMarkovKernel counterModel.outcome := by
  change IsMarkovKernel (Kernel.const ((Bool × Unit) × Bool) (Measure.dirac ()))
  infer_instance

theorem designated_action_keeps_state :
    update counterModel ((false, ()), (false, ())) = (false, ()) := rfl

theorem single_action_counterexample :
    step counterModel (false, ()) {(false, ())} = (1/2 : ℝ≥0∞) := by
  rw [step_apply _ _ (measurableSet_singleton _), joint, Kernel.compProd_apply]
  · norm_num [counterModel, Kernel.const_apply, RepaymentExample.fair, update,
      historyOut, parameterOut, feedback, Measure.add_apply, Measure.smul_apply,
      Measure.dirac_apply, Set.indicator_apply, smul_eq_mul]
  · exact ((measurable_update counterModel).comp
      (measurable_const.prodMk measurable_id)) (measurableSet_singleton _)

#print axioms ae_invariant_iterations
#print axioms ae_invariant_path
#print axioms designated_action_keeps_state
#print axioms single_action_counterexample

end
end LegalMath20261110.InvariantClosure
