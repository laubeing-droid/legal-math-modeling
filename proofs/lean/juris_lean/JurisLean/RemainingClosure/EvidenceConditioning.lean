import JurisLean.CN.Completion20261105.Execution
import Mathlib.Probability.ConditionalProbability
import Mathlib.Probability.Kernel.Disintegration.Unique

/-!
Positive-mass conditioning, regular conditional kernels, null-fiber ambiguity,
and the actual admitted-information consumers. A null likelihood reports a
pending statistical update; it does not withdraw a legal evidence cell.
Source only; CI_NOT_RUN pending the exact subject build and axiom evidence.
-/
set_option autoImplicit false

namespace LegalMath20261110.RemainingClosure.EvidenceConditioning

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

noncomputable section

variable {Ω Z : Type*} [MeasurableSpace Ω] [MeasurableSpace Z]

theorem positive_event_conditioning (μ : Measure Ω) [IsFiniteMeasure μ]
    (E : Set Ω) (hE : MeasurableSet E) (positive : μ E ≠ 0) :
    IsProbabilityMeasure (ProbabilityTheory.cond μ E) ∧
      ∀ B : Set Ω, (ProbabilityTheory.cond μ E) B = (μ E)⁻¹ * μ (E ∩ B) :=
  ⟨cond_isProbabilityMeasure positive, fun B => cond_apply hE μ B⟩

/-- General standard-Borel conditional laws exist without a density model. -/
theorem regular_conditional_exists [StandardBorelSpace Ω] [Nonempty Ω]
    (joint : Measure (Z × Ω)) [IsFiniteMeasure joint] :
    ∃ κ : Kernel Z Ω, IsMarkovKernel κ ∧ joint.fst ⊗ₘ κ = joint :=
  ⟨joint.condKernel, by infer_instance, joint.disintegrate joint.condKernel⟩

/-- Uniqueness is marginal-almost-everywhere, never at every null observation. -/
theorem regular_conditional_unique_ae [StandardBorelSpace Ω] [Nonempty Ω]
    (joint : Measure (Z × Ω)) [IsFiniteMeasure joint]
    (κ : Kernel Z Ω) [IsFiniteKernel κ] (disintegrates : joint = joint.fst ⊗ₘ κ) :
    ∀ᵐ z ∂joint.fst, κ z = joint.condKernel z :=
  eq_condKernel_of_measure_eq_compProd κ disintegrates

/-- The positive-atom formula is derived from that same joint distribution. -/
theorem positive_observation_fiber [StandardBorelSpace Ω] [Nonempty Ω]
    [MeasurableSingletonClass Z] (joint : Measure (Z × Ω)) [IsFiniteMeasure joint]
    (z : Z) (positive : joint.fst {z} ≠ 0) (B : Set Ω) :
    joint.condKernel z B = (joint.fst {z})⁻¹ * joint ({z} ×ˢ B) :=
  Measure.condKernel_apply_of_ne_zero positive B

inductive UpdateStatus
  | conditioned
  | zeroMassPending
  deriving DecidableEq

/-- Preserve the prior on a zero-mass report and mark the unresolved update. -/
def conditionOn (μ : Measure Ω) (E : Set Ω) : UpdateStatus × Measure Ω := by
  classical
  exact if μ E = 0 then (.zeroMassPending,μ) else (.conditioned,ProbabilityTheory.cond μ E)

theorem zero_mass_keeps_prior (μ : Measure Ω) (E : Set Ω) (zero : μ E = 0) :
    conditionOn μ E = (.zeroMassPending,μ) := by simp [conditionOn, zero]

theorem positive_mass_updates (μ : Measure Ω) (E : Set Ω) (positive : μ E ≠ 0) :
    conditionOn μ E = (.conditioned,ProbabilityTheory.cond μ E) := by
  simp [conditionOn, positive]

theorem zero_mass_normalization_is_not_probability (μ : Measure Ω)
    (E : Set Ω) (zero : μ E = 0) :
    ProbabilityTheory.cond μ E = 0 ∧ ¬ IsProbabilityMeasure (ProbabilityTheory.cond μ E) := by
  have normalized := cond_eq_zero_of_meas_eq_zero (μ := μ) zero
  refine ⟨normalized, ?_⟩
  intro hp
  haveI := hp
  have mass := measure_univ (μ := ProbabilityTheory.cond μ E)
  simp [normalized] at mass

def nullVersion₀ : Kernel Bool Bool := Kernel.const Bool (Measure.dirac false)
def nullVersion₁ : Kernel Bool Bool := Kernel.deterministic id measurable_id

instance : IsMarkovKernel nullVersion₀ := by dsimp [nullVersion₀]; infer_instance
instance : IsMarkovKernel nullVersion₁ := by dsimp [nullVersion₁]; infer_instance

/-- Both kernels disintegrate exactly the same joint law and differ on its
zero-mass observation. This is a counterexample to pointwise uniqueness. -/
theorem null_observation_not_identified :
    (Measure.dirac false : Measure Bool) {true} = 0 ∧
      (Measure.dirac false : Measure Bool) ⊗ₘ nullVersion₀ = Measure.dirac (false,false) ∧
      (Measure.dirac false : Measure Bool) ⊗ₘ nullVersion₁ = Measure.dirac (false,false) ∧
      nullVersion₀ true ≠ nullVersion₁ true := by
  refine ⟨by simp, ?_, ?_, ?_⟩
  · ext B hB
    rw [Measure.dirac_compProd_apply hB]
    simp [nullVersion₀, Kernel.const_apply, Measure.dirac_apply' _ hB]
    rfl
  · ext B hB
    rw [Measure.dirac_compProd_apply hB]
    simp [nullVersion₁, Kernel.deterministic_apply, Measure.dirac_apply' _ hB]
    rfl
  · intro same
    have value := congrArg (fun ν : Measure Bool => ν {true}) same
    simp [nullVersion₀,nullVersion₁,Kernel.const_apply,Kernel.deterministic_apply] at value

section ActualConsumers
open JurisLean.KernelV3
open JurisLean.CN.Revision20261101
open JurisLean.CN.Completion20261105

/-- The existing native Bayesian calculation rejects a zero normalizer. -/
theorem actual_zero_likelihood_is_pending {n : Nat} (s : Situation) (c : EngineContext)
    (prior : Native.Prob.FiniteLaw (Fin n)) (likelihood : Fin n → ℚ)
    (event : Fin n → Ref .event)
    (zero : Native.Prob.expectation prior likelihood = 0) :
    (consumeProb s c prior likelihood event).native = .unknown .notIdentified ∧
      (consumeProb s c prior likelihood event).legal.after = s := by
  have normalized : Native.Prob.proposed_probability_model prior likelihood = none := by
    change (∑ w, prior.mass w * likelihood w) = 0 at zero
    unfold JurisLean.Candidates.Final20261021.Probability.proposed_probability_model
      JurisLean.Candidates.Final20261021.Probability.normalize
    simp [zero]
  unfold consumeProb
  split <;> simp [probabilitySource,normalized,relayNative,quiet]

/-- Exclusion preserves raw identity and blocks the actual stored engine input;
this is a legal-information operation, independent of numerical likelihood. -/
theorem excluded_material_stays_unusable (s : Situation) (c : EngineContext)
    (i : Ref .material) (raw : Raw i) (reason : Ref .document) (input : EngineMaterial)
    (excluded : s.core.state.E i = .excluded raw reason) (same : input.id = i)
    (stored : s.engineInputs.filter (fun record => record.id == i) = [input]) :
    (recordMaterial s i raw).after = s ∧
      (runBoundEngine s c i).native = none ∧ (runBoundEngine s c i).legal.after = s := by
  have notAdmitted : isAdmitted (s.core.state.E input.id) = false := by
    rw [same, excluded]
    rfl
  have blocked := unadmitted_engine_material_blocks s c input notAdmitted
  exact ⟨recorded_replay_keeps_exclusion s i raw reason excluded,
    by simp [runBoundEngine,stored,blocked,quiet],
    by simp [runBoundEngine,stored,blocked,quiet]⟩

/-- A retained old fit cannot bypass a later exclusion at the real learning step. -/
theorem excluded_report_cannot_reenter_learning (s : Situation) (r : Request)
    (i : Ref .material) (raw : Raw i) (reason : Ref .document) (report : EngineReport)
    (excluded : s.core.state.E i = .excluded raw reason)
    (same : report.material.id = i)
    (stored : s.engineResults.find? (fun item => item.material.id == i) = some report) :
    (learnReport s r i).after = s := by
  have notAdmitted : isAdmitted (s.core.state.E report.material.id) = false := by
    rw [same,excluded]
    rfl
  have blocked := unadmitted_engine_material_blocks s ⟨r.scope,report.material.target⟩
    report.material notAdmitted
  unfold learnReport
  split
  · rfl
  · simp [stored,blocked,quiet]

/-- An unknown proof result reaches the actual pending query branch; it does
not become false or authorize a legal disposition. -/
theorem unresolved_evidence_query_keeps_pending (s : Situation) (c : Law.Call)
    (body : Formula) (reason : UnknownKind)
    (allowed : automationAllowed s.core.state c.request.scope c.mode ≠ false)
    (unknown : proofAt s c body = .unknown reason) :
    (burdenEvidence s c body).answer = .unknown reason :=
  proofAt_unknown_reaches_query s c body reason allowed unknown

end ActualConsumers

#print axioms positive_event_conditioning
#print axioms regular_conditional_exists
#print axioms regular_conditional_unique_ae
#print axioms positive_observation_fiber
#print axioms null_observation_not_identified
#print axioms zero_mass_keeps_prior
#print axioms actual_zero_likelihood_is_pending
#print axioms excluded_material_stays_unusable
#print axioms excluded_report_cannot_reenter_learning

end
end LegalMath20261110.RemainingClosure.EvidenceConditioning
