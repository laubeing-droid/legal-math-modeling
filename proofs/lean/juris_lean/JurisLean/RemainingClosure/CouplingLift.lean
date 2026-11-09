import JurisLean.RemainingClosure.W1Transport

set_option autoImplicit false

/-! A state-space independent primal-coupling theorem. Its hypotheses are a
measurable point coupling and its local cost estimate, not the law-contraction
conclusion. The original feedback kernel is an actual consumer below.
Source only; CI_NOT_RUN. -/
namespace LegalMath.RemainingClosure.CouplingLift

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

noncomputable section

variable {S : Type*} [MeasurableSpace S]

def couplings (μ ν : Measure S) : Set (Measure (S × S)) :=
  {ρ | ρ.map Prod.fst=μ ∧ ρ.map Prod.snd=ν}

def primal (cost : S × S → ℝ≥0∞) (μ ν : Measure S) : ℝ≥0∞ :=
  sInf ((fun ρ => ∫⁻ z, cost z ∂ρ) '' couplings μ ν)

lemma primal_eq_iInf (cost : S × S → ℝ≥0∞) (μ ν : Measure S) :
    primal cost μ ν = ⨅ ρ ∈ couplings μ ν, ∫⁻ z, cost z ∂ρ := by
  simp only [primal,sInf_image]

lemma lifted_map (K : Kernel S S) (Γ : Kernel (S × S) (S × S))
    (f g : S × S → S) (hf : Measurable f) (hg : Measurable g)
    (commute : ∀ z, (Γ z).map f=K (g z)) (ρ : Measure (S × S)) :
    (Γ ∘ₘ ρ).map f=K ∘ₘ (ρ.map g) := by
  ext B hB
  rw [Measure.map_apply hf hB, Measure.bind_apply (hf hB) Γ.aemeasurable,
    Measure.bind_apply hB K.aemeasurable, lintegral_map (K.measurable_coe hB) hg]
  apply lintegral_congr_ae
  exact Filter.Eventually.of_forall fun z => by
    have h := congrArg (fun μ : Measure S => μ B) (commute z)
    simpa only [Measure.map_apply hf hB] using h

/-- Local geometry of an explicit coupling lifts to arbitrary probability laws.
No finite state space, linear update, or finite-support law is required. -/
theorem contraction_of_point_coupling (K : Kernel S S)
    (Γ : Kernel (S × S) (S × S)) (cost : S × S → ℝ≥0∞) (hcost : Measurable cost)
    (I : Set S) (hI : MeasurableSet I) (q : ℝ≥0)
    (fst_law : ∀ z, (Γ z).map Prod.fst=K z.1)
    (snd_law : ∀ z, (Γ z).map Prod.snd=K z.2)
    (point_bound : ∀ s ∈ I, ∀ t ∈ I,
      (∫⁻ z, cost z ∂Γ (s,t)) ≤ (q:ℝ≥0∞)*cost (s,t))
    (μ ν : Measure S) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : μ I=1) (hν : ν I=1) :
    primal cost (K ∘ₘ μ) (K ∘ₘ ν) ≤ (q:ℝ≥0∞)*primal cost μ ν := by
  have each (ρ : Measure (S × S)) (hρ : ρ ∈ couplings μ ν) :
      primal cost (K ∘ₘ μ) (K ∘ₘ ν) ≤ (q:ℝ≥0∞)*(∫⁻ z, cost z ∂ρ) := by
    have output : Γ ∘ₘ ρ ∈ couplings (K ∘ₘ μ) (K ∘ₘ ν) := by
      constructor
      · rw [lifted_map K Γ Prod.fst Prod.fst measurable_fst measurable_fst fst_law,hρ.1]
      · rw [lifted_map K Γ Prod.snd Prod.snd measurable_snd measurable_snd snd_law,hρ.2]
    have hm : ∀ᵐ z ∂ρ, z.1 ∈ I := by
      apply (ae_map_iff measurable_fst.aemeasurable hI).mp
      rw [hρ.1]
      exact (mem_ae_iff_prob_eq_one hI).mpr hμ
    have hn : ∀ᵐ z ∂ρ, z.2 ∈ I := by
      apply (ae_map_iff measurable_snd.aemeasurable hI).mp
      rw [hρ.2]
      exact (mem_ae_iff_prob_eq_one hI).mpr hν
    calc
      _ ≤ ∫⁻ z, cost z ∂(Γ ∘ₘ ρ) := by
        change sInf ((fun m : Measure (S × S) => ∫⁻ z, cost z ∂m) ''
          couplings (K ∘ₘ μ) (K ∘ₘ ν)) ≤ _
        exact sInf_le ⟨Γ ∘ₘ ρ,output,rfl⟩
      _ = ∫⁻ z, ∫⁻ z', cost z' ∂Γ z ∂ρ :=
        Measure.lintegral_bind Γ.aemeasurable hcost.aemeasurable
      _ ≤ ∫⁻ z, (q:ℝ≥0∞)*cost z ∂ρ := by
        apply lintegral_mono_ae
        filter_upwards [hm,hn] with z hz1 hz2
        exact point_bound z.1 hz1 z.2 hz2
      _ = _ := lintegral_const_mul _ hcost
  by_cases hq : q=0
  · have hp : μ.prod ν ∈ couplings μ ν := by constructor <;> simp
    simpa only [hq,ENNReal.coe_zero,zero_mul] using each (μ.prod ν) hp
  · have hq' : (q:ℝ≥0∞) ≠ 0 := by exact_mod_cast hq
    rw [primal_eq_iInf cost μ ν, ENNReal.mul_iInf_of_ne hq' ENNReal.coe_ne_top]
    refine le_iInf fun ρ => ?_
    rw [ENNReal.mul_iInf_of_ne hq' ENNReal.coe_ne_top]
    exact le_iInf fun hρ => each ρ hρ

section ActualFeedback
open LegalMath20261108.ClosedLoop LegalMath20261108.UnifiedFeedbackBridge
open LegalMath20261110.FeedbackW1
open LegalMath.RemainingClosure.W1Transport

/-- An actual consumer of the general theorem with the existing legal-feedback
cost, actual transition law and proved common-outcome coupling. -/
theorem actual_feedback_lift : generalW1LiftTarget := by
  intro μ ν hμp hνp hμ hν
  letI : IsProbabilityMeasure μ := hμp
  letI : IsProbabilityMeasure ν := hνp
  have ratio : ((3/4:ℝ≥0):ℝ≥0∞) = (3/4:ℝ≥0∞) := by
    rw [ENNReal.coe_div (by norm_num : (4:ℝ≥0) ≠ 0)]
    norm_num
  rw [← ratio]
  change primal (fun z => ENNReal.ofReal (dstar z.1 z.2))
      (step model ∘ₘ μ) (step model ∘ₘ ν) ≤
    ((3/4:ℝ≥0):ℝ≥0∞)*primal (fun z => ENNReal.ofReal (dstar z.1 z.2)) μ ν
  apply contraction_of_point_coupling (step model) monotoneCoupling
    (fun z => ENNReal.ofReal (dstar z.1 z.2))
    (ENNReal.measurable_ofReal.comp measurable_dstar) square measurable_square (3/4)
    (fun z => couplingAt_fst z.1 z.2 _ (monotone_admissible z.1 z.2))
    (fun z => couplingAt_snd z.1 z.2 _ (monotone_admissible z.1 z.2)) ?_ μ ν hμ hν
  intro s hs t ht
  change (∫⁻ z, ENNReal.ofReal (dstar z.1 z.2)
    ∂couplingAt s t (min (probability s) (probability t))) ≤ _
  rw [couplingAt_cost _ _ _ (monotone_admissible s t)]
  have h := ENNReal.ofReal_le_ofReal (one_step_contraction s t hs ht)
  rw [ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 3/4),
    ENNReal.ofReal_div_of_pos (by norm_num : (0:ℝ) < 4)] at h
  norm_num at h ⊢
  exact h

end ActualFeedback

#print axioms contraction_of_point_coupling
#print axioms actual_feedback_lift

end
end LegalMath.RemainingClosure.CouplingLift
