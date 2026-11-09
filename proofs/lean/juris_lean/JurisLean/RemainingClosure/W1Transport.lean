import JurisLean.Review20261110.FeedbackW1

/-!
Measure couplings for the already defined feedback kernel. The finite cost,
the actual kernel, and the primal distance are reused without changing them.
Source only; CI_NOT_RUN until subject-bound evidence is recorded.
-/
namespace LegalMath.RemainingClosure.W1Transport

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open LegalMath20261108.ClosedLoop LegalMath20261108.SequentialFeedback
open LegalMath20261108.UnifiedFeedbackBridge
open LegalMath20261110.FeedbackW1

noncomputable section

def couplingAt (s t : State) (r : ℝ) : Measure (State × State) :=
  ENNReal.ofReal (1 - probability s - probability t + r) •
      Measure.dirac (after s false, after t false) +
    ENNReal.ofReal (probability t - r) •
      Measure.dirac (after s false, after t true) +
    ENNReal.ofReal (probability s - r) •
      Measure.dirac (after s true, after t false) +
    ENNReal.ofReal r • Measure.dirac (after s true, after t true)

lemma weight_nonneg (s t : State) (r : ℝ)
    (hr : admissible (probability s) (probability t) r) :
    0 ≤ 1-probability s-probability t+r ∧ 0 ≤ probability t-r ∧
      0 ≤ probability s-r ∧ 0 ≤ r := by
  rcases hr with ⟨h0,hp,hq,hl⟩
  exact ⟨by linarith, by linarith, by linarith, h0⟩

lemma couplingAt_fst (s t : State) (r : ℝ)
    (hr : admissible (probability s) (probability t) r) :
    (couplingAt s t r).map Prod.fst = step model s := by
  obtain ⟨h00,h01,h10,h11⟩ := weight_nonneg s t r hr
  rw [couplingAt, step_two_atoms]
  simp only [Measure.map_add _ _ measurable_fst, Measure.map_smul,
    Measure.map_dirac' measurable_fst, Prod.fst]
  rw [← add_smul, add_assoc, ← add_smul, ← ENNReal.ofReal_add h00 h01,
    ← ENNReal.ofReal_add h10 h11]
  congr 2 <;> ring

lemma couplingAt_snd (s t : State) (r : ℝ)
    (hr : admissible (probability s) (probability t) r) :
    (couplingAt s t r).map Prod.snd = step model t := by
  obtain ⟨h00,h01,h10,h11⟩ := weight_nonneg s t r hr
  rw [couplingAt, step_two_atoms]
  simp only [Measure.map_add _ _ measurable_snd, Measure.map_smul,
    Measure.map_dirac' measurable_snd, Prod.snd]
  rw [add_right_comm (_ + _) _, add_assoc, ← add_smul, ← add_smul,
    ← ENNReal.ofReal_add h00 h10, ← ENNReal.ofReal_add h01 h11]
  congr 2 <;> ring

lemma couplingAt_mem (s t : State) (r : ℝ)
    (hr : admissible (probability s) (probability t) r) :
    couplingAt s t r ∈ couplingMeasures (step model s) (step model t) :=
  ⟨couplingAt_fst s t r hr, couplingAt_snd s t r hr⟩

lemma couplingAt_cost (s t : State) (r : ℝ)
    (hr : admissible (probability s) (probability t) r) :
    (∫⁻ z, ENNReal.ofReal (dstar z.1 z.2) ∂couplingAt s t r) =
      ENNReal.ofReal (cost s t r) := by
  obtain ⟨h00,h01,h10,h11⟩ := weight_nonneg s t r hr
  simp only [couplingAt, lintegral_add_measure, lintegral_smul_measure,
    lintegral_dirac, smul_eq_mul]
  rw [← ENNReal.ofReal_mul h00, ← ENNReal.ofReal_mul h01,
    ← ENNReal.ofReal_mul h10, ← ENNReal.ofReal_mul h11]
  rw [← ENNReal.ofReal_add (mul_nonneg h00 (dstar_nonneg _ _))
    (mul_nonneg h01 (dstar_nonneg _ _)),
    ← ENNReal.ofReal_add
      (add_nonneg (mul_nonneg h00 (dstar_nonneg _ _))
        (mul_nonneg h01 (dstar_nonneg _ _))) (mul_nonneg h10 (dstar_nonneg _ _)),
    ← ENNReal.ofReal_add
      (add_nonneg (add_nonneg (mul_nonneg h00 (dstar_nonneg _ _))
        (mul_nonneg h01 (dstar_nonneg _ _))) (mul_nonneg h10 (dstar_nonneg _ _)))
      (mul_nonneg h11 (dstar_nonneg _ _))]
  rfl

def monotoneCoupling : Kernel (State × State) (State × State) where
  toFun := fun z => couplingAt z.1 z.2 (min (probability z.1) (probability z.2))
  measurable' := by
    unfold couplingAt
    have h1 : Measurable (fun z : State × State => probability z.1) :=
      measurable_probability.comp measurable_fst
    have h2 : Measurable (fun z : State × State => probability z.2) :=
      measurable_probability.comp measurable_snd
    have ha (b c : Bool) : Measurable (fun z : State × State => (after z.1 b, after z.2 c)) := by
      simp only [after_formula, learnExample]
      fun_prop
    apply Measure.measurable_of_measurable_coe
    intro B hB
    have hd (b c : Bool) : Measurable (fun z : State × State =>
        Measure.dirac (after z.1 b, after z.2 c) B) :=
      (Measure.measurable_coe hB).comp (measurable_dirac.comp (ha b c))
    simp only [Measure.add_apply, Measure.smul_apply, smul_eq_mul]
    exact ((((ENNReal.measurable_ofReal.comp
      (((measurable_const.sub h1).sub h2).add (h1.min h2))).mul (hd false false)).add
      ((ENNReal.measurable_ofReal.comp (h2.sub (h1.min h2))).mul (hd false true))).add
      ((ENNReal.measurable_ofReal.comp (h1.sub (h1.min h2))).mul (hd true false))).add
      ((ENNReal.measurable_ofReal.comp (h1.min h2)).mul (hd true true))

instance monotoneCoupling_markov : IsMarkovKernel monotoneCoupling where
  isProbabilityMeasure z := ⟨by
    have h := congrArg (fun μ : Measure State => μ Set.univ)
      (couplingAt_fst z.1 z.2 _ (monotone_admissible z.1 z.2))
    simpa only [Measure.map_apply measurable_fst MeasurableSet.univ,
      Set.preimage_univ, measure_univ] using h⟩

lemma measurable_dstar : Measurable (fun z : State × State => dstar z.1 z.2) := by
  unfold dstar
  fun_prop

lemma distributionW1_le_cost {μ ν : Measure State} (ρ : Measure (State × State))
    (hρ : ρ ∈ couplingMeasures μ ν) :
    distributionW1 μ ν ≤ ∫⁻ z, ENNReal.ofReal (dstar z.1 z.2) ∂ρ :=
  sInf_le ⟨ρ,hρ,rfl⟩

lemma transported_fst (ρ : Measure (State × State)) :
    (monotoneCoupling ∘ₘ ρ).map Prod.fst = step model ∘ₘ (ρ.map Prod.fst) := by
  ext B hB
  rw [Measure.map_apply measurable_fst hB,
    Measure.bind_apply (measurable_fst hB) monotoneCoupling.aemeasurable,
    Measure.bind_apply hB (step model).aemeasurable,
    lintegral_map ((step model).measurable_coe hB) measurable_fst]
  apply lintegral_congr_ae
  exact Filter.Eventually.of_forall fun z => by
    have hm := congrArg (fun μ : Measure State => μ B)
      (couplingAt_fst z.1 z.2 _ (monotone_admissible z.1 z.2))
    simpa [monotoneCoupling, Measure.map_apply measurable_fst hB] using hm

lemma transported_snd (ρ : Measure (State × State)) :
    (monotoneCoupling ∘ₘ ρ).map Prod.snd = step model ∘ₘ (ρ.map Prod.snd) := by
  ext B hB
  rw [Measure.map_apply measurable_snd hB,
    Measure.bind_apply (measurable_snd hB) monotoneCoupling.aemeasurable,
    Measure.bind_apply hB (step model).aemeasurable,
    lintegral_map ((step model).measurable_coe hB) measurable_snd]
  apply lintegral_congr_ae
  exact Filter.Eventually.of_forall fun z => by
    have hm := congrArg (fun μ : Measure State => μ B)
      (couplingAt_snd z.1 z.2 _ (monotone_admissible z.1 z.2))
    simpa [monotoneCoupling, Measure.map_apply measurable_snd hB] using hm

lemma coupling_supported {μ ν : Measure State} [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (hμ : μ square = 1) (hν : ν square = 1)
    {ρ : Measure (State × State)} (hρ : ρ ∈ couplingMeasures μ ν) :
    ∀ᵐ z ∂ρ, z.1 ∈ square ∧ z.2 ∈ square := by
  have hm : ∀ᵐ s ∂μ, s ∈ square := (mem_ae_iff_prob_eq_one measurable_square).mpr hμ
  have hn : ∀ᵐ s ∂ν, s ∈ square := (mem_ae_iff_prob_eq_one measurable_square).mpr hν
  have hmf : ∀ᵐ z ∂ρ, z.1 ∈ square := by
    apply (ae_map_iff measurable_fst.aemeasurable measurable_square).mp
    simpa only [hρ.1] using hm
  have hns : ∀ᵐ z ∂ρ, z.2 ∈ square := by
    apply (ae_map_iff measurable_snd.aemeasurable measurable_square).mp
    simpa only [hρ.2] using hn
  exact hmf.and hns

lemma transported_cost {μ ν : Measure State} [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (hμ : μ square = 1) (hν : ν square = 1)
    {ρ : Measure (State × State)} (hρ : ρ ∈ couplingMeasures μ ν) :
    (∫⁻ z, ENNReal.ofReal (dstar z.1 z.2) ∂(monotoneCoupling ∘ₘ ρ)) ≤
      (3/4 : ℝ≥0∞) * (∫⁻ z, ENNReal.ofReal (dstar z.1 z.2) ∂ρ) := by
  rw [Measure.lintegral_bind monotoneCoupling.aemeasurable
    (ENNReal.measurable_ofReal.comp measurable_dstar).aemeasurable]
  calc
    _ ≤ ∫⁻ z, (3/4 : ℝ≥0∞) * ENNReal.ofReal (dstar z.1 z.2) ∂ρ := by
      apply lintegral_mono_ae
      filter_upwards [coupling_supported hμ hν hρ] with z hz
      rw [show monotoneCoupling z = couplingAt z.1 z.2
        (min (probability z.1) (probability z.2)) from rfl,
        couplingAt_cost _ _ _ (monotone_admissible z.1 z.2)]
      have hc := ENNReal.ofReal_le_ofReal (one_step_contraction z.1 z.2 hz.1 hz.2)
      simpa only [ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 3/4),
        ENNReal.ofReal_div_of_pos (by norm_num : (0:ℝ) < 4),
        ENNReal.ofReal_ofNat] using hc
    _ = _ := lintegral_const_mul _ _

lemma distributionW1_eq_iInf (μ ν : Measure State) :
    distributionW1 μ ν = ⨅ ρ ∈ couplingMeasures μ ν,
      ∫⁻ z, ENNReal.ofReal (dstar z.1 z.2) ∂ρ := by
  simp only [distributionW1, sInf_image]

/-- This is the original arbitrary-input-law target, with no finite-law premise. -/
theorem generalW1Lift : generalW1LiftTarget := by
  intro μ ν hμprob hνprob hμ hν
  letI : IsProbabilityMeasure μ := hμprob
  letI : IsProbabilityMeasure ν := hνprob
  rw [distributionW1_eq_iInf μ ν,
    ENNReal.mul_iInf_of_ne (by norm_num) (by norm_num)]
  refine le_iInf fun ρ => ?_
  rw [ENNReal.mul_iInf_of_ne (by norm_num) (by norm_num)]
  refine le_iInf fun hρ => ?_
  have ht : monotoneCoupling ∘ₘ ρ ∈
      couplingMeasures (step model ∘ₘ μ) (step model ∘ₘ ν) := by
    constructor
    · rw [transported_fst, hρ.1]
    · rw [transported_snd, hρ.2]
  exact (distributionW1_le_cost _ ht).trans (transported_cost hμ hν hρ)

#print axioms couplingAt_fst
#print axioms couplingAt_snd
#print axioms couplingAt_cost
#print axioms transported_cost
#print axioms generalW1Lift

end
end LegalMath.RemainingClosure.W1Transport
