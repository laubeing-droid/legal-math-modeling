import JurisLean.RemainingClosure.W1Atoms
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
import Mathlib.MeasureTheory.Measure.Portmanteau

set_option autoImplicit false

/-!
The primal cost separates probability laws. Compactness here is weak
compactness supplied by the pinned library, not an assumed W1-completeness
theorem. The actual two-atom feedback operator is Feller. Source: CI_NOT_RUN.
-/
namespace LegalMath.RemainingClosure.W1Laws

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open LegalMath20261108.ClosedLoop LegalMath20261108.SequentialFeedback
open LegalMath20261108.UnifiedFeedbackBridge
open LegalMath20261110.FeedbackW1
open LegalMath.RemainingClosure.W1Transport

noncomputable section

lemma coupling_probability {μ ν : Measure State} [IsProbabilityMeasure μ]
    {ρ : Measure (State × State)} (hρ : ρ ∈ couplingMeasures μ ν) : IsProbabilityMeasure ρ :=
  ⟨by
    have h := congrArg (fun m : Measure State => m Set.univ) hρ.1
    simpa only [Measure.map_apply measurable_fst MeasurableSet.univ,
      Set.preimage_univ, measure_univ] using h⟩

lemma dstar_le_five (s t : State) (hs : s ∈ square) (ht : t ∈ square) : dstar s t ≤ 5 := by
  have hx : |s.1-t.1| ≤ 1 := abs_le.mpr ⟨by linarith [hs.1.1,ht.1.2], by linarith [hs.1.2,ht.1.1]⟩
  have hp : |s.2-t.2| ≤ 1 := abs_le.mpr ⟨by linarith [hs.2.1,ht.2.2], by linarith [hs.2.2,ht.2.1]⟩
  unfold dstar
  linarith

lemma dist_le_dstar (s t : State) : dist s t ≤ dstar s t := by
  simp only [Prod.dist_eq, Real.dist_eq, dstar]
  have hx := abs_nonneg (s.1-t.1)
  have ht := abs_nonneg (s.2-t.2)
  exact max_le (by linarith) (by linarith)

theorem distributionW1_le_five {μ ν : Measure State} [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (hμ : μ square = 1) (hν : ν square = 1) :
    distributionW1 μ ν ≤ 5 := by
  have hp : μ.prod ν ∈ couplingMeasures μ ν := by
    constructor <;> simp
  apply (distributionW1_le_cost _ hp).trans
  calc
    _ ≤ ∫⁻ _z : State × State, (5 : ℝ≥0∞) ∂μ.prod ν := by
      apply lintegral_mono_ae
      filter_upwards [coupling_supported hμ hν hp] with z hz
      exact (ENNReal.ofReal_le_ofReal (dstar_le_five z.1 z.2 hz.1 hz.2)).trans_eq (by norm_num)
    _ = 5 := by simp

lemma coupling_test_bound {μ ν : Measure State} [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (f : State →ᵇ ℝ) (C : ℝ) (hC : 0 < C)
    (hf : ∀ s t, |f s-f t| ≤ C*dstar s t)
    {ρ : Measure (State × State)} (hρ : ρ ∈ couplingMeasures μ ν) :
    ENNReal.ofReal |(∫ s, f s ∂μ) - (∫ t, f t ∂ν)| ≤
      ENNReal.ofReal C * (∫⁻ z, ENNReal.ofReal (dstar z.1 z.2) ∂ρ) := by
  letI : IsProbabilityMeasure ρ := coupling_probability hρ
  have h1 : Integrable (fun z : State × State => f z.1) ρ :=
    (f.compContinuous ⟨Prod.fst,continuous_fst⟩).integrable ρ
  have h2 : Integrable (fun z : State × State => f z.2) ρ :=
    (f.compContinuous ⟨Prod.snd,continuous_snd⟩).integrable ρ
  have i1 : (∫ z : State × State, f z.1 ∂ρ) = ∫ s, f s ∂μ := by
    rw [← hρ.1]
    exact (integral_map measurable_fst.aemeasurable f.continuous.measurable.aestronglyMeasurable).symm
  have i2 : (∫ z : State × State, f z.2 ∂ρ) = ∫ s, f s ∂ν := by
    rw [← hρ.2]
    exact (integral_map measurable_snd.aemeasurable f.continuous.measurable.aestronglyMeasurable).symm
  have difference : (∫ z : State × State, (f z.1-f z.2) ∂ρ) =
      (∫ s, f s ∂μ) - (∫ t, f t ∂ν) := by rw [integral_sub h1 h2,i1,i2]
  calc
    _ = ‖∫ z : State × State, (f z.1-f z.2) ∂ρ‖ₑ := by
      rw [difference, Real.enorm_eq_ofReal_abs]
    _ ≤ ∫⁻ z : State × State, ‖f z.1-f z.2‖ₑ ∂ρ := enorm_integral_le_lintegral_enorm _
    _ ≤ ∫⁻ z : State × State, ENNReal.ofReal C * ENNReal.ofReal (dstar z.1 z.2) ∂ρ := by
      apply lintegral_mono
      intro z
      simpa only [Real.enorm_eq_ofReal_abs, ENNReal.ofReal_mul hC.le] using
        ENNReal.ofReal_le_ofReal (hf z.1 z.2)
    _ = _ := lintegral_const_mul _ (ENNReal.measurable_ofReal.comp measurable_dstar)

theorem distribution_test_bound {μ ν : Measure State} [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (f : State →ᵇ ℝ) (C : ℝ) (hC : 0 < C)
    (hf : ∀ s t, |f s-f t| ≤ C*dstar s t) :
    ENNReal.ofReal |(∫ s, f s ∂μ) - (∫ t, f t ∂ν)| ≤
      ENNReal.ofReal C * distributionW1 μ ν := by
  rw [distributionW1_eq_iInf,
    ENNReal.mul_iInf_of_ne (ENNReal.ofReal_ne_zero_iff.mpr hC) ENNReal.ofReal_ne_top]
  refine le_iInf fun ρ => ?_
  rw [ENNReal.mul_iInf_of_ne (ENNReal.ofReal_ne_zero_iff.mpr hC) ENNReal.ofReal_ne_top]
  exact le_iInf fun hρ => coupling_test_bound f C hC hf hρ

lemma lipschitz_dstar_bound (f : State → ℝ) {L : ℝ≥0} (hf : LipschitzWith L f) :
    ∀ s t, |f s-f t| ≤ ((L:ℝ)+1)*dstar s t := by
  intro s t
  calc
    _ = dist (f s) (f t) := (Real.dist_eq _ _).symm
    _ ≤ (L:ℝ)*dist s t := hf.dist_le_mul s t
    _ ≤ (L:ℝ)*dstar s t := mul_le_mul_of_nonneg_left (dist_le_dstar s t) L.coe_nonneg
    _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) (dstar_nonneg s t)

theorem distributionW1_separates (μ ν : ProbabilityMeasure State)
    (hz : distributionW1 (μ:Measure State) (ν:Measure State) = 0) : μ = ν := by
  apply tendsto_nhds_unique (l := atTop) (f := fun _n : ℕ => μ) tendsto_const_nhds
  apply tendsto_iff_forall_lipschitz_integral_tendsto.mpr
  intro f hbounded ⟨L,hL⟩
  let g : State →ᵇ ℝ := ⟨⟨f,hL.continuous⟩,hbounded⟩
  have hi := distribution_test_bound (μ := (μ:Measure State)) (ν := (ν:Measure State))
    g ((L:ℝ)+1) (by positivity) (lipschitz_dstar_bound f hL)
  rw [hz,mul_zero] at hi
  have hzero := ENNReal.ofReal_eq_zero.mp (le_antisymm hi (zero_le _))
  have heq : (∫ s, f s ∂(μ:Measure State)) = ∫ s, f s ∂(ν:Measure State) := by
    apply sub_eq_zero.mp
    exact abs_eq_zero.mp (le_antisymm hzero (abs_nonneg _))
  simpa only [heq] using
    (tendsto_const_nhds : Tendsto (fun _n : ℕ => ∫ s, f s ∂(μ:Measure State)) atTop
      (𝓝 (∫ s, f s ∂(μ:Measure State))))

def P (μ : ProbabilityMeasure State) : ProbabilityMeasure State :=
  ⟨step model ∘ₘ (μ:Measure State),inferInstance⟩

lemma continuous_probability : Continuous probability := by
  unfold probability responseExample
  fun_prop

def probabilityBCF : State →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup probability continuous_probability 1
    (fun s => by simpa [Real.norm_eq_abs, abs_of_nonneg (probability_bounds s).1] using
      (probability_bounds s).2)

def afterContinuous (y : Bool) : C(State, State) := ⟨fun s => after s y, by
  simp only [after_formula, learnExample]
  fun_prop⟩

def transfer (f : State →ᵇ ℝ) : State →ᵇ ℝ :=
  (1-probabilityBCF)*(f.compContinuous (afterContinuous false)) +
    probabilityBCF*(f.compContinuous (afterContinuous true))

lemma integral_P (μ : ProbabilityMeasure State) (f : State →ᵇ ℝ) :
    (∫ s, f s ∂(P μ:Measure State)) = ∫ s, transfer f s ∂(μ:Measure State) := by
  change (∫ s, f s ∂(step model ∘ₘ (μ:Measure State))) = _
  rw [integral_next (μ:Measure State) f (f.integrable _)]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun s => by rw [integral_step]; rfl

theorem continuous_P : Continuous P := by
  apply ProbabilityMeasure.continuous_iff_forall_continuous_integral.mpr
  intro f
  simpa only [integral_P] using
    ProbabilityMeasure.continuous_integral_boundedContinuousFunction (transfer f)

def supportedLaws : Set (ProbabilityMeasure State) := {μ | (μ:Measure State) square=1}

theorem supportedLaws_compact : IsCompact supportedLaws := by
  have hc := isCompact_setOf_probabilityMeasure_mass_eq_compl_isCompact_le
    (E := State) (u := fun _ : ℕ => (0:ℝ≥0)) (K := fun _ => square)
    tendsto_const_nhds (fun _ => isCompact_Icc.prod isCompact_Icc)
    (Or.inl (inferInstance : NormalSpace State))
  have heq : {μ : ProbabilityMeasure State | ∀ n : ℕ, μ squareᶜ ≤ (0:ℝ≥0)} =
      supportedLaws := by
    ext μ
    simp only [mem_setOf_eq, forall_const, nonpos_iff_eq_zero, supportedLaws]
    exact (ProbabilityMeasure.null_iff_toMeasure_null μ squareᶜ).trans
      (prob_compl_eq_zero_iff measurable_square)
  rwa [heq] at hc

theorem P_supported (μ : ProbabilityMeasure State) (hμ : μ ∈ supportedLaws) :
    P μ ∈ supportedLaws := by
  apply (mem_ae_iff_prob_eq_one measurable_square).mp
  exact next_supported (μ:Measure State) ((mem_ae_iff_prob_eq_one measurable_square).mpr hμ)

/-- Uniqueness uses the proved law-level contraction, not just mean stability. -/
theorem invariant_unique (μ ν : ProbabilityMeasure State)
    (hμ : μ ∈ supportedLaws) (hν : ν ∈ supportedLaws) (hm : P μ = μ) (hn : P ν = ν) :
    μ = ν := by
  have hc := generalW1Lift (μ:Measure State) (ν:Measure State) inferInstance inferInstance hμ hν
  change distributionW1 (P μ:Measure State) (P ν:Measure State) ≤
    (3/4:ℝ≥0∞)*distributionW1 (μ:Measure State) (ν:Measure State) at hc
  rw [hm,hn] at hc
  have hf : distributionW1 (μ:Measure State) (ν:Measure State) ≠ ∞ :=
    ne_top_of_le_ne_top (by norm_num) (distributionW1_le_five hμ hν)
  have hr := ENNReal.toReal_mono
    (ENNReal.mul_ne_top (ENNReal.div_ne_top (by norm_num) (by norm_num)) hf) hc
  simp only [ENNReal.toReal_mul, ENNReal.toReal_div, ENNReal.toReal_ofNat] at hr
  have zero : (distributionW1 (μ:Measure State) (ν:Measure State)).toReal=0 := by
    have nonneg := ENNReal.toReal_nonneg (a := distributionW1 (μ:Measure State) (ν:Measure State))
    linarith
  apply distributionW1_separates μ ν
  exact ((ENNReal.toReal_eq_zero_iff _).mp zero).resolve_right hf

#print axioms distribution_test_bound
#print axioms distributionW1_separates
#print axioms continuous_P
#print axioms supportedLaws_compact
#print axioms invariant_unique

end
end LegalMath.RemainingClosure.W1Laws
