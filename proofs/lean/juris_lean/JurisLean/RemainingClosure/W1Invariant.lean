import JurisLean.RemainingClosure.W1Laws

/-!
Existence of an invariant law for the actual feedback kernel. Weak compactness
produces a subsequential limit. The proved W1 contraction makes successive
laws asymptotically equal, and the Feller property makes the limit invariant.
No W1 completeness API or invariant-law premise is assumed. CI_NOT_RUN.
-/
namespace LegalMath.RemainingClosure.W1Invariant

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal Topology
open LegalMath20261108.ClosedLoop LegalMath20261108.SequentialFeedback
open LegalMath20261108.UnifiedFeedbackBridge
open LegalMath20261110.FeedbackW1
open LegalMath.RemainingClosure.W1Transport LegalMath.RemainingClosure.W1Laws

noncomputable section

def orbit : ℕ → ProbabilityMeasure State
  | 0 => ⟨Measure.dirac (0,0),inferInstance⟩
  | n+1 => P (orbit n)

lemma orbit_supported (n : ℕ) : orbit n ∈ supportedLaws := by
  induction n with
  | zero => simp [orbit,supportedLaws,square]
  | succ n ih => exact P_supported (orbit n) ih

theorem successive_distance (n : ℕ) :
    distributionW1 (orbit (n+1):Measure State) (orbit n:Measure State) ≤
      (5:ℝ≥0∞)*(3/4:ℝ≥0∞)^n := by
  induction n with
  | zero =>
      simpa using distributionW1_le_five (orbit_supported 1) (orbit_supported 0)
  | succ n ih =>
      have h := generalW1Lift (orbit (n+1):Measure State) (orbit n:Measure State)
        inferInstance inferInstance (orbit_supported (n+1)) (orbit_supported n)
      change distributionW1 (orbit (n+2):Measure State) (orbit (n+1):Measure State) ≤
        (3/4:ℝ≥0∞)*distributionW1 (orbit (n+1):Measure State) (orbit n:Measure State) at h
      exact h.trans ((mul_le_mul_left' ih (3/4:ℝ≥0∞)).trans_eq (by rw [pow_succ]; ring))

lemma test_gap (μ ν : ProbabilityMeasure State) (hμ : μ ∈ supportedLaws)
    (hν : ν ∈ supportedLaws) (f : State →ᵇ ℝ) (C : ℝ) (hC : 0 < C)
    (hf : ∀ s t, |f s-f t| ≤ C*dstar s t) :
    |(∫ s, f s ∂(μ:Measure State))-(∫ t, f t ∂(ν:Measure State))| ≤
      C*(distributionW1 (μ:Measure State) (ν:Measure State)).toReal := by
  have finite : distributionW1 (μ:Measure State) (ν:Measure State) ≠ ∞ :=
    ne_top_of_le_ne_top (by norm_num) (distributionW1_le_five hμ hν)
  have h := (ENNReal.ofReal_le_iff_le_toReal
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top finite)).mp
      (distribution_test_bound f C hC hf)
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal hC.le] using h

theorem successive_integrals (f : State →ᵇ ℝ) (C : ℝ) (hC : 0 < C)
    (hf : ∀ s t, |f s-f t| ≤ C*dstar s t) :
    Tendsto (fun n => (∫ s, f s ∂(orbit (n+1):Measure State))-
      (∫ s, f s ∂(orbit n:Measure State))) atTop (𝓝 0) := by
  have bound (n : ℕ) :
      |(∫ s, f s ∂(orbit (n+1):Measure State))-(∫ s, f s ∂(orbit n:Measure State))| ≤
        C*(5*(3/4:ℝ)^n) := by
    have hreal := ENNReal.toReal_mono (by finiteness) (successive_distance n)
    norm_num [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_div] at hreal
    exact (test_gap _ _ (orbit_supported (n+1)) (orbit_supported n) f C hC hf).trans
      (mul_le_mul_of_nonneg_left hreal hC.le)
  rw [tendsto_zero_iff_abs_tendsto_zero]
  apply squeeze_zero (fun _ => abs_nonneg _) bound
  simpa using (tendsto_const_nhds.mul
    (tendsto_const_nhds.mul (tendsto_pow_atTop_nhds_zero_of_lt_one
      (by norm_num : (0:ℝ) ≤ 3/4) (by norm_num : (3/4:ℝ) < 1))))

theorem invariant_exists : ∃ μ : ProbabilityMeasure State, μ ∈ supportedLaws ∧ P μ = μ := by
  obtain ⟨μ,hμ,φ,hφ,hsub⟩ := supportedLaws_compact.tendsto_subseq orbit_supported
  have hshift : Tendsto (fun n => P (orbit (φ n))) atTop (𝓝 μ) := by
    apply tendsto_iff_forall_lipschitz_integral_tendsto.mpr
    intro f hbounded ⟨L,hL⟩
    let g : State →ᵇ ℝ := ⟨⟨f,hL.continuous⟩,hbounded⟩
    have hg := (successive_integrals g ((L:ℝ)+1) (by positivity)
      (lipschitz_dstar_bound f hL)).comp hφ.tendsto_atTop
    have ho := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hsub) g
    have ht := hg.add ho
    simpa only [Function.comp_def, orbit, sub_add_cancel, zero_add] using ht
  have hP : Tendsto (fun n => P (orbit (φ n))) atTop (𝓝 (P μ)) :=
    (continuous_P.tendsto μ).comp hsub
  exact ⟨μ,hμ,tendsto_nhds_unique hP hshift⟩

/-- The unchanged original existential-uniqueness target has both parts proved. -/
theorem uniqueInvariantLaw : uniqueInvariantLawTarget := by
  obtain ⟨μ,hμ,hm⟩ := invariant_exists
  refine ⟨(μ:Measure State), ⟨inferInstance,hμ,congrArg Subtype.val hm⟩, ?_⟩
  rintro ν ⟨hνprob,hν,hn⟩
  let νp : ProbabilityMeasure State := ⟨ν,hνprob⟩
  have hfix : P νp = νp := Subtype.ext hn
  exact congrArg Subtype.val (invariant_unique νp μ hν hμ hfix hm)

#print axioms successive_distance
#print axioms successive_integrals
#print axioms invariant_exists
#print axioms uniqueInvariantLaw

end
end LegalMath.RemainingClosure.W1Invariant
