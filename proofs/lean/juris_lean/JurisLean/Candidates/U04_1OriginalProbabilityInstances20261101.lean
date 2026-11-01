import JurisLean.Seams.Probability
import JurisLean.Candidates.U04_2SharpConditioning20261029

/-!
Frozen topic04 L89/L91/L93 only. Reuse the admitted rational-to-PMF bridge
and Mathlib's PMF/Measure inverse. The labels stay fixed. The finite space
has measurable singletons (hence the full power set); no cross-label
representation uniqueness or real-world dependence is asserted.
-/

noncomputable section
open MeasureTheory Set
open scoped BigOperators
open JurisLean.Seams.Probability

namespace JurisLean.Candidates.U04_1OriginalProbabilityInstances20261101

section FixedLabels
variable {K : Type} [Fintype K] [MeasurableSpace K] [MeasurableSingletonClass K]

/-- L93: extend the existing rational-to-PMF construction to its measure. -/
def fixedAtomMeasure (p : K → ℚ) (hp : ∀ k, 0 ≤ p k)
    (hp1 : ∑ k, p k = 1) : Measure K :=
  (finite_distribution_to_pmf p hp hp1).toMeasure

theorem fixed_atom_measure_is_probability (p : K → ℚ) (hp : ∀ k, 0 ≤ p k)
    (hp1 : ∑ k, p k = 1) : IsProbabilityMeasure (fixedAtomMeasure p hp hp1) := by
  unfold fixedAtomMeasure
  infer_instance

/-- L93: each labelled atom keeps its supplied rational mass. -/
theorem fixed_atom_measure_singleton (p : K → ℚ) (hp : ∀ k, 0 ≤ p k)
    (hp1 : ∑ k, p k = 1) (k : K) :
    fixedAtomMeasure p hp hp1 {k} = ENNReal.ofReal (p k : ℝ) := by
  change (finite_distribution_to_pmf p hp hp1).toMeasure {k} = _
  rw [(finite_distribution_to_pmf p hp hp1).toMeasure_apply_singleton
    k (measurableSet_singleton k)]
  exact finite_distribution_to_pmf_apply p hp hp1 k

/-- L93: uniqueness is on these same fixed labels, by the existing PMF injection. -/
theorem fixed_atom_measure_injective (p q : K → ℚ)
    (hp : ∀ k, 0 ≤ p k) (hq : ∀ k, 0 ≤ q k)
    (hp1 : ∑ k, p k = 1) (hq1 : ∑ k, q k = 1)
    (h : fixedAtomMeasure p hp hp1 = fixedAtomMeasure q hq hq1) : p = q := by
  apply finite_distribution_to_pmf_injective p q hp hq hp1 hq1
  exact PMF.toMeasure_injective h

/-- L93: a probability measure with these labelled atom masses is exactly the constructed measure. -/
theorem fixed_atom_measure_unique (p : K → ℚ) (hp : ∀ k, 0 ≤ p k)
    (hp1 : ∑ k, p k = 1) (μ : Measure K) [IsProbabilityMeasure μ]
    (hatom : ∀ k, μ {k} = ENNReal.ofReal (p k : ℝ)) :
    μ = fixedAtomMeasure p hp hp1 := by
  have hpmf : μ.toPMF = finite_distribution_to_pmf p hp hp1 := by
    ext k
    rw [Measure.toPMF_apply, finite_distribution_to_pmf_apply]
    exact hatom k
  calc
    μ = μ.toPMF.toMeasure := (Measure.toPMF_toMeasure μ).symm
    _ = fixedAtomMeasure p hp hp1 := congrArg PMF.toMeasure hpmf

/-- L93: conversely, any probability measure with rational atom masses on K
comes from normalized nonnegative rational weights. Normalization is proved,
not supplied as an extra conclusion-shaped premise. No Nonempty K is added. -/
theorem fixed_atom_measure_surjective (μ : Measure K) [IsProbabilityMeasure μ]
    (hrat : ∀ k, ∃ q : ℚ, 0 ≤ q ∧ μ {k} = ENNReal.ofReal (q : ℝ)) :
    ∃ (p : K → ℚ) (hp : ∀ k, 0 ≤ p k) (hp1 : ∑ k, p k = 1),
      fixedAtomMeasure p hp hp1 = μ := by
  classical
  choose p hp hatom using hrat
  have hsumE : ∑ k, ENNReal.ofReal (p k : ℝ) = 1 := by
    simpa only [tsum_fintype, Measure.toPMF_apply, hatom] using μ.toPMF.tsum_coe
  have hn : 0 ≤ ∑ k, (p k : ℝ) :=
    Finset.sum_nonneg (fun k _ => Rat.cast_nonneg.mpr (hp k))
  have hsumE' : ENNReal.ofReal (∑ k, (p k : ℝ)) = 1 := by
    rw [ENNReal.ofReal_sum_of_nonneg (fun k _ => Rat.cast_nonneg.mpr (hp k))]
    exact hsumE
  have hsumR : ∑ k, (p k : ℝ) = 1 := by
    simpa only [ENNReal.toReal_ofReal hn, ENNReal.toReal_one] using
      congrArg ENNReal.toReal hsumE'
  have hp1 : ∑ k, p k = 1 := by exact_mod_cast hsumR
  have hpmf : finite_distribution_to_pmf p hp hp1 = μ.toPMF := by
    ext k
    rw [finite_distribution_to_pmf_apply, Measure.toPMF_apply]
    exact (hatom k).symm
  refine ⟨p, hp, hp1, ?_⟩
  change (finite_distribution_to_pmf p hp hp1).toMeasure = μ
  rw [hpmf, Measure.toPMF_toMeasure]
end FixedLabels

-- L89: the same two-point space supports the equal and complementary couplings.
local instance : MeasurableSpace Bool := ⊤

private theorem half_nonneg : ∀ _ : Bool, 0 ≤ (1 / 2 : ℚ) := by
  intro b
  norm_num

private theorem half_sum : (∑ _ : Bool, (1 / 2 : ℚ)) = 1 := by
  norm_num [Fintype.sum_bool]

def fairBoolLaw : Measure Bool := fixedAtomMeasure (fun _ => (1 / 2 : ℚ)) half_nonneg half_sum

instance : IsProbabilityMeasure fairBoolLaw :=
  fixed_atom_measure_is_probability _ _ _

private theorem fairBool_atom (b : Bool) : fairBoolLaw {b} = (1 / 2 : ENNReal) := by
  change fixedAtomMeasure (fun _ : Bool => (1 / 2 : ℚ)) half_nonneg half_sum {b} = _
  rw [fixed_atom_measure_singleton]
  have hc : (((1 / 2 : ℚ) : ℝ)) = (1 / 2 : ℝ) := by norm_num
  rw [hc, ENNReal.ofReal_div_of_pos (by norm_num : 0 < (2 : ℝ))]
  norm_num

/-- L89: id, its copy, and its complement all have Bernoulli(1/2) marginals. -/
theorem two_couplings_same_marginals (b : Bool) :
    fairBoolLaw {w : Bool | w = b} = (1 / 2 : ENNReal) ∧
    fairBoolLaw {w : Bool | (!w) = b} = (1 / 2 : ENNReal) := by
  have hc : {w : Bool | (!w) = b} = {(!b)} := by
    ext w
    cases w <;> cases b <;> simp
  exact ⟨by simpa using fairBool_atom b, by rw [hc]; exact fairBool_atom (!b)⟩

/-- L89: same marginals, two different joint laws on this very same finite Ω. -/
theorem two_couplings_different_joints :
    fairBoolLaw {w : Bool | w = w} = 1 ∧
    fairBoolLaw {w : Bool | w = true ∧ w = true} = (1 / 2 : ENNReal) ∧
    fairBoolLaw {w : Bool | w = (!w)} = 0 ∧
    fairBoolLaw {w : Bool | w = true ∧ (!w) = true} = 0 := by
  have he : {w : Bool | w = (!w)} = ∅ := by
    ext w
    cases w <;> simp
  have hj : {w : Bool | w = true ∧ (!w) = true} = ∅ := by
    ext w
    cases w <;> simp
  have hs : {w : Bool | w = w} = (Set.univ : Set Bool) := by
    ext w
    simp
  refine ⟨by rw [hs]; exact measure_univ, ?_, by rw [he]; simp, by rw [hj]; simp⟩
  simpa using fairBool_atom true

/-- L91: instantiate the admitted common-space bound; these three constraints conflict. -/
theorem probability_one_constraints_incompatible {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (A B : Set Ω)
    (hA : MeasurableSet A) (hB : MeasurableSet B) :
    ¬ (μ.real A = 1 ∧ μ.real B = 1 ∧ μ.real (A ∩ B) = 0) := by
  rintro ⟨ha, hb, hab⟩
  have hu : μ.real Set.univ = 1 := by simp
  have hl := (U04_2SharpConditioning20261029.three_event_bounds
    μ A B Set.univ hA hB MeasurableSet.univ).1
  rw [Set.inter_univ, ha, hb, hu, hab] at hl
  norm_num at hl

/-- L93: normalizing scores does not identify a supplied target probability law. -/
theorem normalized_scores_do_not_identify_target :
    (1 : ℚ) / (1 + 1) = 1 / 2 ∧
    fairBoolLaw {true} = (1 / 2 : ENNReal) ∧
    (Measure.dirac true : Measure Bool) {true} = 1 ∧
    fairBoolLaw ≠ (Measure.dirac true : Measure Bool) := by
  have hd : (Measure.dirac true : Measure Bool) {true} = 1 := by simp
  refine ⟨by norm_num, fairBool_atom true, hd, ?_⟩
  intro h
  have hc := fairBool_atom true
  rw [h, hd] at hc
  have hcR := congrArg ENNReal.toReal hc
  norm_num [ENNReal.toReal_inv] at hcR

end JurisLean.Candidates.U04_1OriginalProbabilityInstances20261101
