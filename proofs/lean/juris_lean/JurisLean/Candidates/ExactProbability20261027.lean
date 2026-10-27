import JurisLean.Candidates.Final20261021.Probability
import Mathlib.MeasureTheory.MeasurableSpace.Prod
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.Probability.Distributions.Beta

/-!
Exact additions required by original topic 04. A measurable deterministic copy
has the same generated information, not merely the same finite likelihood
example. Supplied numerator/denominator enclosures have an explicit width bound.
Source identity and the mechanism producing the supplied bounds remain external;
these statements do not identify a sampling law or implement quadrature.
-/

namespace JurisLean.Candidates.ExactProbability20261027

open MeasureTheory
open JurisLean.Candidates.Final20261021

theorem deterministic_copy_preserves_generated_information
    {Ω A B : Type*} [mA : MeasurableSpace A] [mB : MeasurableSpace B]
    (X : Ω → A) (g : A → B) (measurableCopy : Measurable g) :
    (mA.prod mB).comap (fun w => (X w, g (X w))) = mA.comap X := by
  rw [MeasurableSpace.comap_prodMk]
  apply sup_eq_left.mpr
  simpa only [MeasurableSpace.comap_comp, Function.comp_def] using
    (MeasurableSpace.comap_mono (g := X) measurableCopy.comap_le)

theorem deterministic_copy_keeps_integrable_conditional_expectation
    {Ω A B : Type*} [MeasurableSpace Ω] [mA : MeasurableSpace A] [mB : MeasurableSpace B]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → A) (g : A → B)
    (_observed : Measurable X) (measurableCopy : Measurable g)
    (target : Ω → ℝ) (_integrable : Integrable target μ) :
    μ[target | (mA.prod mB).comap (fun w => (X w, g (X w)))] =ᵐ[μ]
      μ[target | mA.comap X] := by
  rw [deterministic_copy_preserves_generated_information X g measurableCopy]

theorem supplied_enclosure_has_explicit_width_bound (N B nL nU bL bU : ℝ)
    (nonnegative : 0 ≤ N) (belowTotal : N ≤ B) (numeratorLower : nL ≤ N) (numeratorUpper : N ≤ nU)
    (denominatorPositive : 0 < bL) (denominatorLower : bL ≤ B) (denominatorUpper : B ≤ bU) :
    0 ≤ min 1 (nU / bL) - max 0 (nL / bU) ∧
      min 1 (nU / bL) - max 0 (nL / bU) ≤ 1 ∧
      min 1 (nU / bL) - max 0 (nL / bU) ≤
        (nU - nL) / bU + nU * (bU - bL) / (bL * bU) := by
  have enclosure := Probability.u04_2_enclosed_propagation N B nL nU bL bU
    nonnegative belowTotal numeratorLower numeratorUpper denominatorPositive denominatorLower denominatorUpper
  have upperPositive : 0 < bU := lt_of_lt_of_le denominatorPositive (denominatorLower.trans denominatorUpper)
  have unclipped : min 1 (nU / bL) - max 0 (nL / bU) ≤ nU / bL - nL / bU :=
    sub_le_sub (min_le_right _ _) (le_max_right _ _)
  have propagation : nU / bL - nL / bU =
      (nU - nL) / bU + nU * (bU - bL) / (bL * bU) := by
    field_simp [ne_of_gt denominatorPositive, ne_of_gt upperPositive]
    <;> ring
  refine ⟨sub_nonneg.mpr (enclosure.1.trans enclosure.2), ?_, unclipped.trans_eq propagation⟩
  have zeroLower : 0 ≤ max 0 (nL / bU) := le_max_left _ _
  have oneUpper : min 1 (nU / bL) ≤ 1 := min_le_left _ _
  linarith

open ProbabilityTheory
open scoped ENNReal

def bernoulliLikelihood (successes failures : Nat) (x : ℝ) : ℝ :=
  x ^ successes * (1 - x) ^ failures

noncomputable def betaEvidence (α β : ℝ) (successes failures : Nat) : ℝ :=
  beta (α + successes) (β + failures) / beta α β

theorem beta_evidence_is_positive (α β : ℝ) (positiveAlpha : 0 < α) (positiveBeta : 0 < β)
    (successes failures : Nat) : 0 < betaEvidence α β successes failures := by
  exact div_pos (beta_pos (by positivity) (by positivity)) (beta_pos positiveAlpha positiveBeta)

theorem real_beta_likelihood_density_identity (α β : ℝ)
    (positiveAlpha : 0 < α) (positiveBeta : 0 < β) (successes failures : Nat) (x : ℝ) :
    betaPDFReal α β x * bernoulliLikelihood successes failures x =
      betaEvidence α β successes failures * betaPDFReal (α + successes) (β + failures) x := by
  by_cases inside : 0 < x ∧ x < 1
  · have firstExponent : α + (successes : ℝ) - 1 = (α - 1) + (successes : ℝ) := by ring
    have secondExponent : β + (failures : ℝ) - 1 = (β - 1) + (failures : ℝ) := by ring
    have positiveOneMinus : 0 < 1 - x := by linarith [inside.2]
    have baseNonzero : beta α β ≠ 0 := ne_of_gt (beta_pos positiveAlpha positiveBeta)
    have updatedNonzero : beta (α + successes) (β + failures) ≠ 0 :=
      ne_of_gt (beta_pos (by positivity) (by positivity))
    simp only [betaPDFReal, if_pos inside, bernoulliLikelihood, betaEvidence,
      firstExponent, secondExponent,
      Real.rpow_add_natCast (ne_of_gt inside.1), Real.rpow_add_natCast (ne_of_gt positiveOneMinus)]
    field_simp [baseNonzero, updatedNonzero]
    <;> ring
  · simp only [betaPDFReal, if_neg inside, zero_mul, mul_zero]

theorem beta_likelihood_density_identity (α β : ℝ)
    (positiveAlpha : 0 < α) (positiveBeta : 0 < β) (successes failures : Nat) (x : ℝ) :
    betaPDF α β x * ENNReal.ofReal (bernoulliLikelihood successes failures x) =
      ENNReal.ofReal (betaEvidence α β successes failures) *
        betaPDF (α + successes) (β + failures) x := by
  have priorNonnegative : 0 ≤ betaPDFReal α β x := by
    by_cases inside : 0 < x ∧ x < 1
    · exact le_of_lt (betaPDFReal_pos inside.1 inside.2 positiveAlpha positiveBeta)
    · simp [betaPDFReal, inside]
  rw [betaPDF, betaPDF, ← ENNReal.ofReal_mul priorNonnegative,
    real_beta_likelihood_density_identity α β positiveAlpha positiveBeta,
    ENNReal.ofReal_mul (le_of_lt (beta_evidence_is_positive α β positiveAlpha positiveBeta successes failures))]

theorem beta_likelihood_normalization_integral (α β : ℝ)
    (positiveAlpha : 0 < α) (positiveBeta : 0 < β) (successes failures : Nat) :
    (∫⁻ x, betaPDF α β x * ENNReal.ofReal (bernoulliLikelihood successes failures x)) =
      ENNReal.ofReal (betaEvidence α β successes failures) := by
  simp_rw [beta_likelihood_density_identity α β positiveAlpha positiveBeta successes failures]
  rw [lintegral_const_mul' _ _ (by simp), lintegral_betaPDF_eq_one (by positivity) (by positivity), mul_one]

noncomputable def normalizedBetaLikelihood (α β : ℝ) (successes failures : Nat) (x : ℝ) : ℝ≥0∞ :=
  (∫⁻ y, betaPDF α β y * ENNReal.ofReal (bernoulliLikelihood successes failures y))⁻¹ *
    (betaPDF α β x * ENNReal.ofReal (bernoulliLikelihood successes failures x))

theorem positive_real_beta_posterior_density (α β : ℝ)
    (positiveAlpha : 0 < α) (positiveBeta : 0 < β) (successes failures : Nat) (x : ℝ) :
    normalizedBetaLikelihood α β successes failures x = betaPDF (α + successes) (β + failures) x := by
  rw [normalizedBetaLikelihood, beta_likelihood_normalization_integral α β positiveAlpha positiveBeta,
    beta_likelihood_density_identity α β positiveAlpha positiveBeta, ← mul_assoc,
    ENNReal.inv_mul_cancel (ne_of_gt (ENNReal.ofReal_pos.mpr
      (beta_evidence_is_positive α β positiveAlpha positiveBeta successes failures))) (by simp), one_mul]

theorem positive_real_beta_posterior_measure (α β : ℝ)
    (positiveAlpha : 0 < α) (positiveBeta : 0 < β) (successes failures : Nat) :
    volume.withDensity (normalizedBetaLikelihood α β successes failures) =
      betaMeasure (α + successes) (β + failures) := by
  change volume.withDensity (normalizedBetaLikelihood α β successes failures) =
    volume.withDensity (betaPDF (α + successes) (β + failures))
  congr 1
  funext x
  exact positive_real_beta_posterior_density α β positiveAlpha positiveBeta successes failures x

theorem beta_one_success_evidence_ratio (α β : ℝ) (positiveAlpha : 0 < α) (positiveBeta : 0 < β) :
    betaEvidence α β 1 0 = α / (α + β) := by
  have ratio := Probability.u04_1_real_gamma_weight_ratio α β positiveAlpha positiveBeta 1 0
  norm_num [JurisLean.FullMath.Probability.rising] at ratio
  simpa only [betaEvidence, beta, Nat.cast_one, Nat.cast_zero, add_zero,
    add_assoc, add_comm, add_left_comm] using ratio

-- This is the posterior mean of the Bernoulli parameter. Its interpretation as
-- a future success probability additionally requires the stated conditional
-- Bernoulli sampling bridge; no frequency-coverage claim follows from it.
theorem positive_real_beta_predictive_mean (α β : ℝ)
    (positiveAlpha : 0 < α) (positiveBeta : 0 < β) (successes failures : Nat) :
    (∫⁻ x, ENNReal.ofReal x * normalizedBetaLikelihood α β successes failures x) =
      ENNReal.ofReal ((α + successes) / ((α + successes) + (β + failures))) := by
  have updatedAlpha : 0 < α + (successes : ℝ) := by positivity
  have updatedBeta : 0 < β + (failures : ℝ) := by positivity
  have mass := beta_likelihood_normalization_integral (α + successes) (β + failures)
    updatedAlpha updatedBeta 1 0
  rw [beta_one_success_evidence_ratio _ _ updatedAlpha updatedBeta] at mass
  simp_rw [positive_real_beta_posterior_density α β positiveAlpha positiveBeta successes failures]
  simpa only [bernoulliLikelihood, pow_one, pow_zero, mul_one, mul_comm] using mass

end JurisLean.Candidates.ExactProbability20261027
