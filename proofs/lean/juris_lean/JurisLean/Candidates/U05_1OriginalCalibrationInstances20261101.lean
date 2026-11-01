import JurisLean.Candidates.CalibrationSemantics20261027
import JurisLean.Candidates.U04_1OriginalProbabilityInstances20261101
import Mathlib.Probability.ProbabilityMassFunction.Integrals

/-!
Frozen original05.1 L87/L89/L91 only. Reuse the admitted conditional-expectation
and Brier results. The two finite instances use the admitted fair Bool measure;
no equivalence between arbitrary finite bucket predicates and CE is assumed.
For the normalized-score counterexample the rule is fixed before training:
raw weights (1,9), normalized positive score 9/(1+9), with both training and
test law equal to fairBoolLaw. No fit, training optimum or OOD guarantee is claimed.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators
open JurisLean.Seams.Probability
open JurisLean.Candidates.CalibrationSemantics20261027
open JurisLean.Candidates.U04_1OriginalProbabilityInstances20261101

namespace JurisLean.Candidates.U05_1OriginalCalibrationInstances20261101

/-- L87: binary outcome, the original actual-score range, and its sigma-field. -/
theorem conditional_correct_score_is_calibrated
    {Ω Input : Type*} [mΩ : MeasurableSpace Ω] [mInput : MeasurableSpace Input]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → Input) (hX : Measurable X) (score : Input → ℝ)
    (hscore : Measurable score) (Y : Ω → Bool)
    (_scoreRange : ∀ᵐ w ∂μ, 0 ≤ score (X w) ∧ score (X w) ≤ 1)
    (correct : μ[(fun w => if Y w then (1 : ℝ) else 0) |
      MeasurableSpace.comap X mInput] =ᵐ[μ] score ∘ X) :
    μ[(fun w => if Y w then (1 : ℝ) else 0) |
      MeasurableSpace.comap (score ∘ X) (inferInstance : MeasurableSpace ℝ)]
      =ᵐ[μ] score ∘ X := by
  have observedScore : Measurable[MeasurableSpace.comap X mInput] (score ∘ X) :=
    hscore.comp (comap_measurable X)
  exact q05_1_conditional_correct_implies_calibration μ _ _
    observedScore.comap_le hX.comap_le (fun w => if Y w then (1 : ℝ) else 0)
    (score ∘ X) (comap_measurable (score ∘ X)).aestronglyMeasurable correct

/-- L91: discharge the original binary/bounded L2 premises, then reuse the
conditional decomposition and minimum; integral_condExp gives the population objective. -/
theorem bounded_binary_brier_contract
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (m : MeasurableSpace Ω) (hm : m ≤ mΩ) (Y p : Ω → ℝ)
    (labelMeasurable : AEStronglyMeasurable Y μ)
    (scoreMeasurable : StronglyMeasurable[m] p)
    (binary : ∀ᵐ w ∂μ, Y w = 0 ∨ Y w = 1)
    (scoreRange : ∀ᵐ w ∂μ, 0 ≤ p w ∧ p w ≤ 1) :
    (μ[(Y - p) ^ 2 | m] =ᵐ[μ] Var[Y; μ | m] + (μ[Y | m] - p) ^ 2) ∧
    ((∫ w, (Y w - p w) ^ 2 ∂μ) =
      ∫ w, (Var[Y; μ | m]) w + ((μ[Y | m]) w - p w) ^ 2 ∂μ) ∧
    (∀ᵐ w ∂μ, (Var[Y; μ | m]) w ≤ (μ[(Y - p) ^ 2 | m]) w ∧
      ((Var[Y; μ | m]) w = (μ[(Y - p) ^ 2 | m]) w ↔ p w = (μ[Y | m]) w)) := by
  have hY : MemLp Y 2 μ := MemLp.of_bound labelMeasurable 1 <| by
    filter_upwards [binary] with w hw
    rcases hw with hw | hw <;> simp [hw]
  have ambientScore : Measurable p := scoreMeasurable.measurable.mono hm le_rfl
  have hp : MemLp p 2 μ := MemLp.of_bound ambientScore.aestronglyMeasurable 1 <| by
    filter_upwards [scoreRange] with w hw
    rw [Real.norm_eq_abs, abs_of_nonneg hw.1]
    exact hw.2
  have decomposition := q05_1_conditional_brier_decomposition μ m hm Y p hY hp scoreMeasurable
  refine ⟨decomposition, ?_,
    q05_1_conditional_brier_unique_optimum μ m hm Y p hY hp scoreMeasurable⟩
  calc
    (∫ w, (Y w - p w) ^ 2 ∂μ) = ∫ w, (μ[(Y - p) ^ 2 | m]) w ∂μ :=
      (integral_condExp hm).symm
    _ = ∫ w, (Var[Y; μ | m]) w + ((μ[Y | m]) w - p w) ^ 2 ∂μ :=
      integral_congr_ae decomposition

def fairLabel (b : Bool) : ℝ := if b then 1 else 0

private theorem fair_label_mean : (∫ b, fairLabel b ∂fairBoolLaw) = (1 / 2 : ℝ) := by
  unfold fairBoolLaw fixedAtomMeasure
  rw [PMF.integral_eq_sum]
  norm_num [Fintype.sum_bool, fairLabel, finite_distribution_to_pmf_apply]

private theorem fair_constant_score_condExp (c : ℝ) :
    fairBoolLaw[fairLabel | MeasurableSpace.comap (fun _ : Bool => c)
      (inferInstance : MeasurableSpace ℝ)] = fun _ => (1 / 2 : ℝ) := by
  rw [MeasurableSpace.comap_const, condExp_bot, fair_label_mean]

/-- L87 converse: X is the Bool input itself. The actual score CE is 1/2,
while the full-input CE is 0/1 and is not almost everywhere 1/2. -/
theorem population_calibration_not_conditional_correctness :
    (fairBoolLaw[fairLabel | MeasurableSpace.comap (fun _ : Bool => (1 / 2 : ℝ))
      (inferInstance : MeasurableSpace ℝ)] =ᵐ[fairBoolLaw] fun _ => (1 / 2 : ℝ)) ∧
    (fairBoolLaw[fairLabel | (inferInstance : MeasurableSpace Bool)] = fairLabel) ∧
    ¬ (fairBoolLaw[fairLabel | (inferInstance : MeasurableSpace Bool)]
      =ᵐ[fairBoolLaw] fun _ => (1 / 2 : ℝ)) := by
  have labelMeasurable : Measurable fairLabel := by
    unfold fairLabel
    fun_prop
  have labelL2 : MemLp fairLabel 2 fairBoolLaw :=
    MemLp.of_bound labelMeasurable.aestronglyMeasurable 1 <| by
      filter_upwards [] with b
      cases b <;> norm_num [fairLabel]
  have fullInput : fairBoolLaw[fairLabel | (inferInstance : MeasurableSpace Bool)] = fairLabel :=
    condExp_of_stronglyMeasurable le_rfl labelMeasurable.stronglyMeasurable
      (labelL2.integrable one_le_two)
  refine ⟨?, fullInput, ?_⟩
  · filter_upwards [] with b
    exact congrFun (fair_constant_score_condExp (1 / 2)) b
  · intro claimed
    rw [fullInput] at claimed
    obtain ⟨b, hb⟩ := claimed.exists
    cases b <;> norm_num [fairLabel] at hb

/-- L89 rule: fixed raw weights (1,9), with training=test=fairBoolLaw. -/
def normalizedRule (_ : Bool) : ℝ := 9 / (1 + 9)

/-- L89: normalization supplies the range but fails actual CE calibration. -/
theorem normalized_rule_not_calibrated :
    (∀ b : Bool, 0 ≤ normalizedRule b ∧ normalizedRule b ≤ 1) ∧
    ¬ (fairBoolLaw[fairLabel | MeasurableSpace.comap normalizedRule
      (inferInstance : MeasurableSpace ℝ)] =ᵐ[fairBoolLaw] normalizedRule) := by
  constructor
  · intro b
    norm_num [normalizedRule]
  · intro claimed
    have trueScoreMean :
        fairBoolLaw[fairLabel | MeasurableSpace.comap normalizedRule
          (inferInstance : MeasurableSpace ℝ)] =ᵐ[fairBoolLaw] fun _ => (1 / 2 : ℝ) := by
      filter_upwards [] with b
      exact congrFun (fair_constant_score_condExp (9 / (1 + 9))) b
    have mismatch := trueScoreMean.symm.trans claimed
    obtain ⟨b, hb⟩ := mismatch.exists
    norm_num [normalizedRule] at hb

end JurisLean.Candidates.U05_1OriginalCalibrationInstances20261101