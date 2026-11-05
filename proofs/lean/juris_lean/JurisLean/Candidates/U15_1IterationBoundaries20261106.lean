import JurisLean.Candidates.AdaptiveValidation20261027
import JurisLean.Candidates.ProcedureClosure20261027

/-!
Original 15.1 L89 lacks a strict same-sample validation-score comparator for
the existing adaptive overfit. L91 lacks the rank premise derived from the
fixed finite model class and its actual target risk.
-/
namespace JurisLean.Candidates.U15_1IterationBoundaries20261106

open JurisLean.Candidates.AdaptiveValidation20261027

theorem validation_score_rises_while_target_risk_increases :
    let sample : Finset (Fin 6) := {0, 1}
    let baseline : Fin 6 → Bool := fun x => decide (x = 0)
    let selected := fromProbeScores (probeScores sample)
    1 - zeroLabelValidationScore sample baseline <
      1 - zeroLabelValidationScore sample selected ∧
    uniformZeroRisk baseline < uniformZeroRisk selected := by
  let sample : Finset (Fin 6) := {0, 1}
  let baseline : Fin 6 → Bool := fun x => decide (x = 0)
  let selected := fromProbeScores (probeScores sample)
  change 1 - zeroLabelValidationScore sample baseline <
      1 - zeroLabelValidationScore sample selected ∧
    uniformZeroRisk baseline < uniformZeroRisk selected
  have present : sample.Nonempty := ⟨0, by simp [sample]⟩
  have oldValidation : zeroLabelValidationScore sample baseline = 1/2 := by
    change zeroLabelValidationScore ({0, 1} : Finset (Fin 6)) (fun x => decide (x = 0)) = _
    decide +kernel
  have oldTarget : uniformZeroRisk baseline = 1/6 := by
    change uniformZeroRisk (fun x : Fin 6 => decide (x = 0)) = _
    decide +kernel
  have newValidation : zeroLabelValidationScore sample selected = 0 :=
    feedback_model_zero_validation sample present
  have newTarget : uniformZeroRisk selected = 2/3 := by
    have size : sample.card = 2 := by
      change ({0, 1} : Finset (Fin 6)).card = 2
      decide +kernel
    calc
      _ = 1 - (sample.card : ℚ) / 6 :=
        feedback_model_population_risk (by decide : 0 < 6) sample present
      _ = _ := by norm_num [size]
  rw [oldValidation, newValidation, oldTarget, newTarget]
  norm_num

theorem finite_class_excludes_infinite_strict_risk_decrease
    {Model : Type} (models : Finset Model) (risk : Model → ℝ) :
    ¬ ∃ path : Nat → {m // m ∈ models},
      ∀ k, risk (path (k + 1)).val < risk (path k).val := by
  classical
  let rank (model : {m // m ∈ models}) :=
    (models.filter (fun h => risk h < risk model.val)).card
  refine JurisLean.Candidates.ProcedureClosure20261027.strict_rank_excludes_infinite_execution
    rank (fun old next => risk next.val < risk old.val) ?_
  intro old next decrease
  change (models.filter (fun h => risk h < risk next.val)).card <
    (models.filter (fun h => risk h < risk old.val)).card
  apply Finset.card_lt_card
  refine ⟨?_, ?_⟩
  · intro x member
    obtain ⟨inClass, lower⟩ := Finset.mem_filter.mp member
    exact Finset.mem_filter.mpr ⟨inClass, lt_trans lower decrease⟩
  · intro backward
    have inLarger : next.val ∈ models.filter (fun h => risk h < risk old.val) :=
      Finset.mem_filter.mpr ⟨next.property, decrease⟩
    exact lt_irrefl (risk next.val) (Finset.mem_filter.mp (backward inLarger)).2

#check validation_score_rises_while_target_risk_increases
#print axioms validation_score_rises_while_target_risk_increases
#check finite_class_excludes_infinite_strict_risk_decrease
#print axioms finite_class_excludes_infinite_strict_risk_decrease

end JurisLean.Candidates.U15_1IterationBoundaries20261106
