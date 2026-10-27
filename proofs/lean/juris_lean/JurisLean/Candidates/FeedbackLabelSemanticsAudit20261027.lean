import JurisLean.Candidates.FeedbackLabelSemantics20261027

#check JurisLean.Candidates.FeedbackLabelSemantics20261027.confirmed_observation_has_fixed_target
#print axioms JurisLean.Candidates.FeedbackLabelSemantics20261027.confirmed_observation_has_fixed_target
#check JurisLean.Candidates.FeedbackLabelSemantics20261027.record_cell_preserves_target
#print axioms JurisLean.Candidates.FeedbackLabelSemantics20261027.record_cell_preserves_target
#check JurisLean.Candidates.FeedbackLabelSemantics20261027.observation_updates_preserve_target
#print axioms JurisLean.Candidates.FeedbackLabelSemantics20261027.observation_updates_preserve_target
#check JurisLean.Candidates.FeedbackLabelSemantics20261027.valid_correction_has_fixed_target
#print axioms JurisLean.Candidates.FeedbackLabelSemantics20261027.valid_correction_has_fixed_target
#check JurisLean.Candidates.FeedbackLabelSemantics20261027.corrections_preserve_target
#print axioms JurisLean.Candidates.FeedbackLabelSemantics20261027.corrections_preserve_target
#check JurisLean.Candidates.FeedbackLabelSemantics20261027.update_keeps_target_scope_and_external_catalog
#print axioms JurisLean.Candidates.FeedbackLabelSemantics20261027.update_keeps_target_scope_and_external_catalog
#check JurisLean.Candidates.FeedbackLabelSemantics20261027.finite_feedback_preserves_fixed_target
#print axioms JurisLean.Candidates.FeedbackLabelSemantics20261027.finite_feedback_preserves_fixed_target
#check JurisLean.Candidates.FeedbackLabelSemantics20261027.empty_journal_has_no_unreliable_active_label
#print axioms JurisLean.Candidates.FeedbackLabelSemantics20261027.empty_journal_has_no_unreliable_active_label
#check JurisLean.Candidates.FeedbackLabelSemantics20261027.actual_fitted_sample_is_target_correct
#print axioms JurisLean.Candidates.FeedbackLabelSemantics20261027.actual_fitted_sample_is_target_correct
#check JurisLean.Candidates.FeedbackLabelSemantics20261027.suggestions_fit_better_but_true_risk_worsens
#print axioms JurisLean.Candidates.FeedbackLabelSemantics20261027.suggestions_fit_better_but_true_risk_worsens

open JurisLean.Candidates.Final20261021
open JurisLean.Candidates.LearningConsumer20261027
open JurisLean.Candidates.LearningERM20261027
open JurisLean.Candidates.FeedbackLabelSemantics20261027

/-- info: true -/
#guard_msgs in
#eval decide (fittedOnSuggestions = Result.known ⟨twoPointProtocol, [1, 0], 2, 0⟩)

/-- info: true -/
#guard_msgs in
#eval decide (empiricalScore (tableLoss binaryLoss) pseudoData [0, 0] = (1/2 : ℚ) ∧
  empiricalScore (tableLoss binaryLoss) pseudoData [1, 0] = 0 ∧
  empiricalScore (tableLoss binaryLoss) trueData [0, 0] = (1/2 : ℚ) ∧
  empiricalScore (tableLoss binaryLoss) trueData [1, 0] = 1)
