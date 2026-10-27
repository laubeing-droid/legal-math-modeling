import JurisLean.Candidates.AdaptiveValidation20261027

#check JurisLean.Candidates.AdaptiveValidation20261027.conditional_event_mass
#print axioms JurisLean.Candidates.AdaptiveValidation20261027.conditional_event_mass
#check JurisLean.Candidates.AdaptiveValidation20261027.predictable_failure_budget
#print axioms JurisLean.Candidates.AdaptiveValidation20261027.predictable_failure_budget
#check JurisLean.Candidates.AdaptiveValidation20261027.history_budget_is_expected_spend
#print axioms JurisLean.Candidates.AdaptiveValidation20261027.history_budget_is_expected_spend
#check JurisLean.Candidates.AdaptiveValidation20261027.predictable_failure_expected_budget
#print axioms JurisLean.Candidates.AdaptiveValidation20261027.predictable_failure_expected_budget
#check JurisLean.Candidates.AdaptiveValidation20261027.fresh_iid_history_budget
#print axioms JurisLean.Candidates.AdaptiveValidation20261027.fresh_iid_history_budget
#check JurisLean.Candidates.AdaptiveValidation20261027.sample_count_covers_radius
#print axioms JurisLean.Candidates.AdaptiveValidation20261027.sample_count_covers_radius
#check JurisLean.Candidates.AdaptiveValidation20261027.probe_score_reveals_membership
#print axioms JurisLean.Candidates.AdaptiveValidation20261027.probe_score_reveals_membership
#check JurisLean.Candidates.AdaptiveValidation20261027.feedback_model_eq_unseen
#print axioms JurisLean.Candidates.AdaptiveValidation20261027.feedback_model_eq_unseen
#check JurisLean.Candidates.AdaptiveValidation20261027.feedback_model_zero_validation
#print axioms JurisLean.Candidates.AdaptiveValidation20261027.feedback_model_zero_validation
#check JurisLean.Candidates.AdaptiveValidation20261027.feedback_model_population_risk
#print axioms JurisLean.Candidates.AdaptiveValidation20261027.feedback_model_population_risk
#check JurisLean.Candidates.AdaptiveValidation20261027.feedback_model_large_population_risk
#print axioms JurisLean.Candidates.AdaptiveValidation20261027.feedback_model_large_population_risk
#check JurisLean.Candidates.AdaptiveValidation20261027.three_failure_events_not_independent_formula
#print axioms JurisLean.Candidates.AdaptiveValidation20261027.three_failure_events_not_independent_formula

namespace JurisLean.Candidates.AdaptiveValidationAudit20261027

open JurisLean.Candidates.AdaptiveValidation20261027

def visiblePoints : Finset (Fin 6) := {0, 1}

/-- info: true -/
#guard_msgs in
#eval (List.ofFn (probeScores visiblePoints) == [1/2, 1/2, 0, 0, 0, 0])

/-- info: true -/
#guard_msgs in
#eval (List.ofFn (fromProbeScores (probeScores visiblePoints)) ==
  [false, false, true, true, true, true])

/-- info: true -/
#guard_msgs in
#eval (zeroLabelValidationScore visiblePoints (fromProbeScores (probeScores visiblePoints)) == 0)

/-- info: true -/
#guard_msgs in
#eval (uniformZeroRisk (fromProbeScores (probeScores visiblePoints)) == 2/3)

/-- info: true -/
#guard_msgs in
#eval (fourPointFailureMass (fun w => decide (w.val < 3)) == 3/4 &&
  decide ((1 - (1 - (1/4 : ℚ))^3) < 3/4))

/-- info: true -/
#guard_msgs in
#eval ((List.ofFn fun i : Fin 3 =>
  fourPointFailureMass (fun w => decide (w.val = i.val))) == [1/4, 1/4, 1/4])

end JurisLean.Candidates.AdaptiveValidationAudit20261027
