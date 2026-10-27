import JurisLean.Candidates.PolicyEvaluation20261027

#check JurisLean.Candidates.PolicyEvaluation20261027.finite_policy_ipw
#print axioms JurisLean.Candidates.PolicyEvaluation20261027.finite_policy_ipw
#check JurisLean.Candidates.PolicyEvaluation20261027.rational_clipping_loss
#print axioms JurisLean.Candidates.PolicyEvaluation20261027.rational_clipping_loss
#check JurisLean.Candidates.PolicyEvaluation20261027.finite_clipping_bias_bound
#print axioms JurisLean.Candidates.PolicyEvaluation20261027.finite_clipping_bias_bound
#check JurisLean.Candidates.PolicyEvaluation20261027.unsupported_value_bounds
#print axioms JurisLean.Candidates.PolicyEvaluation20261027.unsupported_value_bounds
#check JurisLean.Candidates.PolicyEvaluation20261027.unsupported_completions_same_visible_law
#print axioms JurisLean.Candidates.PolicyEvaluation20261027.unsupported_completions_same_visible_law
#check JurisLean.Candidates.PolicyEvaluation20261027.original_policy_values_and_clipping
#print axioms JurisLean.Candidates.PolicyEvaluation20261027.original_policy_values_and_clipping
#check JurisLean.Candidates.PolicyEvaluation20261027.original_support_gap_sharp
#print axioms JurisLean.Candidates.PolicyEvaluation20261027.original_support_gap_sharp
#check JurisLean.Candidates.PolicyEvaluation20261027.support_gap_endpoints_observationally_compatible
#print axioms JurisLean.Candidates.PolicyEvaluation20261027.support_gap_endpoints_observationally_compatible
#check JurisLean.Candidates.PolicyEvaluation20261027.heterogeneous_values_change_with_population
#print axioms JurisLean.Candidates.PolicyEvaluation20261027.heterogeneous_values_change_with_population
#check JurisLean.Candidates.PolicyEvaluation20261027.missing_world_is_probability
#print axioms JurisLean.Candidates.PolicyEvaluation20261027.missing_world_is_probability
#check JurisLean.Candidates.PolicyEvaluation20261027.missing_outcome_visible_law_independent
#print axioms JurisLean.Candidates.PolicyEvaluation20261027.missing_outcome_visible_law_independent
#check JurisLean.Candidates.PolicyEvaluation20261027.missing_outcome_interval_sharp
#print axioms JurisLean.Candidates.PolicyEvaluation20261027.missing_outcome_interval_sharp
#check JurisLean.Candidates.PolicyEvaluation20261027.initial_logs_do_not_identify_terminal_value
#print axioms JurisLean.Candidates.PolicyEvaluation20261027.initial_logs_do_not_identify_terminal_value

#check JurisLean.Candidates.PolicyEvaluation20261027.bounded_policy_score_uniform
#print axioms JurisLean.Candidates.PolicyEvaluation20261027.bounded_policy_score_uniform
#check JurisLean.Candidates.PolicyEvaluation20261027.empirical_policy_winner_regret
#print axioms JurisLean.Candidates.PolicyEvaluation20261027.empirical_policy_winner_regret
#check JurisLean.Candidates.PolicyEvaluation20261027.bounded_policy_winner_probability
#print axioms JurisLean.Candidates.PolicyEvaluation20261027.bounded_policy_winner_probability

open JurisLean.Candidates.PolicyEvaluation20261027

/-- info: true -/
#guard_msgs in
#eval decide (policyValue groupMass loggingPolicy originalMean = 9/20 ∧ policyValue groupMass chooseOne originalMean = 11/20)

/-- info: true -/
#guard_msgs in
#eval decide (clippedValue groupMass loggingPolicy chooseOne originalMean 2 = 7/20 ∧ policyValue groupMass chooseOne originalMean - clippedValue groupMass loggingPolicy chooseOne originalMean 2 = 1/5)

/-- info: true -/
#guard_msgs in
#eval decide (policyValue groupMass chooseOne (fillUnsupported supportGapLogging originalMean 0) = 3/20 ∧ policyValue groupMass chooseOne (fillUnsupported supportGapLogging originalMean 1) = 13/20)

/-- info: true -/
#guard_msgs in
#eval decide (∀ x a y, bernoulliVisibleLaw groupMass supportGapLogging (fillUnsupported supportGapLogging originalMean 0) x a y = bernoulliVisibleLaw groupMass supportGapLogging (fillUnsupported supportGapLogging originalMean 1) x a y)

/-- info: true -/
#guard_msgs in
#eval decide (policyValue groupMass personalized originalMean = 3/4 ∧ policyValue shiftedMass chooseZero originalMean = 16/25 ∧ policyValue shiftedMass chooseOne originalMean = 2/5 ∧ policyValue shiftedMass personalized originalMean = 18/25)

/-- info: true -/
#guard_msgs in
#eval decide (∀ r report, missingVisibleMass 0 r report = missingVisibleMass 1 r report)

/-- info: true -/
#guard_msgs in
#eval decide (missingPopulationMean 0 = 1/2 ∧ missingPopulationMean 1 = 1 ∧ missingPopulationMean (1/2) = 3/4)

/-- info: true -/
#guard_msgs in
#eval decide ((∀ a, firstStageLog id a = firstStageLog Bool.not a) ∧ terminalValue id true = 1 ∧ terminalValue Bool.not true = 0)

