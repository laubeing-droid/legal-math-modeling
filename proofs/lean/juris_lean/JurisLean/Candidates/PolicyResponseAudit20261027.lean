import JurisLean.Candidates.PolicyResponse20261027

#check JurisLean.Candidates.PolicyResponse20261027.finite_response_payoffs
#print axioms JurisLean.Candidates.PolicyResponse20261027.finite_response_payoffs
#check JurisLean.Candidates.PolicyResponse20261027.score_only_cannot_distinguish_preparation
#print axioms JurisLean.Candidates.PolicyResponse20261027.score_only_cannot_distinguish_preparation
#check JurisLean.Candidates.PolicyResponse20261027.logit_is_original_softmax
#print axioms JurisLean.Candidates.PolicyResponse20261027.logit_is_original_softmax
#check JurisLean.Candidates.PolicyResponse20261027.logit_is_probability
#print axioms JurisLean.Candidates.PolicyResponse20261027.logit_is_probability
#check JurisLean.Candidates.PolicyResponse20261027.logit_actual_means
#print axioms JurisLean.Candidates.PolicyResponse20261027.logit_actual_means
#check JurisLean.Candidates.PolicyResponse20261027.logit_zero_means
#print axioms JurisLean.Candidates.PolicyResponse20261027.logit_zero_means
#check JurisLean.Candidates.PolicyResponse20261027.logit_high_rationality_limits
#print axioms JurisLean.Candidates.PolicyResponse20261027.logit_high_rationality_limits
#check JurisLean.Candidates.PolicyResponse20261027.affine_iterate_formula
#print axioms JurisLean.Candidates.PolicyResponse20261027.affine_iterate_formula
#check JurisLean.Candidates.PolicyResponse20261027.original_maps_and_unique_fixed_points
#print axioms JurisLean.Candidates.PolicyResponse20261027.original_maps_and_unique_fixed_points
#check JurisLean.Candidates.PolicyResponse20261027.affine_converges_to_center
#print axioms JurisLean.Candidates.PolicyResponse20261027.affine_converges_to_center
#check JurisLean.Candidates.PolicyResponse20261027.reflection_has_no_limit_except_center
#print axioms JurisLean.Candidates.PolicyResponse20261027.reflection_has_no_limit_except_center
#check JurisLean.Candidates.PolicyResponse20261027.damped_as_affine
#print axioms JurisLean.Candidates.PolicyResponse20261027.damped_as_affine
#check JurisLean.Candidates.PolicyResponse20261027.damped_preserves_unit_interval
#print axioms JurisLean.Candidates.PolicyResponse20261027.damped_preserves_unit_interval
#check JurisLean.Candidates.PolicyResponse20261027.damping_converges_for_all_iff
#print axioms JurisLean.Candidates.PolicyResponse20261027.damping_converges_for_all_iff
#check JurisLean.Candidates.PolicyResponse20261027.local_affine_behavior_does_not_give_global_contraction
#print axioms JurisLean.Candidates.PolicyResponse20261027.local_affine_behavior_does_not_give_global_contraction
#check JurisLean.Candidates.PolicyResponse20261027.stable_fixed_point_can_be_outside_legal_constraint
#print axioms JurisLean.Candidates.PolicyResponse20261027.stable_fixed_point_can_be_outside_legal_constraint
#check JurisLean.Candidates.PolicyResponse20261027.behavior_only_cannot_recover_admissible_sets
#print axioms JurisLean.Candidates.PolicyResponse20261027.behavior_only_cannot_recover_admissible_sets

open JurisLean.Candidates.PolicyResponse20261027

/-- info: true -/
#guard_msgs in
#eval decide (preparationUtility (1/2) 0 = 0 ∧ preparationUtility (1/2) 1 = 2/5 ∧ preparationUtility (1/2) 2 = 9/10)

/-- info: true -/
#guard_msgs in
#eval decide (preparationUtility 1 0 = 0 ∧ preparationUtility 1 1 = 2/5 ∧ preparationUtility 1 2 = 9/10)

/-- info: true -/
#guard_msgs in
#eval decide (preparationScore 1 = preparationScore 2 ∧ preparationQuality 1 = 1 ∧ preparationQuality 2 = 0)

/-- info: true -/
#guard_msgs in
#eval decide (((affineResponse (1/2 : ℚ))^[3] 0) = 7/16)

/-- info: true -/
#guard_msgs in
#eval decide (((affineResponse (-1 : ℚ))^[4] 0) = 0 ∧ ((affineResponse (-1 : ℚ))^[5] 0) = 1)

/-- info: true -/
#guard_msgs in
#eval decide (((dampedResponse (1/2 : ℚ))^[1] 0) = 1/2 ∧ ((dampedResponse (1/2 : ℚ))^[2] 1) = 1/2)

/-- info: true -/
#guard_msgs in
#eval decide (((dampedResponse (0 : ℚ))^[3] 0) = 0 ∧ ((dampedResponse (1 : ℚ))^[3] 0) = 1)

