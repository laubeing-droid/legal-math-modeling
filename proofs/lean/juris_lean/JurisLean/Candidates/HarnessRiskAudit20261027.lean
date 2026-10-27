import JurisLean.Candidates.HarnessRisk20261027

#check JurisLean.Candidates.HarnessRisk20261027.conditional_risk_implies_expected_marginal
#print axioms JurisLean.Candidates.HarnessRisk20261027.conditional_risk_implies_expected_marginal
#check JurisLean.Candidates.HarnessRisk20261027.conditional_risk_implies_constant_marginal
#print axioms JurisLean.Candidates.HarnessRisk20261027.conditional_risk_implies_constant_marginal
#check JurisLean.Candidates.HarnessRisk20261027.finite_conditional_union_bound
#print axioms JurisLean.Candidates.HarnessRisk20261027.finite_conditional_union_bound
#check JurisLean.Candidates.HarnessRisk20261027.finite_adaptive_union_bound
#print axioms JurisLean.Candidates.HarnessRisk20261027.finite_adaptive_union_bound
#check JurisLean.Candidates.HarnessRisk20261027.countable_summable_risk_budget
#print axioms JurisLean.Candidates.HarnessRisk20261027.countable_summable_risk_budget
#check JurisLean.Candidates.HarnessRisk20261027.countable_conditional_risk_budget
#print axioms JurisLean.Candidates.HarnessRisk20261027.countable_conditional_risk_budget
#check JurisLean.Candidates.HarnessRisk20261027.bernoulli_coordinates_are_independent
#print axioms JurisLean.Candidates.HarnessRisk20261027.bernoulli_coordinates_are_independent
#check JurisLean.Candidates.HarnessRisk20261027.bernoulli_cylinder_probability
#print axioms JurisLean.Candidates.HarnessRisk20261027.bernoulli_cylinder_probability
#check JurisLean.Candidates.HarnessRisk20261027.bernoulli_one_attempt_risk
#print axioms JurisLean.Candidates.HarnessRisk20261027.bernoulli_one_attempt_risk
#check JurisLean.Candidates.HarnessRisk20261027.no_failure_is_the_false_cylinder
#print axioms JurisLean.Candidates.HarnessRisk20261027.no_failure_is_the_false_cylinder
#check JurisLean.Candidates.HarnessRisk20261027.independent_constant_risk_accumulates
#print axioms JurisLean.Candidates.HarnessRisk20261027.independent_constant_risk_accumulates
#check JurisLean.Candidates.HarnessRisk20261027.positive_constant_risk_has_no_fixed_subunit_horizon_limit
#print axioms JurisLean.Candidates.HarnessRisk20261027.positive_constant_risk_has_no_fixed_subunit_horizon_limit
#check JurisLean.Candidates.HarnessRisk20261027.two_attempts_are_not_one_budget
#print axioms JurisLean.Candidates.HarnessRisk20261027.two_attempts_are_not_one_budget

open JurisLean.Candidates.HarnessRisk20261027

namespace JurisLean.Candidates.HarnessRisk20261027.Audit

/-- info: true -/
#guard_msgs in
#eval decide (finitePaths (1/10) 0 = [([], 1)] ∧ enumeratedFailureMass (1/10) 0 = 0)

/-- info: true -/
#guard_msgs in
#eval decide (finitePaths (1/10) 1 = [([false], 9/10), ([true], 1/10)] ∧
  enumeratedFailureMass (1/10) 1 = 1/10)

/-- info: true -/
#guard_msgs in
#eval decide ((finitePaths (1/10) 5).length = 32 ∧
  ((finitePaths (1/10) 5).map Prod.snd).sum = 1 ∧
  enumeratedFailureMass (1/10) 5 = 40951/100000)

/-- info: true -/
#guard_msgs in
#eval decide (enumeratedFailureMass (1/100) 2 = 199/10000 ∧
  enumeratedFailureMass (1/100) 2 > 1/100)

/-- info: true -/
#guard_msgs in
#eval decide (enumeratedFailureMass 0 7 = 0 ∧ enumeratedFailureMass 1 7 = 1)

/-- info: true -/
#guard_msgs in
#eval decide (enumeratedFailureMass (1/2) 8 = 255/256 ∧
  ((finitePaths (1/2) 8).map Prod.snd).sum = 1)

/-- info: true -/
#guard_msgs in
#eval ([0, 1/10, 1/3, 1/2, 1] : List ℚ).all fun δ =>
  (List.range 9).all fun T => decide (enumeratedFailureMass δ T = 1 - (1 - δ)^T)

theorem resetting_the_per_attempt_number_is_not_a_total_bound (δ : ℝ)
    (positive : 0 < δ) (belowOne : δ < 1) : δ < 1 - (1 - δ)^2 := by
  have increase := mul_pos positive (sub_pos.mpr belowOne)
  nlinarith

theorem ten_percent_each_is_nineteen_percent_after_two :
    1 - (1 - (1/10 : ℝ))^2 = 19/100 ∧ (1/10 : ℝ) < 19/100 := by norm_num

end JurisLean.Candidates.HarnessRisk20261027.Audit

#check JurisLean.Candidates.HarnessRisk20261027.Audit.resetting_the_per_attempt_number_is_not_a_total_bound
#print axioms JurisLean.Candidates.HarnessRisk20261027.Audit.resetting_the_per_attempt_number_is_not_a_total_bound
#check JurisLean.Candidates.HarnessRisk20261027.Audit.ten_percent_each_is_nineteen_percent_after_two
#print axioms JurisLean.Candidates.HarnessRisk20261027.Audit.ten_percent_each_is_nineteen_percent_after_two
