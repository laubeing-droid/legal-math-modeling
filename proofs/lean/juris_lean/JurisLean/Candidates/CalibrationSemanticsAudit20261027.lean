import JurisLean.Candidates.CalibrationSemantics20261027

#check JurisLean.Candidates.CalibrationSemantics20261027.q05_1_conditional_correct_implies_calibration
#print axioms JurisLean.Candidates.CalibrationSemantics20261027.q05_1_conditional_correct_implies_calibration
#check JurisLean.Candidates.CalibrationSemantics20261027.q05_1_conditional_brier_decomposition
#print axioms JurisLean.Candidates.CalibrationSemantics20261027.q05_1_conditional_brier_decomposition
#check JurisLean.Candidates.CalibrationSemantics20261027.q05_1_conditional_brier_unique_optimum
#print axioms JurisLean.Candidates.CalibrationSemantics20261027.q05_1_conditional_brier_unique_optimum
#check JurisLean.Candidates.CalibrationSemantics20261027.q05_1_binary_conditional_variance
#print axioms JurisLean.Candidates.CalibrationSemantics20261027.q05_1_binary_conditional_variance
#check JurisLean.Candidates.CalibrationSemantics20261027.q05_1_binary_conditional_brier
#print axioms JurisLean.Candidates.CalibrationSemantics20261027.q05_1_binary_conditional_brier
#check JurisLean.Candidates.CalibrationSemantics20261027.q05_2_population_calibration_not_group_calibration
#print axioms JurisLean.Candidates.CalibrationSemantics20261027.q05_2_population_calibration_not_group_calibration
#check JurisLean.Candidates.CalibrationSemantics20261027.q05_1_normalized_score_not_calibrated
#print axioms JurisLean.Candidates.CalibrationSemantics20261027.q05_1_normalized_score_not_calibrated
#check JurisLean.Candidates.CalibrationSemantics20261027.q05_3_higher_cutoff_can_raise_risk
#print axioms JurisLean.Candidates.CalibrationSemantics20261027.q05_3_higher_cutoff_can_raise_risk

open JurisLean.Candidates.CalibrationSemantics20261027

/-- info: true -/
#guard_msgs in
#eval decide (groupRate balancedAtoms (fun _ => true) id = some (1/2))

/-- info: true -/
#guard_msgs in
#eval decide (groupRate balancedAtoms id id = some 1 ∧ groupRate balancedAtoms (fun w => !w) id = some 0)

/-- info: true -/
#guard_msgs in
#eval decide (groupRate balancedAtoms (fun _ => false) id = none)

/-- info: true -/
#guard_msgs in
#eval decide (groupRate balancedAtoms (fun w => decide ((1/2 : ℚ) ≤ confidenceScore w)) id = some (1/2) ∧
  groupRate balancedAtoms (fun w => decide ((1 : ℚ) ≤ confidenceScore w)) id = some 1)
