import JurisLean.Candidates.SelectiveCalibration20261027

#check JurisLean.Candidates.SelectiveCalibration20261027.q05_3_selectPassing_spec
#print axioms JurisLean.Candidates.SelectiveCalibration20261027.q05_3_selectPassing_spec

#check JurisLean.Candidates.SelectiveCalibration20261027.q05_3_no_result_iff_no_threshold_passes
#print axioms JurisLean.Candidates.SelectiveCalibration20261027.q05_3_no_result_iff_no_threshold_passes

#check JurisLean.Candidates.SelectiveCalibration20261027.q05_3_empty_sample_refused
#print axioms JurisLean.Candidates.SelectiveCalibration20261027.q05_3_empty_sample_refused

#check JurisLean.Candidates.SelectiveCalibration20261027.q05_3_reject_all_has_no_certificate
#print axioms JurisLean.Candidates.SelectiveCalibration20261027.q05_3_reject_all_has_no_certificate

#check JurisLean.Candidates.SelectiveCalibration20261027.q05_3_simultaneous_numerator_and_coverage
#print axioms JurisLean.Candidates.SelectiveCalibration20261027.q05_3_simultaneous_numerator_and_coverage

#check JurisLean.Candidates.SelectiveCalibration20261027.q05_3_selected_threshold_has_population_risk_bound
#print axioms JurisLean.Candidates.SelectiveCalibration20261027.q05_3_selected_threshold_has_population_risk_bound

open JurisLean.Candidates.SelectiveCalibration20261027

/-- info: true -/
#guard_msgs in
#eval decide (calibrate (fun (_ : Bool) (_ : Unit) => 0)
  (fun h _ => h) [false, true] (fun _ : Fin 4 => ()) (1/10) (1/4) = some true)

/-- info: true -/
#guard_msgs in
#eval decide (calibrate (fun (_ : Bool) (_ : Unit) => 0)
  (fun _ _ => false) [false, true] (fun _ : Fin 4 => ()) (1/10) (1/4) = none)

/-- info: true -/
#guard_msgs in
#eval decide (calibrate (fun (_ : Bool) (_ : Unit) => 1)
  (fun _ _ => true) [false, true] (fun _ : Fin 4 => ()) (1/10) (1/4) = none)

/-- info: true -/
#guard_msgs in
#eval decide (calibrate (fun (_ : Bool) (_ : Unit) => 0)
  (fun _ _ => true) [false, true] (fun _ : Fin 0 => ()) (1/10) (1/4) = none)
