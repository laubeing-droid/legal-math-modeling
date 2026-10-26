import JurisLean.Candidates.LearningERM20261027

#check JurisLean.Candidates.LearningERM20261027.u01_1_actual_empirical_fit_minimizes
#print axioms JurisLean.Candidates.LearningERM20261027.u01_1_actual_empirical_fit_minimizes

#check JurisLean.Candidates.LearningERM20261027.u01_1_actual_fit_consumes_iid_oracle
#print axioms JurisLean.Candidates.LearningERM20261027.u01_1_actual_fit_consumes_iid_oracle

#check JurisLean.Candidates.LearningERM20261027.u01_1_empty_class_rejected
#print axioms JurisLean.Candidates.LearningERM20261027.u01_1_empty_class_rejected

#check JurisLean.Candidates.LearningERM20261027.u01_1_empty_sample_rejected
#print axioms JurisLean.Candidates.LearningERM20261027.u01_1_empty_sample_rejected

#check JurisLean.Candidates.LearningERM20261027.u01_1_fit_reads_actual_sample
#print axioms JurisLean.Candidates.LearningERM20261027.u01_1_fit_reads_actual_sample

open JurisLean.Candidates.LearningERM20261027

/-- info: some false -/
#guard_msgs in
#eval proposed_empirical_fit (fun (h z : Bool) => if h = z then (0 : ℚ) else 1)
  [false, true] (fun _ : Fin 2 => false)

/-- info: some true -/
#guard_msgs in
#eval proposed_empirical_fit (fun (h z : Bool) => if h = z then (0 : ℚ) else 1)
  [false, true] (fun _ : Fin 2 => true)

/-- info: none -/
#guard_msgs in
#eval proposed_empirical_fit (fun (h z : Bool) => if h = z then (0 : ℚ) else 1)
  [] (fun _ : Fin 2 => true)
