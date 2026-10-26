import JurisLean.Candidates.LearningConsumer20261027

#check JurisLean.Candidates.LearningConsumer20261027.u01_6_fit_card_minimizes_actual_sample
#print axioms JurisLean.Candidates.LearningConsumer20261027.u01_6_fit_card_minimizes_actual_sample

#check JurisLean.Candidates.LearningConsumer20261027.u01_6_reject_changed_model_contents
#print axioms JurisLean.Candidates.LearningConsumer20261027.u01_6_reject_changed_model_contents

#check JurisLean.Candidates.LearningConsumer20261027.u01_6_reject_changed_fit_scope
#print axioms JurisLean.Candidates.LearningConsumer20261027.u01_6_reject_changed_fit_scope

#check JurisLean.Candidates.LearningConsumer20261027.u01_6_reject_wrong_feature_width
#print axioms JurisLean.Candidates.LearningConsumer20261027.u01_6_reject_wrong_feature_width

#check JurisLean.Candidates.LearningConsumer20261027.u01_6_reject_invalid_failure_budget
#print axioms JurisLean.Candidates.LearningConsumer20261027.u01_6_reject_invalid_failure_budget

#check JurisLean.Candidates.LearningConsumer20261027.u01_6_actual_fit_output_is_consumed
#print axioms JurisLean.Candidates.LearningConsumer20261027.u01_6_actual_fit_output_is_consumed

#check JurisLean.Candidates.LearningConsumer20261027.u01_6_matching_calibration_reads_selected_table
#print axioms JurisLean.Candidates.LearningConsumer20261027.u01_6_matching_calibration_reads_selected_table

#check JurisLean.Candidates.LearningConsumer20261027.u01_6_successful_pipeline_uses_actual_empirical_minimizer
#print axioms JurisLean.Candidates.LearningConsumer20261027.u01_6_successful_pipeline_uses_actual_empirical_minimizer

open JurisLean.Candidates.Final20261021
open JurisLean.Candidates.LearningConsumer20261027

def fixtureProtocol : LearningProtocol :=
  ⟨⟨1, 2, 3, 4, 5, ⟨10⟩, ⟨1⟩⟩, 6, 7, 8, 9, 10, 11, 12, 1/10⟩

def fixtureCertificate (table : List ℚ) : TableCalibration :=
  ⟨fixtureProtocol, table, ⟨fixtureProtocol.fit, 1, 0, 20, 21, []⟩⟩

def fixtureRun (label : Bool) (certificateTable : List ℚ) : Result ℚ :=
  match fitThenCalibrationGate fixtureProtocol fixtureProtocol
    (fun score truth => if (score = 1) = truth then (0 : ℚ) else 1)
    [[0], [1]] (fun _ : Fin 2 => ((0 : Fin 1), label))
    (0 : Fin 1) (fixtureCertificate certificateTable) 0 true with
  | .known out => .known out.value
  | .unknown e => .unknown e
  | .rejected e => .rejected e
  | .conflict a b => .conflict a b

/-- info: JurisLean.Candidates.Final20261021.Result.known (0 : Rat) -/
#guard_msgs in
#eval fixtureRun false [0]

/-- info: JurisLean.Candidates.Final20261021.Result.known (1 : Rat) -/
#guard_msgs in
#eval fixtureRun true [1]

/-- info: JurisLean.Candidates.Final20261021.Result.unknown
  JurisLean.Candidates.Final20261021.Error.targetMismatch -/
#guard_msgs in
#eval fixtureRun true [0]
