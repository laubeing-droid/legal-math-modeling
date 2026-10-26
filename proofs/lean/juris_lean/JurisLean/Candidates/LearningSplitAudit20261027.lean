import JurisLean.Candidates.LearningSplit20261027

#check JurisLean.Candidates.LearningSplit20261027.u01_3_partition_membership
#print axioms JurisLean.Candidates.LearningSplit20261027.u01_3_partition_membership
#check JurisLean.Candidates.LearningSplit20261027.u01_3_same_measurement_cannot_cross
#print axioms JurisLean.Candidates.LearningSplit20261027.u01_3_same_measurement_cannot_cross
#check JurisLean.Candidates.LearningSplit20261027.u01_3_every_row_has_a_partition
#print axioms JurisLean.Candidates.LearningSplit20261027.u01_3_every_row_has_a_partition
#check JurisLean.Candidates.LearningSplit20261027.u01_3_duplicate_records_do_not_add_measurement_units
#print axioms JurisLean.Candidates.LearningSplit20261027.u01_3_duplicate_records_do_not_add_measurement_units
#check JurisLean.Candidates.LearningSplit20261027.u01_3_record_identifier_does_not_choose_partition
#print axioms JurisLean.Candidates.LearningSplit20261027.u01_3_record_identifier_does_not_choose_partition
#check JurisLean.Candidates.LearningSplit20261027.u01_3_grouped_split_does_not_certify_information
#print axioms JurisLean.Candidates.LearningSplit20261027.u01_3_grouped_split_does_not_certify_information

open JurisLean.Candidates.LearningSplit20261027

/-- info: true -/
#guard_msgs in
#eval decide (groupedSplit (fun unit => unit == 10)
  [leakedTrain, { leakedTrain with record := 99 }, leakedTest] =
  ([leakedTrain, { leakedTrain with record := 99 }], [leakedTest]))

/-- info: true -/
#guard_msgs in
#eval decide ((measurementUnits
  [leakedTrain, { leakedTrain with record := 99 }, leakedTest]).card = 2)
