import JurisLean.Candidates.LearningEventSplit20261027

#check JurisLean.Candidates.LearningEventSplit20261027.u01_3_partition_membership
#print axioms JurisLean.Candidates.LearningEventSplit20261027.u01_3_partition_membership
#check JurisLean.Candidates.LearningEventSplit20261027.u01_3_same_event_cannot_cross
#print axioms JurisLean.Candidates.LearningEventSplit20261027.u01_3_same_event_cannot_cross
#check JurisLean.Candidates.LearningEventSplit20261027.u01_3_every_row_has_a_partition
#print axioms JurisLean.Candidates.LearningEventSplit20261027.u01_3_every_row_has_a_partition
#check JurisLean.Candidates.LearningEventSplit20261027.u01_3_duplicate_records_do_not_add_events
#print axioms JurisLean.Candidates.LearningEventSplit20261027.u01_3_duplicate_records_do_not_add_events
#check JurisLean.Candidates.LearningEventSplit20261027.u01_3_non_event_ids_do_not_choose_partition
#print axioms JurisLean.Candidates.LearningEventSplit20261027.u01_3_non_event_ids_do_not_choose_partition
#check JurisLean.Candidates.LearningEventSplit20261027.u01_3_event_split_does_not_certify_information
#print axioms JurisLean.Candidates.LearningEventSplit20261027.u01_3_event_split_does_not_certify_information

open JurisLean.Candidates.LearningEventSplit20261027

-- Same event, different measurement and record: all copies stay together.
/-- info: true -/
#guard_msgs in
#eval decide (eventSplit (fun event => event == 1)
  [leakedTrain, { leakedTrain with measurement := 99, record := 99 }, leakedTest] =
  ([leakedTrain, { leakedTrain with measurement := 99, record := 99 }], [leakedTest]))

/-- info: true -/
#guard_msgs in
#eval decide ((eventUnits
  [leakedTrain, { leakedTrain with measurement := 99, record := 99 }, leakedTest]).card = 2)
