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

#check JurisLean.Candidates.LearningSplit20261027.measurement_split_agrees_with_event_split
#print axioms JurisLean.Candidates.LearningSplit20261027.measurement_split_agrees_with_event_split

#check JurisLean.Candidates.LearningSplit20261027.measurement_split_can_cross_one_event
#print axioms JurisLean.Candidates.LearningSplit20261027.measurement_split_can_cross_one_event

#check JurisLean.Candidates.LearningSplit20261027.count_weights_join
#print axioms JurisLean.Candidates.LearningSplit20261027.count_weights_join

#check JurisLean.Candidates.LearningSplit20261027.posterior_join_commutes
#print axioms JurisLean.Candidates.LearningSplit20261027.posterior_join_commutes

#check JurisLean.Candidates.LearningSplit20261027.malformed_counts_uninhabited
#print axioms JurisLean.Candidates.LearningSplit20261027.malformed_counts_uninhabited

#check JurisLean.Candidates.LearningSplit20261027.unbounded_count_join_counterexample
#print axioms JurisLean.Candidates.LearningSplit20261027.unbounded_count_join_counterexample

#check JurisLean.Candidates.LearningSplit20261027.successful_events_subset
#print axioms JurisLean.Candidates.LearningSplit20261027.successful_events_subset

#check JurisLean.Candidates.LearningSplit20261027.successful_events_copy
#print axioms JurisLean.Candidates.LearningSplit20261027.successful_events_copy

#check JurisLean.Candidates.LearningSplit20261027.consistent_labels_copy
#print axioms JurisLean.Candidates.LearningSplit20261027.consistent_labels_copy

#check JurisLean.Candidates.LearningSplit20261027.event_posterior_replay_stable
#print axioms JurisLean.Candidates.LearningSplit20261027.event_posterior_replay_stable

#check JurisLean.Candidates.LearningSplit20261027.conflicting_event_labels_refused
#print axioms JurisLean.Candidates.LearningSplit20261027.conflicting_event_labels_refused

#check JurisLean.Candidates.LearningSplit20261027.accepted_event_posterior_is_existing_beta_readout
#print axioms JurisLean.Candidates.LearningSplit20261027.accepted_event_posterior_is_existing_beta_readout
