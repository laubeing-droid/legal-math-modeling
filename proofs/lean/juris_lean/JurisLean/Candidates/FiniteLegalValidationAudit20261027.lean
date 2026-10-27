import JurisLean.Candidates.FiniteLegalValidation20261027

#check JurisLean.Candidates.FiniteLegalValidation20261027.fired_conclusions_are_enabled_rules
#print axioms JurisLean.Candidates.FiniteLegalValidation20261027.fired_conclusions_are_enabled_rules
#check JurisLean.Candidates.FiniteLegalValidation20261027.advance_is_recorded_round
#print axioms JurisLean.Candidates.FiniteLegalValidation20261027.advance_is_recorded_round
#check JurisLean.Candidates.FiniteLegalValidation20261027.generated_trace_has_actual_rule_premises
#print axioms JurisLean.Candidates.FiniteLegalValidation20261027.generated_trace_has_actual_rule_premises
#check JurisLean.Candidates.FiniteLegalValidation20261027.replay_generated_trace_is_exact_closure
#print axioms JurisLean.Candidates.FiniteLegalValidation20261027.replay_generated_trace_is_exact_closure
#check JurisLean.Candidates.FiniteLegalValidation20261027.trace_has_exact_number_of_rounds
#print axioms JurisLean.Candidates.FiniteLegalValidation20261027.trace_has_exact_number_of_rounds
#check JurisLean.Candidates.FiniteLegalValidation20261027.enabled_count_bounded_by_rule_count
#print axioms JurisLean.Candidates.FiniteLegalValidation20261027.enabled_count_bounded_by_rule_count
#check JurisLean.Candidates.FiniteLegalValidation20261027.closure_list_size_bound
#print axioms JurisLean.Candidates.FiniteLegalValidation20261027.closure_list_size_bound
#check JurisLean.Candidates.FiniteLegalValidation20261027.full_horn_consumes_every_source_fact
#print axioms JurisLean.Candidates.FiniteLegalValidation20261027.full_horn_consumes_every_source_fact
#check JurisLean.Candidates.FiniteLegalValidation20261027.full_horn_trace_is_checked
#print axioms JurisLean.Candidates.FiniteLegalValidation20261027.full_horn_trace_is_checked

open JurisLean.Candidates.Final20261021.Compiler
open JurisLean.Candidates.FiniteLegalValidation20261027

/-- info: true -/
#guard_msgs in
#eval decide (replayTrace [1] (traceRounds [⟨[1], 2⟩, ⟨[2], 3⟩] 3 [1]) =
  proposed_rule_input [⟨[1], 2⟩, ⟨[2], 3⟩] 3 [1])

/-- info: true -/
#guard_msgs in
#eval decide (traceRounds [⟨[1], 2⟩, ⟨[2], 3⟩] 2 [1] =
  [[⟨[1], 2⟩], [⟨[1], 2⟩, ⟨[2], 3⟩]])

/-- info: true -/
#guard_msgs in
#eval decide (traceRounds [⟨[2], 1⟩, ⟨[1], 2⟩] 2 [] = [[], []])

/-- info: true -/
#guard_msgs in
#eval decide (replayTrace [1, 4] (traceRounds [⟨[4], 5⟩] 3 [1, 4]) = [1, 4, 5, 5, 5])

/-- info: true -/
#guard_msgs in
#eval decide (traceRounds ([] : List (Rule Nat)) 0 [] = [])
