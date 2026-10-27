import JurisLean.Candidates.ProcedureClosure20261027

#check JurisLean.Candidates.ProcedureClosure20261027.lawful_closed_iff_local_checks
#print axioms JurisLean.Candidates.ProcedureClosure20261027.lawful_closed_iff_local_checks
#check JurisLean.Candidates.ProcedureClosure20261027.checked_closed_iff_valid_and_exhausted
#print axioms JurisLean.Candidates.ProcedureClosure20261027.checked_closed_iff_valid_and_exhausted
#check JurisLean.Candidates.ProcedureClosure20261027.checked_closure_exhausts_independent_requirements
#print axioms JurisLean.Candidates.ProcedureClosure20261027.checked_closure_exhausts_independent_requirements
#check JurisLean.Candidates.ProcedureClosure20261027.exhaustion_transfers_under_coverage
#print axioms JurisLean.Candidates.ProcedureClosure20261027.exhaustion_transfers_under_coverage
#check JurisLean.Candidates.ProcedureClosure20261027.reverse_exhaustion_needs_no_extra_domain
#print axioms JurisLean.Candidates.ProcedureClosure20261027.reverse_exhaustion_needs_no_extra_domain
#check JurisLean.Candidates.ProcedureClosure20261027.missing_witness_is_an_actual_uncovered_requirement
#print axioms JurisLean.Candidates.ProcedureClosure20261027.missing_witness_is_an_actual_uncovered_requirement
#check JurisLean.Candidates.ProcedureClosure20261027.unfinished_witness_is_an_actual_open_policy_opportunity
#print axioms JurisLean.Candidates.ProcedureClosure20261027.unfinished_witness_is_an_actual_open_policy_opportunity
#check JurisLean.Candidates.ProcedureClosure20261027.final_undetermined_exact
#print axioms JurisLean.Candidates.ProcedureClosure20261027.final_undetermined_exact
#check JurisLean.Candidates.ProcedureClosure20261027.successful_inspection_reads_actual_process_result
#print axioms JurisLean.Candidates.ProcedureClosure20261027.successful_inspection_reads_actual_process_result
#check JurisLean.Candidates.ProcedureClosure20261027.inspected_final_undetermined_retains_coverage
#print axioms JurisLean.Candidates.ProcedureClosure20261027.inspected_final_undetermined_retains_coverage
#check JurisLean.Candidates.ProcedureClosure20261027.branch_inspection_does_not_drop_open_results
#print axioms JurisLean.Candidates.ProcedureClosure20261027.branch_inspection_does_not_drop_open_results
#check JurisLean.Candidates.ProcedureClosure20261027.strict_rank_bounds_finite_transition_count
#print axioms JurisLean.Candidates.ProcedureClosure20261027.strict_rank_bounds_finite_transition_count
#check JurisLean.Candidates.ProcedureClosure20261027.strict_rank_excludes_infinite_execution
#print axioms JurisLean.Candidates.ProcedureClosure20261027.strict_rank_excludes_infinite_execution
#check JurisLean.Candidates.ProcedureClosure20261027.self_loop_has_no_strict_natural_rank
#print axioms JurisLean.Candidates.ProcedureClosure20261027.self_loop_has_no_strict_natural_rank

open JurisLean.Candidates.Final20261021
open JurisLean.Candidates.Final20261021.EvidenceProcedure
open JurisLean.Candidates.ProcedureClosure20261027

namespace JurisLean.Candidates.ProcedureClosure20261027.Audit

def positive : EvidenceItem := ⟨⟨1⟩, 0, .yes, true, true⟩
def negative : EvidenceItem := ⟨⟨2⟩, 0, .yes, true, false⟩
def openInput : ProcessInput := ⟨[1], [1], [], [], [], some ⟨12⟩, [⟨12⟩], false⟩
def closedInput : ProcessInput :=
  ⟨[1], [1], [⟨1, 0, some ⟨11⟩, none, []⟩], [⟨11⟩], [], some ⟨12⟩, [⟨12⟩], false⟩
def badPolicy : ProcessInput := ⟨[], [], [], [], [], some ⟨12⟩, [⟨12⟩], false⟩

theorem vacuous_policy_exhaustion_misses_independent_requirement :
    exhausted badPolicy = true ∧ procedure badPolicy = .closedLawfully ∧
      missingOpportunities [1] badPolicy = [1] ∧
      checkProcess [1] badPolicy = .rejected .scopeMismatch := by decide

theorem required_exhaustion_need_not_exhaust_larger_policy_domain :
    (∀ o ∈ ([1] : List Nat), terminal { closedInput with policyDomain := [1, 2] } o = true) ∧
      exhausted { closedInput with policyDomain := [1, 2] } = false ∧
      procedure { closedInput with policyDomain := [1, 2] } = .open := by decide

theorem four_judgment_process_products_are_distinct :
    proposed_judgment_and_process 0 [positive] openInput = (.supported, .open) ∧
    proposed_judgment_and_process 0 [] closedInput = (.insufficient, .closedLawfully) ∧
    proposed_judgment_and_process 0 [positive, negative] openInput = (.incompatible, .open) ∧
    proposed_judgment_and_process 0 [] { openInput with blocked := true } = (.insufficient, .blocked) := by decide

def futureWithoutNew (_ : Nat) : List EvidenceItem := []
def futureWithNew (time : Nat) : List EvidenceItem := if time = 0 then [] else [positive]

theorem same_current_record_has_different_future_extensions :
    futureWithoutNew 0 = futureWithNew 0 ∧
      judgment 0 (futureWithoutNew 1) = .insufficient ∧
      judgment 0 (futureWithNew 1) = .supported ∧
      finalUndetermined (judgment 0 (futureWithoutNew 0), procedure closedInput) = true := by decide

theorem current_record_does_not_imply_future_impossibility :
    ¬ (∀ future : Nat → List EvidenceItem, future 0 = [] →
      ∀ time, judgment 0 (future time) ≠ .supported) := by
  intro impossible
  exact impossible futureWithNew (by decide) 1 (by decide)

def retryStep (before after : Nat) : Prop := before = after
theorem finite_inspection_does_not_end_retry_execution :
    ∃ path : Nat → Nat, (∀ k, retryStep (path k) (path (k + 1))) ∧
      inspect 1 [1] 0 [] openInput = .known (.insufficient, .open) := by
  exact ⟨fun _ => 0, fun _ => rfl, by decide⟩

/-- info: true -/
#guard_msgs in
#eval decide (inspect 1 [1] 0 [positive] openInput =
  (Result.known (Judgment.supported, Procedure.open) : Result (Judgment × Procedure)))

/-- info: true -/
#guard_msgs in
#eval decide (inspect 1 [1] 0 [] closedInput =
  (Result.known (Judgment.insufficient, Procedure.closedLawfully) : Result (Judgment × Procedure)))

/-- info: true -/
#guard_msgs in
#eval decide (inspect 1 [1] 0 [positive, negative] openInput =
  (Result.known (Judgment.incompatible, Procedure.open) : Result (Judgment × Procedure)))

/-- info: true -/
#guard_msgs in
#eval decide (inspect 1 [1] 0 [] { openInput with blocked := true } =
  (Result.known (Judgment.insufficient, Procedure.blocked) : Result (Judgment × Procedure)))

/-- info: true -/
#guard_msgs in
#eval decide (inspect 0 [1] 0 [] closedInput =
  (Result.unknown Error.checkIncomplete : Result (Judgment × Procedure)))

/-- info: true -/
#guard_msgs in
#eval decide (validPolicy [1] badPolicy = false ∧ checkProcess [1] badPolicy =
  (Result.rejected Error.scopeMismatch : Result Procedure))

/-- info: true -/
#guard_msgs in
#eval decide (missingOpportunities [1] badPolicy = [1] ∧
  unfinishedOpportunities openInput = [1] ∧ unfinishedOpportunities closedInput = [])

/-- info: true -/
#guard_msgs in
#eval decide (procedure { closedInput with validExecutionReceipts := [] } = Procedure.open)

/-- info: true -/
#guard_msgs in
#eval decide (procedure { closedInput with closureAuthority := none } = Procedure.open)

/-- info: true -/
#guard_msgs in
#eval decide (procedure { closedInput with records := closedInput.records ++ closedInput.records } = Procedure.open)

/-- info: true -/
#guard_msgs in
#eval decide (procedure { closedInput with
  records := [⟨1, 0, none, some ⟨13⟩, []⟩], validWaivers := [⟨13⟩] } = Procedure.closedLawfully)

/-- info: true -/
#guard_msgs in
#eval decide (procedure { closedInput with
  records := [⟨1, 0, none, some ⟨13⟩, []⟩], validWaivers := [] } = Procedure.open)

/-- info: true -/
#guard_msgs in
#eval decide (procedure { closedInput with
  records := [⟨1, 0, some ⟨11⟩, none, [2]⟩] } = Procedure.open)

/-- info: true -/
#guard_msgs in
#eval decide (procedure { closedInput with
  required := [1, 2], policyDomain := [1, 2],
  records := [⟨1, 0, some ⟨11⟩, none, [2]⟩, ⟨2, 1, some ⟨11⟩, none, [1]⟩] } = Procedure.open)

/-- info: true -/
#guard_msgs in
#eval decide (finalUndetermined (Judgment.insufficient, Procedure.closedLawfully) = true ∧
  finalUndetermined (Judgment.insufficient, Procedure.blocked) = false ∧
  finalUndetermined (Judgment.supported, Procedure.closedLawfully) = false)

/-- info: true -/
#guard_msgs in
#eval decide (inspectBranches 1 (fun _ => [1]) 0 (fun _ => [])
  (fun branch => if branch = 0 then closedInput else openInput) [0, 1] =
  [(0, Result.known (Judgment.insufficient, Procedure.closedLawfully)),
    (1, Result.known (Judgment.insufficient, Procedure.open))])

end JurisLean.Candidates.ProcedureClosure20261027.Audit

#check JurisLean.Candidates.ProcedureClosure20261027.Audit.vacuous_policy_exhaustion_misses_independent_requirement
#print axioms JurisLean.Candidates.ProcedureClosure20261027.Audit.vacuous_policy_exhaustion_misses_independent_requirement
#check JurisLean.Candidates.ProcedureClosure20261027.Audit.required_exhaustion_need_not_exhaust_larger_policy_domain
#print axioms JurisLean.Candidates.ProcedureClosure20261027.Audit.required_exhaustion_need_not_exhaust_larger_policy_domain
#check JurisLean.Candidates.ProcedureClosure20261027.Audit.four_judgment_process_products_are_distinct
#print axioms JurisLean.Candidates.ProcedureClosure20261027.Audit.four_judgment_process_products_are_distinct
#check JurisLean.Candidates.ProcedureClosure20261027.Audit.same_current_record_has_different_future_extensions
#print axioms JurisLean.Candidates.ProcedureClosure20261027.Audit.same_current_record_has_different_future_extensions
#check JurisLean.Candidates.ProcedureClosure20261027.Audit.current_record_does_not_imply_future_impossibility
#print axioms JurisLean.Candidates.ProcedureClosure20261027.Audit.current_record_does_not_imply_future_impossibility
#check JurisLean.Candidates.ProcedureClosure20261027.Audit.finite_inspection_does_not_end_retry_execution
#print axioms JurisLean.Candidates.ProcedureClosure20261027.Audit.finite_inspection_does_not_end_retry_execution

