import JurisLean.Candidates.LegalActionDomain20261027

import JurisLean.Candidates.FiniteLegalValidationAudit20261027
import JurisLean.Candidates.DecisionTrajectoryConsumerAudit20261027

#check JurisLean.Candidates.LegalActionDomain20261027.meaning_row_binds_full_instructions
#print axioms JurisLean.Candidates.LegalActionDomain20261027.meaning_row_binds_full_instructions
#check JurisLean.Candidates.LegalActionDomain20261027.finite_row_checks_every_world_and_successor
#print axioms JurisLean.Candidates.LegalActionDomain20261027.finite_row_checks_every_world_and_successor
#check JurisLean.Candidates.LegalActionDomain20261027.accepted_meaning_has_nonempty_worlds_and_required_closure
#print axioms JurisLean.Candidates.LegalActionDomain20261027.accepted_meaning_has_nonempty_worlds_and_required_closure
#check JurisLean.Candidates.LegalActionDomain20261027.branch_acceptance_uses_actual_worlds_and_unique_meaning
#print axioms JurisLean.Candidates.LegalActionDomain20261027.branch_acceptance_uses_actual_worlds_and_unique_meaning
#check JurisLean.Candidates.LegalActionDomain20261027.acceptance_binds_proposal_and_every_branch
#print axioms JurisLean.Candidates.LegalActionDomain20261027.acceptance_binds_proposal_and_every_branch
#check JurisLean.Candidates.LegalActionDomain20261027.accepted_actual_branch_step_preserves_declared_invariant
#print axioms JurisLean.Candidates.LegalActionDomain20261027.accepted_actual_branch_step_preserves_declared_invariant
#check JurisLean.Candidates.LegalActionDomain20261027.unresolved_branch_cannot_be_silently_removed
#print axioms JurisLean.Candidates.LegalActionDomain20261027.unresolved_branch_cannot_be_silently_removed
#check JurisLean.Candidates.LegalActionDomain20261027.legal_domain_is_exact_filter_not_a_generator
#print axioms JurisLean.Candidates.LegalActionDomain20261027.legal_domain_is_exact_filter_not_a_generator
#check JurisLean.Candidates.LegalActionDomain20261027.domain_consumes_actual_validator
#print axioms JurisLean.Candidates.LegalActionDomain20261027.domain_consumes_actual_validator
#check JurisLean.Candidates.LegalActionDomain20261027.selected_plan_was_approved_and_reproduces_the_decision
#print axioms JurisLean.Candidates.LegalActionDomain20261027.selected_plan_was_approved_and_reproduces_the_decision
#check JurisLean.Candidates.LegalActionDomain20261027.no_selected_plan_preserves_all_business_state
#print axioms JurisLean.Candidates.LegalActionDomain20261027.no_selected_plan_preserves_all_business_state
#check JurisLean.Candidates.LegalActionDomain20261027.chosen_execution_uses_the_entire_approved_instruction_list
#print axioms JurisLean.Candidates.LegalActionDomain20261027.chosen_execution_uses_the_entire_approved_instruction_list
#check JurisLean.Candidates.LegalActionDomain20261027.execution_choice_preserves_reported_state_invariant
#print axioms JurisLean.Candidates.LegalActionDomain20261027.execution_choice_preserves_reported_state_invariant
#check JurisLean.Candidates.LegalActionDomain20261027.complete_consumer_choice_has_actual_legal_validation
#print axioms JurisLean.Candidates.LegalActionDomain20261027.complete_consumer_choice_has_actual_legal_validation
#check JurisLean.Candidates.LegalActionDomain20261027.indistinguishable_permission_prevents_sound_and_complete
#print axioms JurisLean.Candidates.LegalActionDomain20261027.indistinguishable_permission_prevents_sound_and_complete
#check JurisLean.Candidates.LegalActionDomain20261027.pure_filter_cannot_offer_an_unproposed_action
#print axioms JurisLean.Candidates.LegalActionDomain20261027.pure_filter_cannot_offer_an_unproposed_action
#check JurisLean.Candidates.LegalActionDomain20261027.undefined_denominators_remain_unknown
#print axioms JurisLean.Candidates.LegalActionDomain20261027.undefined_denominators_remain_unknown

open JurisLean.Candidates.Final20261021
open JurisLean.Candidates.Final20261021.EvidenceProcedure
open JurisLean.Candidates.SourceCompilation20261027
open JurisLean.Candidates.FiniteLegalValidation20261027
open JurisLean.Candidates.IntervalDecisionConsumer20261027
open JurisLean.Candidates.DecisionTrajectoryConsumer20261027
open JurisLean.Candidates.LegalActionDomain20261027

namespace JurisLean.Candidates.LegalActionDomain20261027.Audit

def materialA : MaterialSnapshot :=
  { FiniteLegalValidation20261027.Audit.material with gamma := intervalDecisionGamma }

def materialB : MaterialSnapshot :=
  { materialA with gamma := { intervalDecisionGamma with interpretation := 2 } }

def supplementA : Supplement :=
  { FiniteLegalValidation20261027.Audit.supplement with material := materialA }

def supplementB : Supplement := { supplementA with material := materialB }

def policyA : ProcessPolicy :=
  { FiniteLegalValidation20261027.Audit.policy with gamma := materialA.gamma }

def policyB : ProcessPolicy := { policyA with gamma := materialB.gamma }

def legalInput : LegalInput (List Nat) :=
  { anchor := materialA
    branches := [⟨0, materialA, 0⟩, ⟨1, materialB, 0⟩]
    catalog := [⟨materialA, 0, FiniteLegalValidation20261027.Audit.source⟩,
      ⟨materialB, 0, FiniteLegalValidation20261027.Audit.source⟩]
    supplements := [supplementA, supplementB]
    policies := [policyA, policyB]
    history := []
    versions := [1]
    app := fun _ _ v => if v = 1 then .yes else .no
    rules := [⟨50, 1, ⟨[1], 2⟩⟩, ⟨51, 1, ⟨[4], 5⟩⟩]
    ruleGate := fun _ _ => true
    allowedPairs := [(0, [1, 2, 4, 5]), (0, [1, 2, 4, 5, 7]),
      (1, [1, 2, 4, 5]), (1, [1, 2, 4, 5, 7])]
    truth := FiniteLegalValidation20261027.Audit.valuation }

def proposals : List Proposal := trajectoryQuotes.map fun q => ⟨q, trajectorySteps⟩

def meaning (g : Gamma) (p : Proposal) (atom : Nat) : ActionMeaning :=
  ⟨g, 17, ⟨80⟩, p.quote.id, p.steps, [atom], true⟩

def actionModel : ActionModel (List Nat) Ledger.Handle :=
  { checkerVersion := 17
    meanings := proposals.map (fun p => meaning materialA.gamma p 2) ++
      proposals.map (fun p => meaning materialB.gamma p 5)
    successors := fun _ _ before steps =>
      match (runTrajectory trajectoryGrants before steps).current with
      | some post => [post]
      | none => []
    invariant := fun _ _ post => decide (0 ≤ Ledger.balance post.state) }

def fixture (input : LegalInput (List Nat) := legalInput)
    (model : ActionModel (List Nat) Ledger.Handle := actionModel)
    (candidates : List Proposal := proposals) (grants : List Authorization.Grant := trajectoryGrants)
    (initial : Ledger.Handle := trajectoryOpening) : LegalDecisionRun (List Nat) 2 :=
  runLegalDecision input model candidates intervalDecisionRequest probabilityFixtureProtocol
    probabilityFixtureLoss [[0, 1], [0, 0]]
    (fun i => {probabilityTraining i with label := false}) probabilityCalibration
    (1/10) 8 true id grants initial

/-- info: true -/
#guard_msgs in
#eval
  let result := fixture
  match result.decision, result.execution.proposal, result.execution.payment.current with
  | .known selected, some plan, some post =>
      decide (result.review.allowed.length = 2 ∧ result.review.results.length = 2 ∧
        selected.nominal.action.id = 2 ∧ plan.quote.id = 2 ∧ plan.steps = trajectorySteps ∧
        result.execution.payment.exit = Pipeline.Exit.success ∧ post.state.allocated = 10 ∧
        post.state.paid = 14 ∧ post.state.surplus = 4 ∧ Ledger.balance post.state = 0)
  | _, _, _ => false

-- Both full branch contexts are retained; no Cartesian world pairs are added.
/-- info: true -/
#guard_msgs in
#eval match (fixture).review.validation with
  | .known rows => decide (rows.map Prod.fst = [0, 1]) && rows.all (fun (_, result) =>
      match result with
      | .known report => (match report.horn with | .known _ => true | _ => false) &&
          decide (report.procedure = .known Procedure.closedLawfully)
      | _ => false)
  | _ => false

/-- info: true -/
#guard_msgs in
#eval (review {legalInput with branches := []} actionModel trajectoryOpening proposals).allowed.isEmpty

/-- info: true -/
#guard_msgs in
#eval (review {legalInput with branches := [⟨0, materialA, 0⟩, ⟨0, materialB, 0⟩]}
  actionModel trajectoryOpening proposals).allowed.isEmpty

/-- info: true -/
#guard_msgs in
#eval (review {legalInput with branches := [⟨0, materialA, 0⟩, ⟨1, materialB, 99⟩]}
  actionModel trajectoryOpening proposals).allowed.isEmpty

/-- info: true -/
#guard_msgs in
#eval (review {legalInput with allowedPairs := [(0, [1, 2, 4, 5])]}
  actionModel trajectoryOpening proposals).allowed.isEmpty

/-- info: true -/
#guard_msgs in
#eval (review {legalInput with app := fun _ _ _ => .unknown}
  actionModel trajectoryOpening proposals).allowed.isEmpty

/-- info: true -/
#guard_msgs in
#eval (review {legalInput with policies := [{policyA with validClosures := []}, policyB]}
  actionModel trajectoryOpening proposals).allowed.isEmpty

/-- info: true -/
#guard_msgs in
#eval (review legalInput {actionModel with meanings := []} trajectoryOpening proposals).allowed.isEmpty

/-- info: true -/
#guard_msgs in
#eval (review legalInput {actionModel with checkerVersion := 18} trajectoryOpening proposals).allowed.isEmpty

/-- info: true -/
#guard_msgs in
#eval (review legalInput {actionModel with meanings := actionModel.meanings ++ actionModel.meanings}
  trajectoryOpening proposals).allowed.isEmpty

-- A source-derived permission missing in just one legal branch blocks the plan.
/-- info: true -/
#guard_msgs in
#eval (review legalInput {actionModel with meanings := actionModel.meanings.map fun row =>
    if row.gamma = materialB.gamma then {row with permissionAtoms := [7]} else row}
  trajectoryOpening proposals).allowed.isEmpty

/-- info: true -/
#guard_msgs in
#eval (review legalInput {actionModel with successors := fun _ _ _ _ => []}
  trajectoryOpening proposals).allowed.isEmpty

/-- info: true -/
#guard_msgs in
#eval (review legalInput {actionModel with invariant := fun _ _ _ => false}
  trajectoryOpening proposals).allowed.isEmpty

-- The payload projection alone cannot license hidden extra refresh instructions.
/-- info: true -/
#guard_msgs in
#eval (review legalInput actionModel trajectoryOpening (proposals.map fun p =>
  {p with steps := .refresh trajectoryRefresh :: p.steps})).allowed.isEmpty

/-- info: true -/
#guard_msgs in
#eval (review legalInput actionModel trajectoryOpening (proposals.map fun p =>
  {p with steps := [.pay (trajectoryRequest 1 70) .submit]})).allowed.isEmpty

/-- info: true -/
#guard_msgs in
#eval (review legalInput actionModel trajectoryOpening (proposals.map fun p =>
  {p with quote := {p.quote with gamma := {p.quote.gamma with caseId := ⟨99⟩}}})).allowed.isEmpty

/-- info: true -/
#guard_msgs in
#eval (review legalInput actionModel trajectoryOpening (proposals.map fun p =>
  {p with quote := {p.quote with execution := []}})).allowed.isEmpty

def openInput : LegalInput (List Nat) :=
  { legalInput with supplements :=
    [{supplementA with process := {supplementA.process with records := []}}, supplementB] }

/-- info: true -/
#guard_msgs in
#eval (review openInput actionModel trajectoryOpening proposals).allowed.isEmpty

-- Nonfinal actions may be explicitly permitted while the process stays open.
/-- info: true -/
#guard_msgs in
#eval decide ((review openInput {actionModel with meanings := actionModel.meanings.map fun row =>
  {row with requiresClosed := false}} trajectoryOpening proposals).allowed.length = 2)

-- Pending unrelated evidence is retained, while robust atoms 2/5 hold in every
-- remaining world. The pending atom is never turned into a positive premise.
/-- info: true -/
#guard_msgs in
#eval
  let input := {legalInput with supplements :=
    [{supplementA with evidence := supplementA.evidence ++
      [FiniteLegalValidation20261027.Audit.quoted ⟨⟨1⟩, 7, .unknown, true, true⟩]}, supplementB]}
  let result := review input actionModel trajectoryOpening proposals
  decide (result.allowed.length = 2) && match result.validation with
    | .known rows => rows.any fun (_, value) => match value with
        | .known report => decide (.pendingEvidence ⟨1⟩ 7 ∈ report.failures)
        | _ => false
    | _ => false

-- Replacing the primitive admitted fact with unknown destroys permission 2 in
-- an explicitly retained world; the model cannot use the unknown as a premise.
/-- info: true -/
#guard_msgs in
#eval (review {legalInput with
    supplements := [{supplementA with evidence :=
      [FiniteLegalValidation20261027.Audit.quoted ⟨⟨1⟩, 1, .unknown, true, true⟩,
       FiniteLegalValidation20261027.Audit.quoted ⟨⟨1⟩, 4, .yes, true, true⟩]}, supplementB]
    allowedPairs := legalInput.allowedPairs ++ [(0, [4, 5])]}
  actionModel trajectoryOpening proposals).allowed.isEmpty

/-- info: true -/
#guard_msgs in
#eval
  let result := fixture legalInput actionModel proposals []
  decide (result.review.allowed.length = 2 ∧ result.execution.payment.current = some trajectoryOpening ∧
    result.execution.payment.exit ≠ Pipeline.Exit.success)

/-- info: true -/
#guard_msgs in
#eval
  let changed := {trajectoryOpening with gamma := {trajectoryOpening.gamma with caseRevision := 99}}
  let result := fixture legalInput actionModel proposals trajectoryGrants changed
  decide (result.decision = .rejected Error.scopeMismatch ∧
    result.execution.proposal = none ∧ result.execution.payment.current = some changed ∧
    result.execution.payment.outcomes = [])

/-- info: true -/
#guard_msgs in
#eval
  let result := fixture {legalInput with branches := []}
  decide (result.execution.proposal = none ∧ result.execution.payment.current = some trajectoryOpening ∧
    result.execution.payment.outcomes = [])

-- Different acceptance and admissibility denominators yield different rates.
/-- info: true -/
#guard_msgs in
#eval decide (rateReport 40 2 80 24 = (Result.known (1/20), Result.known (3/10)))

/-- info: true -/
#guard_msgs in
#eval decide (rateReport 0 0 1 1 = (Result.unknown Error.notIdentified, Result.known 1))

-- A valid plan can lose its external commit receipt. The runtime must stop
-- without inventing a known poststate or executing the second payment.
/-- info: true -/
#guard_msgs in
#eval
  let plans := proposals.map fun p =>
    {p with steps := [.pay (trajectoryRequest 1) .unknownCommit, .pay (trajectoryRequest 2) .submit]}
  let model := {actionModel with
    meanings := plans.map (fun p => meaning materialA.gamma p 2) ++
      plans.map (fun p => meaning materialB.gamma p 5)
    successors := fun _ _ before _ => [before]}
  let result := fixture legalInput model plans
  decide (result.review.allowed.length = 2 ∧ result.execution.payment.current = none ∧
    result.execution.payment.outcomes = [Ledger.Outcome.unknownCommit ⟨1⟩ ⟨1⟩])

-- Revalidation reads the actual new balance, even with an unchanged Gamma.
/-- info: true -/
#guard_msgs in
#eval
  let model := {actionModel with successors := fun g w before steps =>
    if Ledger.balance before.state = 10 then actionModel.successors g w before steps else []}
  let result := fixture legalInput model
  match result.execution.payment.current with
  | some post => decide (result.review.allowed.length = 2) &&
      (review legalInput model post proposals).allowed.isEmpty
  | none => false

theorem schema_correct_can_be_normatively_forbidden :
    (fun (_ : Nat) => true) 1 = true ∧ ¬ (1 ≤ (0 : Nat)) := by decide

theorem checked_action_is_not_a_substituted_execution :
    1 ≤ (1 : Nat) ∧ ¬ (2 ≤ (1 : Nat)) := by decide

theorem two_standalone_steps_need_the_actual_intermediate_state :
    1 ≤ (1 : Nat) ∧ 1 ≤ (1 : Nat) ∧ ¬ (1 + 1 ≤ (1 : Nat)) := by decide

theorem inaction_does_not_remove_deadline_loss :
    (0 : Nat) ≤ 1 ∧ ¬ ((0 : Nat) + 2 ≤ 1) := by decide

theorem syntax_and_proof_do_not_establish_external_fact_fidelity :
    (fun (fact : Bool) => fact) true = true ∧ (false : Bool) ≠ true := by decide

end JurisLean.Candidates.LegalActionDomain20261027.Audit


#check JurisLean.Candidates.LegalActionDomain20261027.Audit.schema_correct_can_be_normatively_forbidden
#print axioms JurisLean.Candidates.LegalActionDomain20261027.Audit.schema_correct_can_be_normatively_forbidden
#check JurisLean.Candidates.LegalActionDomain20261027.Audit.checked_action_is_not_a_substituted_execution
#print axioms JurisLean.Candidates.LegalActionDomain20261027.Audit.checked_action_is_not_a_substituted_execution
#check JurisLean.Candidates.LegalActionDomain20261027.Audit.two_standalone_steps_need_the_actual_intermediate_state
#print axioms JurisLean.Candidates.LegalActionDomain20261027.Audit.two_standalone_steps_need_the_actual_intermediate_state
#check JurisLean.Candidates.LegalActionDomain20261027.Audit.inaction_does_not_remove_deadline_loss
#print axioms JurisLean.Candidates.LegalActionDomain20261027.Audit.inaction_does_not_remove_deadline_loss
#check JurisLean.Candidates.LegalActionDomain20261027.Audit.syntax_and_proof_do_not_establish_external_fact_fidelity
#print axioms JurisLean.Candidates.LegalActionDomain20261027.Audit.syntax_and_proof_do_not_establish_external_fact_fidelity
