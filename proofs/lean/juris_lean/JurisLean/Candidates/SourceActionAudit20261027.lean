import JurisLean.Candidates.SourceAction20261027
import JurisLean.Candidates.SourceOpeningAudit20261027
import JurisLean.Candidates.BusinessFeedbackLoopAudit20261027

#check JurisLean.Candidates.SourceAction20261027.source_request_keeps_actual_key_payload_and_identity
#print axioms JurisLean.Candidates.SourceAction20261027.source_request_keeps_actual_key_payload_and_identity
#check JurisLean.Candidates.SourceAction20261027.applicable_request_requires_actual_environment_and_all_versions
#print axioms JurisLean.Candidates.SourceAction20261027.applicable_request_requires_actual_environment_and_all_versions
#check JurisLean.Candidates.SourceAction20261027.instruction_payloads_are_source_rows_in_call_order
#print axioms JurisLean.Candidates.SourceAction20261027.instruction_payloads_are_source_rows_in_call_order
#check JurisLean.Candidates.SourceAction20261027.bound_plan_preserves_entire_quote_and_source_instructions
#print axioms JurisLean.Candidates.SourceAction20261027.bound_plan_preserves_entire_quote_and_source_instructions
#check JurisLean.Candidates.SourceAction20261027.usable_plan_has_an_actual_source_spec
#print axioms JurisLean.Candidates.SourceAction20261027.usable_plan_has_an_actual_source_spec
#check JurisLean.Candidates.SourceAction20261027.source_run_keeps_inspection_even_on_failure
#print axioms JurisLean.Candidates.SourceAction20261027.source_run_keeps_inspection_even_on_failure
#check JurisLean.Candidates.SourceAction20261027.completed_run_consumes_actual_opening_and_plans
#print axioms JurisLean.Candidates.SourceAction20261027.completed_run_consumes_actual_opening_and_plans
#check JurisLean.Candidates.SourceAction20261027.selected_source_plan_has_actual_spec_and_legal_validation
#print axioms JurisLean.Candidates.SourceAction20261027.selected_source_plan_has_actual_spec_and_legal_validation
#check JurisLean.Candidates.SourceAction20261027.source_episode_and_finite_continuation_preserve_invariants
#print axioms JurisLean.Candidates.SourceAction20261027.source_episode_and_finite_continuation_preserve_invariants

open JurisLean.Candidates.Final20261021
open JurisLean.Candidates.SourceCompilation20261027
open JurisLean.Candidates.SourceStages20261027
open JurisLean.Candidates.IntervalDecisionConsumer20261027
open JurisLean.Candidates.DecisionTrajectoryConsumer20261027
open JurisLean.Candidates.EventFeedbackConsumer20261027
open JurisLean.Candidates.ValidatedFeedbackLoad20261027
open JurisLean.Candidates.AdaptiveRoundLedger20261027
open JurisLean.Candidates.LegalActionDomain20261027
open JurisLean.Candidates.LoadedLegalConsumer20261027
open JurisLean.Candidates.BusinessMeasurement20261027
open JurisLean.Candidates.MeasuredPolicy20261027
open JurisLean.Candidates.BusinessFeedbackLoop20261027
open JurisLean.Candidates.SourceOpening20261027
open JurisLean.Candidates.SourceAction20261027

namespace JurisLean.Candidates.SourceAction20261027.Audit

def gamma : Gamma := LoadedLegalConsumer20261027.Audit.gamma

def payload (key : Nat) : PaymentPayload :=
  ⟨gamma.caseId, gamma.caseRevision, ⟨9⟩, ⟨1⟩, ⟨2⟩, ⟨7, intervalDecisionTag⟩,
    ⟨1⟩, ⟨100 + key⟩, gamma.normVersion, gamma.lawDate⟩

def source : ConsumedView :=
  {SourceOpening20261027.Audit.source with
    relations := [stageQuote ⟨⟨9⟩, ⟨1⟩, ⟨2⟩, ⟨10, intervalDecisionTag⟩, "source debt metadata"]
    ledger := [stageQuote ⟨⟨20, .principal, .contractStip, 2, .supported, 10⟩,
      ⟨9⟩, ⟨1⟩, intervalDecisionTag⟩]
    payments := [stageQuote ⟨⟨10⟩, 20, payload 10⟩, stageQuote ⟨⟨11⟩, 20, payload 11⟩]}

def legalInput : LegalInput (List Nat) :=
  let old := LoadedLegalConsumer20261027.Audit.legalInput
  let other := {old.anchor with gamma := {gamma with interpretation := 2}}
  {old with
    catalog := [⟨old.anchor, 0, source⟩, ⟨other, 0, source⟩]
    history := [trajectoryVersion]}

def calls : List PaymentCall := [⟨.first, ⟨1000⟩, .submit⟩, ⟨.second, ⟨1001⟩, .submit⟩]

-- This is an independent fixture quote declaration. The production binder
-- below must reject it if any source payload changes.
def specs : List PlanSpec := trajectoryQuotes.map fun quote =>
  ⟨{quote with gamma := gamma, execution := [payload 10, payload 11]}, calls⟩

def independentSteps : List Instruction :=
  [.pay ⟨⟨10⟩, ⟨1000⟩, payload 10, .yes, some ⟨10⟩⟩ .submit,
   .pay ⟨⟨11⟩, ⟨1001⟩, payload 11, .yes, some ⟨11⟩⟩ .submit]

def grants : List Authorization.Grant :=
  [trajectoryGrant gamma (payload 10), trajectoryGrant gamma (payload 11)]

def model : ActionModel (List Nat) Ledger.Handle :=
  {checkerVersion := 17
   meanings := specs.map (fun spec => LegalActionDomain20261027.Audit.meaning gamma
     ⟨spec.quote, independentSteps⟩ 2) ++ specs.map (fun spec =>
     LegalActionDomain20261027.Audit.meaning {gamma with interpretation := 2}
       ⟨spec.quote, independentSteps⟩ 5)
   successors := fun _ _ before steps =>
     match (runTrajectory grants before steps).current with
     | some after => [after]
     | none => []
   invariant := fun _ _ after => decide (0 ≤ Ledger.balance after.state)}

def dictionary : MeasurementDictionary :=
  {BusinessFeedbackLoop20261027.Audit.dictionary 0 with
    construct := .timelyPerformance ⟨9⟩ ⟨1⟩ ⟨2⟩ ⟨10, intervalDecisionTag⟩}

def measurement : MeasurementInput 2 :=
  let rows : List MeasurementRow :=
    [⟨dictionary, ⟨110⟩, ⟨1110⟩, ⟨1⟩, ⟨1⟩, ⟨1⟩, .payment ⟨10⟩⟩,
     ⟨dictionary, ⟨111⟩, ⟨1111⟩, ⟨2⟩, ⟨2⟩, ⟨1⟩, .payment ⟨11⟩⟩]
  let treatment := {BusinessFeedbackLoop20261027.Audit.treatment 0 with dictionary := dictionary}
  ⟨dictionary, ⟨20⟩, attestRows rows, closeWindow dictionary rows, rows,
    BusinessFeedbackLoop20261027.Audit.environment, treatment, [treatment]⟩

def settings (state : RoundState 2) : ActionSettings (List Nat) 2 :=
  let p := {LoadedLegalConsumer20261027.Audit.packet state with modelAvailableAt := ⟨30⟩}
  ⟨model, specs, LoadedLegalConsumer20261027.Audit.request state, p, [p], 1/10, 8, id, grants⟩

def fixture (service : Service 2) : Run (List Nat) 2 :=
  let learning := (BusinessFeedbackLoop20261027.Audit.initial service).learning
  run legalInput learning (settings learning) measurement
    BusinessFeedbackLoop20261027.Audit.policy BusinessFeedbackLoop20261027.Audit.feedback

/-- info: true -/
#guard_msgs in
#eval ValidatedFeedbackLoadFixture.check (fun service _ =>
  match (fixture service).outcome with
  | .known out => match out.episode.action.run, out.episode.continuation.observation with
    | some action, .known row => match action.decision, action.execution.proposal with
      | .known selected, some plan => decide (
          out.initial.business.current = some out.opening.handle ∧ out.opening.handle.state.paid = 0 ∧
          out.opening.anchor.frame.stages.afterSecond.state.paid = 14 ∧ plan.steps = independentSteps ∧
          selected.nominal.action.id = 2 ∧ selected.probability.fitted.table = [0, 0] ∧
          row.measured.actualPost.state.paid = 14 ∧ row.measured.actualPost.state.allocated = 10 ∧
          row.measured.actualPost.state.surplus = 4 ∧ row.measured.measuredTotal = 10 ∧
          row.measured.label = true ∧ row.measured.actualPost.state.receipts.length = 2 ∧
          out.episode.continuation.post.learning.pending.isSome ∧
          (lookup out.episode.continuation.post.learning.service.journal ⟨100⟩).map (fun c => c.state) =
            some (.active 1 true))
      | _, _ => false
    | _, _ => false
  | _ => false)

-- The next action reads the actual assessment output and replays the same
-- source business keys, so changing the fitted decision does not pay twice.
/-- info: true -/
#guard_msgs in
#eval ValidatedFeedbackLoadFixture.check (fun service evaluation =>
  match (fixture service).outcome with
  | .known out =>
      let assessed := BusinessFeedbackLoop20261027.Audit.assessed out.episode.continuation.post evaluation
      let nextSettings := {settings assessed.learning with request :=
        {LoadedLegalConsumer20261027.Audit.request assessed.learning with riskLimit := 2/5}}
      let next := act assessed (actionInput legalInput nextSettings out.plans)
      match next.run, next.post.business.current with
      | some actual, some post => match actual.decision with
        | .known selected => decide (selected.probability.fitted.table = [0, 1] ∧
            selected.nominal.action.id = 1 ∧ post.state.paid = 14 ∧ post.state.receipts.length = 2 ∧
            next.post.business = actual.execution.payment ∧ roundSpent assessed.learning = 1/10)
        | _ => false
      | _, _ => false
  | _ => false)

/-- info: true -/
#guard_msgs in
#eval match openingFor legalInput with
  | .known opening => decide (instructions opening calls = independentSteps ∧
      (paymentRequest opening ⟨.first, ⟨9999⟩, .submit⟩).key = (⟨10⟩ : PaymentId) ∧
      (paymentRequest opening ⟨.first, ⟨9999⟩, .submit⟩).payload = payload 10)
  | _ => false

/-- info: true -/
#guard_msgs in
#eval match openingFor legalInput, specs with
  | .known opening, spec :: _ =>
      decide (bindPlan opening {spec with quote := {spec.quote with execution := []}} =
        Result.rejected Error.scopeMismatch)
  | _, _ => false

/-- info: true -/
#guard_msgs in
#eval match openingFor legalInput, specs with
  | .known opening, spec :: _ =>
      decide (bindPlan opening {spec with quote := {spec.quote with gamma := {gamma with caseRevision := 99}}} =
        Result.rejected Error.scopeMismatch)
  | _, _ => false

/-- info: true -/
#guard_msgs in
#eval match openingFor legalInput, specs with
  | .known opening, spec :: _ => match bindPlan opening spec with
    | .known plan => decide (plan.quote = spec.quote ∧ plan.steps = independentSteps ∧
        plan.quote.success = spec.quote.success ∧ plan.quote.cost = spec.quote.cost)
    | _ => false
  | _, _ => false

/-- info: true -/
#guard_msgs in
#eval ValidatedFeedbackLoadFixture.check (fun service _ =>
  let learning := (BusinessFeedbackLoop20261027.Audit.initial service).learning
  let changed := {settings learning with plans := specs.map fun spec =>
    {spec with quote := {spec.quote with execution := []}}}
  match (run legalInput learning changed measurement BusinessFeedbackLoop20261027.Audit.policy
      BusinessFeedbackLoop20261027.Audit.feedback).outcome with
  | .known out => match out.episode.action.run, out.episode.continuation.post.business.current with
    | some actual, some post => decide (out.plans.length = 2 ∧ usablePlans out.plans = [] ∧
        actual.execution.proposal = none ∧ post.state.paid = 0 ∧
        out.episode.continuation.post.learning = learning)
    | _, _ => false
  | _ => false)

/-- info: true -/
#guard_msgs in
#eval ValidatedFeedbackLoadFixture.check (fun service _ =>
  let learning := (BusinessFeedbackLoop20261027.Audit.initial service).learning
  let missing := {legalInput with catalog := []}
  let result := run missing learning (settings learning) measurement
    BusinessFeedbackLoop20261027.Audit.policy BusinessFeedbackLoop20261027.Audit.feedback
  match result.inspection, result.outcome with
  | .known reports, .unknown .missingEvidence => decide (reports.map Prod.fst = [0, 1])
  | _, _ => false)

/-- info: true -/
#guard_msgs in
#eval ValidatedFeedbackLoadFixture.check (fun service _ =>
  let learning := (BusinessFeedbackLoop20261027.Audit.initial service).learning
  let changed := {learning with service := {learning.service with gamma := {gamma with caseId := ⟨99⟩}}}
  match (run legalInput changed (settings changed) measurement BusinessFeedbackLoop20261027.Audit.policy
      BusinessFeedbackLoop20261027.Audit.feedback).outcome with
  | .unknown .scopeMismatch => true
  | _ => false)

/-- info: true -/
#guard_msgs in
#eval ValidatedFeedbackLoadFixture.check (fun service _ =>
  let learning := (BusinessFeedbackLoop20261027.Audit.initial service).learning
  let input := {settings learning with grants := []}
  match (run legalInput learning input measurement BusinessFeedbackLoop20261027.Audit.policy
      BusinessFeedbackLoop20261027.Audit.feedback).outcome with
  | .known out => match out.episode.action.run, out.episode.continuation.post.business.current with
    | some actual, some post => decide (actual.execution.proposal.isSome ∧ post.state.paid = 0 ∧
        actual.execution.payment.exit = Pipeline.Exit.rejected ∧
        actual.execution.payment.obligations = [Error.authorityUnresolved])
    | _, _ => false
  | _ => false)

/-- info: true -/
#guard_msgs in
#eval ValidatedFeedbackLoadFixture.check (fun service _ =>
  let learning := (BusinessFeedbackLoop20261027.Audit.initial service).learning
  let input := {settings learning with model := {model with meanings := []}}
  match (run legalInput learning input measurement BusinessFeedbackLoop20261027.Audit.policy
      BusinessFeedbackLoop20261027.Audit.feedback).outcome with
  | .known out => match out.episode.action.run with
    | some actual => decide (actual.review.allowed = [] ∧ actual.execution.proposal = none)
    | none => false
  | _ => false)

/-- info: true -/
#guard_msgs in
#eval match openingFor {legalInput with history := []} with
  | .known opening => decide ((paymentRequest opening ⟨.first, ⟨1000⟩, .submit⟩).applicable = Applicable.unknown)
  | _ => false

-- An unresolved legal version also stays unresolved in source-built requests.
/-- info: true -/
#guard_msgs in
#eval match openingFor {legalInput with app := fun _ _ _ => .unknown} with
  | .known opening => decide ((paymentRequest opening ⟨.first, ⟨1000⟩, .submit⟩).applicable = Applicable.unknown)
  | _ => false

/-- info: true -/
#guard_msgs in
#eval
  let changed := {source with payments := source.payments.map fun p =>
    {p with value := {p.value with payload := {p.value.payload with amount := ⟨8, intervalDecisionTag⟩}}}}
  let input := {legalInput with catalog := legalInput.catalog.map fun row => {row with decoded := changed}}
  match openingFor input, specs with
  | .known opening, spec :: _ => decide (bindPlan opening spec = Result.rejected Error.scopeMismatch ∧
      (paymentRequest opening ⟨.first, ⟨1000⟩, .submit⟩).payload.amount.value = 8)
  | _, _ => false

-- A source-bound unknown submission retains its stable key and attempt; no
-- old handle is published as a certain post and no tail payment is executed.
/-- info: true -/
#guard_msgs in
#eval match openingFor legalInput with
  | .known opening =>
      let uncertain : List PaymentCall := [⟨.first, ⟨1000⟩, .submit⟩, ⟨.second, ⟨1001⟩, .unknownCommit⟩]
      let actual := runTrajectory grants opening.handle (instructions opening uncertain)
      decide (actual.current = none ∧ actual.outcomes.length = 2 ∧
        actual.outcomes[1]? = some (Ledger.Outcome.unknownCommit ⟨11⟩ ⟨1001⟩))
  | _ => false

end JurisLean.Candidates.SourceAction20261027.Audit
