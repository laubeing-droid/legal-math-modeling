import JurisLean.Candidates.DecisionTrajectoryConsumer20261027
import JurisLean.Candidates.IntervalDecisionConsumerAudit20261027

#check JurisLean.Candidates.DecisionTrajectoryConsumer20261027.committed_head_feeds_actual_tail
#print axioms JurisLean.Candidates.DecisionTrajectoryConsumer20261027.committed_head_feeds_actual_tail
#check JurisLean.Candidates.DecisionTrajectoryConsumer20261027.replay_continues_from_current_state
#print axioms JurisLean.Candidates.DecisionTrajectoryConsumer20261027.replay_continues_from_current_state
#check JurisLean.Candidates.DecisionTrajectoryConsumer20261027.unknown_commit_stops_the_tail
#print axioms JurisLean.Candidates.DecisionTrajectoryConsumer20261027.unknown_commit_stops_the_tail
#check JurisLean.Candidates.DecisionTrajectoryConsumer20261027.authorized_refresh_feeds_actual_tail
#print axioms JurisLean.Candidates.DecisionTrajectoryConsumer20261027.authorized_refresh_feeds_actual_tail
#check JurisLean.Candidates.DecisionTrajectoryConsumer20261027.every_reported_post_has_an_actual_path
#print axioms JurisLean.Candidates.DecisionTrajectoryConsumer20261027.every_reported_post_has_an_actual_path
#check JurisLean.Candidates.DecisionTrajectoryConsumer20261027.finite_interpreter_preserves_full_invariant
#print axioms JurisLean.Candidates.DecisionTrajectoryConsumer20261027.finite_interpreter_preserves_full_invariant
#check JurisLean.Candidates.DecisionTrajectoryConsumer20261027.selection_reads_actual_sample_and_quote
#print axioms JurisLean.Candidates.DecisionTrajectoryConsumer20261027.selection_reads_actual_sample_and_quote
#check JurisLean.Candidates.DecisionTrajectoryConsumer20261027.substituted_execution_is_refused
#print axioms JurisLean.Candidates.DecisionTrajectoryConsumer20261027.substituted_execution_is_refused
#check JurisLean.Candidates.DecisionTrajectoryConsumer20261027.selected_execution_preserves_full_invariant
#print axioms JurisLean.Candidates.DecisionTrajectoryConsumer20261027.selected_execution_preserves_full_invariant
#check JurisLean.Candidates.DecisionTrajectoryConsumer20261027.complete_consumer_uses_the_chosen_execution
#print axioms JurisLean.Candidates.DecisionTrajectoryConsumer20261027.complete_consumer_uses_the_chosen_execution
#check JurisLean.Candidates.DecisionTrajectoryConsumer20261027.successful_execution_is_the_selected_plan
#print axioms JurisLean.Candidates.DecisionTrajectoryConsumer20261027.successful_execution_is_the_selected_plan
#check JurisLean.Candidates.DecisionTrajectoryConsumer20261027.sampled_consumer_preserves_known_state
#print axioms JurisLean.Candidates.DecisionTrajectoryConsumer20261027.sampled_consumer_preserves_known_state

open JurisLean.Candidates.Final20261021
open JurisLean.Candidates.Final20261021.Decision
open JurisLean.Candidates.IntervalDecisionConsumer20261027
open JurisLean.Candidates.DecisionTrajectoryConsumer20261027

def trajectoryDebt : DebtRecord :=
  ⟨⟨1⟩, ⟨1⟩, ⟨2⟩, ⟨10, intervalDecisionTag⟩, "synthetic debt"⟩

def trajectoryPayload (key : ℕ) (amount : ℚ := 7) : PaymentPayload :=
  ⟨intervalDecisionGamma.caseId, 0, trajectoryDebt.relation, trajectoryDebt.obligor,
    trajectoryDebt.creditor, ⟨amount, intervalDecisionTag⟩, ⟨key⟩, ⟨key⟩, 1, ⟨0⟩⟩

def trajectoryRequest (key : ℕ) (amount : ℚ := 7) : PaymentRequest :=
  ⟨⟨key⟩, ⟨key⟩, trajectoryPayload key amount, .yes, some ⟨key⟩⟩

def trajectoryVersion : Temporal.VersionRecord :=
  ⟨⟨80⟩, 1, intervalDecisionGamma.jurisdiction, 1, ⟨0⟩, some ⟨1⟩, ⟨0⟩, ⟨0⟩⟩

def trajectoryOpening : Ledger.Handle :=
  let initial := Trace.initial intervalDecisionGamma trajectoryDebt
  { initial with state := { initial.state with
      normHistory := [trajectoryVersion]
      env := Temporal.proposed_applicability intervalDecisionGamma [trajectoryVersion] } }

def trajectoryGrant (g : Gamma) (p : PaymentPayload) : Authorization.Grant :=
  { evidence := ⟨90⟩, subject := p.payer, caseId := g.caseId, context := g
    object := .relation p.relation, action := 0, contentVersion := p.normVersion
    payload := some p, nextContext := none, authorityRuleVersion := g.normVersion
    fromDate := ⟨0⟩, untilDate := ⟨100⟩ }

def trajectoryGrants : List Authorization.Grant :=
  [trajectoryGrant intervalDecisionGamma (trajectoryPayload 1),
    trajectoryGrant intervalDecisionGamma (trajectoryPayload 2),
    trajectoryGrant intervalDecisionGamma (trajectoryPayload 3 0)]

def trajectorySteps : List Instruction :=
  [.pay (trajectoryRequest 1) .submit, .pay (trajectoryRequest 2) .submit]

-- Both quotes declare exactly the same execution sequence. Their identified
-- gross outcome values include the separately declared once-only cost of 14.
def trajectoryQuotes : List BinaryQuote :=
  [{riskyQuote with
      success := ledgerAmount ⟨25, intervalDecisionTag⟩
      failure := ledgerAmount ⟨13, intervalDecisionTag⟩
      cost := ⟨14, intervalDecisionTag⟩
      execution := [trajectoryPayload 1, trajectoryPayload 2]},
    {settlementQuote with
      success := ledgerAmount ⟨18, intervalDecisionTag⟩
      failure := ledgerAmount ⟨18, intervalDecisionTag⟩
      cost := ⟨14, intervalDecisionTag⟩
      execution := [trajectoryPayload 1, trajectoryPayload 2]}]

def trajectoryFixture (steps : List Instruction := trajectorySteps)
    (allowed : List ℕ := [1, 2]) (supported : Bool := true) : DecisionRun 2 :=
  runSampledDecision intervalDecisionRequest probabilityFixtureProtocol probabilityFixtureLoss
    [[0, 1], [0, 0]] (fun i => {probabilityTraining i with label := false}) probabilityCalibration
    (1/10) 8 supported id allowed trajectoryQuotes trajectoryGrants trajectoryOpening steps

/-- info: true -/
#guard_msgs in
#eval (match (trajectoryFixture trajectorySteps [1, 2] true).decision, (trajectoryFixture trajectorySteps [1, 2] true).payment.current with
  | .known selected, some post =>
      decide (selected.probability.fitted.table = [0, 0] ∧ selected.probability.estimate = 1/2 ∧
        selected.nominal.action.id = 2 ∧ selected.nominal.expectedNet.value = 4 ∧
        (trajectoryFixture trajectorySteps [1, 2] true).payment.exit = .success ∧ Ledger.balance post.state = 0 ∧
        post.state.allocated = 10 ∧ post.state.paid = 14 ∧ post.state.surplus = 4 ∧
        post.state.receipts.length = 2)
  | _, _ => false)

/-- info: true -/
#guard_msgs in
#eval
  let result := runTrajectory trajectoryGrants trajectoryOpening
    (trajectorySteps ++ [.pay (trajectoryRequest 1) .submit])
  match result.current with
  | some post => decide (result.exit = .success ∧ result.outcomes.length = 3 ∧
      Ledger.balance post.state = 0 ∧ post.state.paid = 14 ∧ post.state.receipts.length = 2 ∧
      post.revision = 2)
  | none => false

/-- info: true -/
#guard_msgs in
#eval
  let result := runTrajectory trajectoryGrants trajectoryOpening
    [.pay (trajectoryRequest 1) .submit, .pay (trajectoryRequest 1 8) .submit]
  match result.current with
  | some post => decide (result.exit = .undecided ∧ result.outcomes.length = 2 ∧
      Ledger.balance post.state = 3 ∧ post.state.paid = 7 ∧ post.state.receipts.length = 1)
  | none => false

/-- info: true -/
#guard_msgs in
#eval
  let result := runTrajectory trajectoryGrants trajectoryOpening
    [.pay (trajectoryRequest 1) .submit, .pay (trajectoryRequest 2) .unknownCommit,
      .pay (trajectoryRequest 3 0) .submit]
  decide (result.exit = .undecided ∧ result.current = none ∧ result.outcomes.length = 2 ∧
    result.outcomes[1]? = some (.unknownCommit ⟨2⟩ ⟨2⟩))

/-- info: true -/
#guard_msgs in
#eval
  let result := runTrajectory [trajectoryGrant intervalDecisionGamma (trajectoryPayload 1)]
    trajectoryOpening trajectorySteps
  match result.current with
  | some post => decide (result.exit = .rejected ∧ Ledger.balance post.state = 3 ∧
      post.state.paid = 7 ∧ result.obligations = [.authorityUnresolved])
  | none => false

/-- info: true -/
#guard_msgs in
#eval
  let changed := trajectoryFixture [.pay (trajectoryRequest 1 8) .submit,
    .pay (trajectoryRequest 2) .submit] [1, 2] true
  decide (changed.payment.exit = .rejected ∧ changed.payment.current = some trajectoryOpening ∧
    changed.payment.outcomes = [] ∧ changed.payment.obligations = [.scopeMismatch])

/-- info: true -/
#guard_msgs in
#eval (match (trajectoryFixture trajectorySteps [1, 2] true).decision with
  | .known selected =>
      let other := {trajectoryOpening with gamma := {intervalDecisionGamma with caseId := ⟨2⟩}}
      decide (executeSelected selected trajectoryGrants other trajectorySteps =
        ⟨.rejected, some other, [], [.scopeMismatch]⟩)
  | _ => false)

/-- info: true -/
#guard_msgs in
#eval
  let result := runTrajectory trajectoryGrants trajectoryOpening
    (trajectorySteps ++ [.pay (trajectoryRequest 3 0) .submit])
  match result.current with
  | some post => decide (result.exit = .success ∧ post.state.receipts.length = 3 ∧
      (⟨3⟩ : PaymentId) ∈ post.state.used ∧ Ledger.balance post.state = 0 ∧
      post.state.allocated = 10 ∧ post.state.paid = 14 ∧ post.state.surplus = 4)
  | none => false

def trajectoryNextGamma : Gamma :=
  {intervalDecisionGamma with normVersion := 2, lawDate := ⟨1⟩}

def trajectoryNextVersion : Temporal.VersionRecord :=
  ⟨⟨81⟩, 2, intervalDecisionGamma.jurisdiction, 1, ⟨1⟩, none, ⟨1⟩, ⟨1⟩⟩

def trajectoryRefresh : Pipeline.RefreshInput :=
  ⟨trajectoryNextGamma, trajectoryNextVersion, trajectoryDebt.obligor⟩

def trajectoryRefreshGrant : Authorization.Grant :=
  {trajectoryGrant intervalDecisionGamma (trajectoryPayload 1) with
    object := .document 2, action := 1, contentVersion := 2
    payload := none, nextContext := some trajectoryNextGamma}

def trajectoryNextRequest : PaymentRequest :=
  {trajectoryRequest 2 with payload := {trajectoryPayload 2 with normVersion := 2, factDate := ⟨1⟩}}

def trajectoryRefreshedSteps : List Instruction :=
  [.pay (trajectoryRequest 1) .submit, .refresh trajectoryRefresh,
    .pay trajectoryNextRequest .submit]

/-- info: true -/
#guard_msgs in
#eval
  let result := runTrajectory
    (trajectoryRefreshGrant :: trajectoryGrant trajectoryNextGamma trajectoryNextRequest.payload ::
      trajectoryGrants) trajectoryOpening trajectoryRefreshedSteps
  match result.current with
  | some post => decide (result.exit = .success ∧ post.gamma = trajectoryNextGamma ∧
      post.state.env = .known 2 ∧ post.revision = 3 ∧ Ledger.balance post.state = 0 ∧
      post.state.allocated = 10 ∧ post.state.paid = 14 ∧ post.state.surplus = 4)
  | none => false

/-- info: true -/
#guard_msgs in
#eval
  let result := runTrajectory (trajectoryRefreshGrant :: trajectoryGrants)
    trajectoryOpening trajectoryRefreshedSteps
  match result.current with
  | some post => decide (result.exit = .rejected ∧ post.gamma = trajectoryNextGamma ∧
      post.state.env = .known 2 ∧ Ledger.balance post.state = 3 ∧ post.state.paid = 7 ∧
      result.obligations = [.authorityUnresolved])
  | none => false

/-- info: true -/
#guard_msgs in
#eval
  let result := runTrajectory trajectoryGrants trajectoryOpening trajectoryRefreshedSteps
  match result.current with
  | some post => decide (result.exit = .undecided ∧ post.gamma = intervalDecisionGamma ∧
      Ledger.balance post.state = 3 ∧ result.outcomes.length = 1 ∧
      result.obligations = [.authorityUnresolved])
  | none => false

/-- info: true -/
#guard_msgs in
#eval
  let result := trajectoryFixture trajectorySteps [] true
  decide (result.decision = .unknown .notIdentified ∧ result.payment.exit = .undecided ∧
    result.payment.current = some trajectoryOpening ∧ result.payment.outcomes = [])

/-- info: true -/
#guard_msgs in
#eval
  let result := trajectoryFixture trajectorySteps [1, 2] false
  decide (result.payment.exit = .undecided ∧ result.payment.current = some trajectoryOpening ∧
    result.payment.outcomes = [])
