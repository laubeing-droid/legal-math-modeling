import JurisLean.Candidates.Final20261021.Pipeline

/-! Synthetic fixtures only. Every theorem below still requires fresh CI.
No concrete example is a substitute for the universally quantified lemmas.
-/
namespace JurisLean.Candidates.Final20261021.Acceptance

set_option maxRecDepth 4096
set_option maxHeartbeats 800000

def txRequest (_ : Nat) : Nat × ℚ := (1, 7)
def txEval (before payment : ℚ) : Option (ℚ × ℚ) :=
  some (max (before-payment) 0, min payment before)
def txOpening : Transactions.Store ℚ ℚ ℚ := ⟨10, 0, fun _ => none, fun _ => false⟩
def txCommitted : Transactions.Store ℚ ℚ ℚ :=
  Transactions.commitStore txRequest txOpening 1 3 7

theorem a02_transaction_actual_commit :
    Transactions.Step txRequest txEval txOpening (.commit 1 1) txCommitted := by
  apply Transactions.Step.commit txOpening 1 0 3 7 <;>
    norm_num [txOpening, txRequest, txEval]

theorem a02_transaction_actual_replay :
    Transactions.Step txRequest txEval txCommitted (.replay 2 1) txCommitted := by
  apply Transactions.Step.replay txCommitted 2 ⟨7, 1, 10, 3, 0, 1, 7⟩
  · simp [txCommitted, Transactions.commitStore, txRequest, txOpening]
  · rfl

theorem n02_cancelled_attempt_no_commit (after : Transactions.Store ℚ ℚ ℚ) :
    ¬ Transactions.Step txRequest txEval (Transactions.abortStore txOpening 2) (.commit 2 1) after := by
  exact Transactions.cancelled_cannot_commit txRequest txEval 2 1 (by rfl)

theorem n07_1_constant_family_not_separating :
    ¬ Representation.Separates (fun _ : Unit => True) (fun _ (_ : Bool) => false) := by
  intro separates
  have impossible := separates false true (fun _ _ => rfl)
  cases impossible

theorem a07_1_identity_observation_separates :
    Representation.Separates (fun _ : Bool => True) (fun observation (a : Bool) =>
      if observation then a else false) := by
  intro a b same
  simpa using same true (by trivial)

theorem n07_1_retraction_need_not_encode_surjectively :
    (∀ x : Unit, (fun _ : Bool => ()) ((fun _ : Unit => false) x) = x) ∧
      ¬ Function.Surjective (fun _ : Unit => false) := by
  constructor
  · intro x; cases x; rfl
  · intro onto
    obtain ⟨x, impossible⟩ := onto true
    cases impossible

def tag : AmountTag := ⟨"SYN", "unit", 0⟩
def gamma : Gamma :=
  { caseId := ⟨1⟩, caseRevision := 0, evidenceVersion := 0, jurisdiction := "SYNTH",
    question := 0, interpretation := 0, normVersion := 0, lawDate := ⟨6⟩,
    knowledgeCutoff := ⟨6⟩, recordCutoff := ⟨6⟩, schemaVersion := 0,
    observationFamily := 0, mechanismVersion := 0 }
def debt : DebtRecord := ⟨⟨1⟩, ⟨1⟩, ⟨2⟩, ⟨10, tag⟩, "synthetic debt"⟩
def payload (id : Nat) (amount : ℚ := 7) : PaymentPayload :=
  ⟨gamma.caseId, 0, debt.relation, debt.obligor, debt.creditor,
    ⟨amount, tag⟩, ⟨id⟩, ⟨id⟩, 0, gamma.lawDate⟩
def version : Temporal.VersionRecord :=
  ⟨⟨80⟩, 0, "SYNTH", 0, ⟨0⟩, none, ⟨0⟩, ⟨0⟩⟩
def opening : Ledger.Handle :=
  let h := Trace.initial gamma debt
  { h with state := { h.state with normHistory := [version], env := .known 0 } }
def request (id : Nat) (amount : ℚ := 7) : PaymentRequest :=
  ⟨⟨id⟩, ⟨id⟩, payload id amount, .yes, some ⟨id⟩⟩
def grant (p : PaymentPayload) : Authorization.Grant :=
  { evidence := ⟨90⟩, subject := debt.obligor, caseId := gamma.caseId,
    context := gamma,
    object := .relation debt.relation, action := 0, contentVersion := 0,
    payload := some p, nextContext := none, authorityRuleVersion := 0, fromDate := ⟨0⟩, untilDate := ⟨100⟩ }
def grants : List Authorization.Grant := [grant (payload 1), grant (payload 2)]
def post1 : Ledger.Handle := (Ledger.commitPayment opening (request 1)).2
def post2 : Ledger.Handle := (Ledger.commitPayment post1 (request 2)).2

theorem a_opening_invariant : Trace.Invariant opening := by
  obtain ⟨numeric, cash, _, receipts⟩ := Trace.initial_invariant gamma debt (by decide)
  exact ⟨numeric, cash, by decide, receipts⟩

theorem a_two_actual_commits_preserve_receipts : Trace.Invariant post2 := by
  have first : Trace.Invariant post1 := Trace.step_preserves
    (Trace.u10_2_committed_executor_is_step opening opening (request 1) true .submit
      (Ledger.commitPayment opening (request 1)).1 post1 (by decide)) a_opening_invariant
  exact Trace.step_preserves
    (Trace.u10_2_committed_executor_is_step post1 post1 (request 2) true .submit
      (Ledger.commitPayment post1 (request 2)).1 post2 (by decide)) first

theorem a_u09_continuous_10_7_7 :
    Ledger.balance post1.state = 3 ∧ Ledger.balance post2.state = 0 ∧
    post2.state.allocated = 10 ∧ post2.state.paid = 14 ∧ post2.state.surplus = 4 := by decide

theorem a_u09_three_observations :
    Ledger.forms post2.state debt.relation = true ∧ Ledger.balance post2.state = 0 ∧
    post2.state.claim = .unknown ∧ post2.state.procedure = .open := by decide

theorem n_a1_layer_collapse :
    Ledger.auditPerformanceLayers post2.state
      { post2.state with formations := [], procedure := .closedLawfully } =
      .rejected .layerCollapse := by decide

theorem n_non_continuous_consume :
    Ledger.balance (Ledger.commitPayment opening (request 2)).2.state = 3 ∧
    Ledger.balance (Ledger.commitPayment post1 (request 2)).2.state = 0 := by decide

theorem n_poststate_name_not_binding :
    Ledger.consume_ext post1 opening (request 2) true .submit =
      .rejectedNoCommit ⟨2⟩ .prestateRequired := by decide

theorem a_zero_yes_writes_U :
    Ledger.consume_ext opening opening (request 3 0) true .submit =
      .committed (Ledger.commitPayment opening (request 3 0)).1
        (Ledger.commitPayment opening (request 3 0)).2 ∧
    (PaymentId.mk 3) ∈ (Ledger.commitPayment opening (request 3 0)).2.state.used ∧
    Ledger.balance (Ledger.commitPayment opening (request 3 0)).2.state = 10 := by decide

theorem n_unknown_does_not_burn_U :
    Ledger.consume_ext opening opening (request 1) true .unknownCommit =
      .unknownCommit ⟨1⟩ ⟨1⟩ ∧
    (Ledger.consume_ext opening opening (request 1) true .unknownCommit).post opening = none := by decide

theorem n_burned_by_unknown :
    Ledger.auditUnknownReport opening.state { opening.state with used := {⟨1⟩} } =
      .rejected .burnedByUnknown := by decide

theorem n_identity_unknown_no_U :
    Ledger.consume_ext opening opening { request 1 with interpretedPayment := none } true .submit =
      .pending .identityUnknown := by decide

theorem n_applicability_unknown_no_U :
    Ledger.consume_ext opening opening { request 1 with applicable := .unknown } true .submit =
      .pending .applicabilityUnknown := by decide

theorem n_not_applicable_zero_no_U :
    Ledger.consume_ext opening opening { request 3 0 with applicable := .no } true .submit =
      .rejectedNoCommit ⟨3⟩ .notApplicable := by decide

theorem n09_1_replay_original_receipt :
    Ledger.consume_ext post2 post2 (request 1) false .submit =
      .replay (Ledger.commitPayment opening (request 1)).1 := by decide

theorem n09_1_payload_conflict :
    Ledger.consume_ext post2 post2 (request 1 9) true .submit =
      .conflict (payload 1) (payload 1 9) := by decide

theorem n09_2_state_conservation_mismatch :
    Ledger.auditReceipt (Ledger.commitPayment opening (request 1)).1 opening.state =
      .rejected .stateConservationMismatch := by decide

theorem n09_3_rounding_basis_missing :
    Ledger.displayMinor ⟨1/2, tag⟩ 2 none = .unknown .roundingBasisMissing := rfl

theorem n09_4_accrual_not_cash :
    (Ledger.accrue post1.state 1).cash = post1.state.cash ∧
    Ledger.auditAccrualReport post1.state { post1.state with paid := 8 } =
      .rejected .accrualCashCollapse := by decide

theorem n09_5_unit_binding_missing :
    Ledger.consume_ext opening opening
      { request 1 with payload := { payload 1 with amount := ⟨7, { tag with currency := "OTHER" }⟩ } }
      true .submit = .rejectedNoCommit ⟨1⟩ .unitBindingMissing := by decide

def restWitness : Ledger.RestClaimWitness := ⟨⟨2⟩, ⟨2⟩, ⟨1⟩, ⟨3, tag⟩, ⟨100⟩⟩
def claimed : Ledger.State :=
  { post1.state with formations := post1.state.formations ++ [⟨2⟩],
    rest := some ⟨⟨2⟩, ⟨2⟩, ⟨1⟩, ⟨3, tag⟩, false, ⟨100⟩, none⟩ }
def eligible : Ledger.State :=
  { claimed with rest := some ⟨⟨2⟩, ⟨2⟩, ⟨1⟩, ⟨3, tag⟩, true, ⟨100⟩, some ⟨101⟩⟩ }
def refund : CashEvent := ⟨⟨3⟩, ⟨102⟩, ⟨2⟩, ⟨1⟩, ⟨3, tag⟩⟩

theorem a_rest_claim_then_eligibility :
    Ledger.RestClaim post1.state restWitness = .known claimed ∧
    Ledger.ExecEligible claimed ⟨2⟩ ⟨101⟩ = .known eligible ∧
    eligible.cash = post1.state.cash ∧ eligible.refundCash = [] := by decide

theorem n1_premature_cash : Ledger.RestPay post1.state refund = .rejected .prematureCash := by decide
theorem n2_auto_full_refund : Ledger.RestPay claimed
    { refund with amount := ⟨7, tag⟩ } = .rejected .autoFullRefund := by decide
theorem n3_accrual_cash_collapse : Ledger.auditAccrualReport eligible
    { Ledger.accrue eligible 1 with refundCash := [refund] } = .rejected .accrualCashCollapse := by decide

theorem a_restpay_only_n3 :
    Ledger.RestPay eligible refund = .known
      { eligible with rest := some ⟨⟨2⟩, ⟨2⟩, ⟨1⟩, ⟨0, tag⟩, true, ⟨100⟩, some ⟨101⟩⟩,
        refundCash := [refund] } := by decide

theorem n_exact_half_and_currency :
    Decision.evalExact (.rational (1/2)) = (1/2 : ℚ) ∧
    Decision.addValues (Decision.ledgerAmount ⟨1, tag⟩)
      (Decision.ledgerAmount ⟨1, { tag with currency := "OTHER" }⟩) = .rejected .mixedCurrency := by decide

def process : EvidenceProcedure.ProcessInput := ⟨[1], [1], [], [], [], none, [], false⟩
theorem n08_2_missing_opportunity : EvidenceProcedure.procedure process = .open := by decide
theorem n08_4_timeout_not_lawful_closure : EvidenceProcedure.procedure
    { process with blocked := true } = .blocked := by decide

theorem a08_insufficient_but_lawfully_closed :
    EvidenceProcedure.proposed_judgment_and_process 0 []
      { process with records := [⟨1, 0, none, some ⟨70⟩, []⟩], validWaivers := [⟨70⟩],
        closureAuthority := some ⟨71⟩, validClosureAuthorities := [⟨71⟩] } =
      (.insufficient, .closedLawfully) := by decide

def ruleA : Temporal.VersionRecord := { version with factUntil := some ⟨10⟩ }
def ruleB : Temporal.VersionRecord := { version with id := ⟨81⟩, version := 1, factFrom := ⟨10⟩ }
theorem a08_event_specific_versions :
    Temporal.proposed_applicability { gamma with lawDate := ⟨5⟩ } [ruleA, ruleB] = .known 0 ∧
    Temporal.proposed_applicability { gamma with lawDate := ⟨12⟩ } [ruleA, ruleB] = .known 1 := by decide

theorem n08_latest_case_time_wrong_for_first_event :
    Temporal.proposed_applicability { gamma with lawDate := ⟨12⟩ } [ruleA, ruleB] ≠
      Temporal.proposed_applicability { gamma with lawDate := ⟨5⟩ } [ruleA, ruleB] := by decide

def view : Representation.SourceView :=
  ⟨gamma, [.formation debt.relation, .performance (payload 1), .performance (payload 2)],
    [(⟨50⟩, .relation debt.relation), (⟨1⟩, .payment ⟨1⟩), (⟨2⟩, .payment ⟨2⟩)],
    ⟨50⟩, debt.relation⟩
def fit : Learning.FitContract := ⟨0, 0, 0, 0, 0, ⟨30⟩, ⟨1⟩⟩
def checkpoint (id : Nat) : RSI.Checkpoint :=
  ⟨⟨1⟩, 0, 0, 0, 0, 0, 0, id, [], 1/2, ⟨200⟩⟩
def scope : Feedback.Scope := ⟨0, 0, 0, 0, 0, ⟨1⟩, [0]⟩
def assessed (id : Nat) (risk : ℚ) : Feedback.Assessed :=
  ⟨scope, checkpoint id, risk, risk, 0, 0, 0⟩
def alternative : Decision.Alternative :=
  ⟨0, [⟨90⟩], some ⟨201⟩, [⟨1, ⟨.rational 4, some tag⟩, []⟩], ⟨0, tag⟩, [payload 1, payload 2]⟩
def input : Pipeline.Input :=
  { view := view, debt := debt, normHistory := [version], facts := [⟨0, ⟨50⟩, 0⟩],
    supportTable := [(⟨50⟩, 0)], rules := [], closureFuel := 1, permissionAtom := 0,
    world0Actions := [0], world1Actions := [0], evidence := [], process := process,
    grants := grants, firstIndex := 1, secondIndex := 2, firstKey := ⟨1⟩, secondKey := ⟨2⟩,
    secondSubmission := .submit, secondRefresh := none,
    fitExpected := fit, fitSupplied := fit,
    calibration := ⟨fit, 1, 0, 0, 0, [0]⟩, supported := true,
    alternatives := [alternative], utility := id, utilityVersion := 0, riskLimit := 1/10,
    observation := ⟨⟨1⟩, ⟨2⟩, ⟨1⟩, 0, 0, ⟨30⟩, ⟨7⟩, some true, some ⟨202⟩, ⟨203⟩⟩,
    policy := ⟨gamma.caseId, 0, 0, 1/2, 1/2, 0, some ⟨204⟩⟩,
    oldModel := assessed 0 (1/2), candidate := assessed 1 0,
    secondCandidate := { assessed 2 0 with scope := { scope with target := 1 } },
    labelStore := ⟨[], [], []⟩ }

theorem u00_pipeline_success :
    (Pipeline.run input).payment.exit = .success ∧
    ((Pipeline.run input).payment.current.map (fun h => Ledger.balance h.state)) = some 0 ∧
    (Pipeline.run input).modelAfterRounds = assessed 1 0 := by decide

theorem u00_pipeline_reject :
    (Pipeline.run { input with grants := [grant (payload 1)] }).payment.exit = .rejected ∧
    ((Pipeline.run { input with grants := [grant (payload 1)] }).payment.current.map
      (fun h => Ledger.balance h.state)) = some 3 := by decide

theorem u00_pipeline_unknown :
    (Pipeline.run { input with secondSubmission := .unknownCommit }).payment.exit = .undecided ∧
    (Pipeline.run { input with secondSubmission := .unknownCommit }).payment.current = none := by decide

theorem n_pipeline_score_does_not_authorize :
    (Pipeline.run { input with grants := [] }).payment.exit = .rejected := by decide

theorem n_pipeline_unresolved_identity :
    (Pipeline.run { input with view := { view with objectMap := [(⟨50⟩, .relation debt.relation)] } }).payment.exit
      = .undecided := by decide

theorem n_pipeline_target_mismatch :
    (Pipeline.run { input with fitSupplied := { fit with target := 1 } }).payment.exit = .undecided := by decide

theorem n_pipeline_decision_payload_mismatch :
    (Pipeline.run { input with alternatives := [{ alternative with execution := [payload 1 9, payload 2] }] }).payment.exit
      = .rejected := by decide

theorem n_pipeline_zero_balance_no_external_label :
    let output := Pipeline.run { input with observation := { input.observation with outcome := none } }
    output.payment.current.map (fun h => Ledger.balance h.state) = some 0 ∧
      output.observation = .unknown .missingEvidence ∧
      output.feedback = .unknown .missingEvidence ∧ output.modelAfterRounds = input.oldModel := by decide

theorem n03_incomplete_fuel_is_not_closure :
    Compiler.proposed_checked_rule_input [⟨[0], 1⟩, ⟨[1], 2⟩] 1 [0] =
      .unknown .checkIncomplete ∧
    Compiler.proposed_checked_rule_input [⟨[0], 1⟩, ⟨[1], 2⟩] 2 [0] =
      .known [0, 1, 1, 2] := by decide

theorem n07_observation_wrong_relation :
    Representation.proposed_source_view { view with observedRelation := ⟨2⟩ } =
      .rejected .observationBindingMismatch := by decide

def disjunctiveRules : List (Compiler.Rule Nat) := [⟨[1], 3⟩, ⟨[2], 3⟩]
theorem n03_must_facts_closure_is_not_robust_closure :
    3 ∈ Compiler.proposed_rule_input disjunctiveRules 2 [1] ∧
    3 ∈ Compiler.proposed_rule_input disjunctiveRules 2 [2] ∧
    3 ∉ Compiler.proposed_rule_input disjunctiveRules 2 [] := by decide

theorem n03_missing_exception_is_not_positive_witness :
    3 ∉ Compiler.proposed_rule_input [⟨[1, 4], 3⟩] 2 [1] ∧
    3 ∈ Compiler.proposed_rule_input [⟨[1, 4], 3⟩] 2 [1, 4] := by decide

theorem a02_common_idle_remains_allowed :
    Harness.proposed_harness_gate (W := Bool) (S := Bool) (fun _ => true)
      (fun w _ a => decide (a = 0 ∨ a = if w then 1 else 2))
      (fun _ _ _ after => after) (fun _ after => after) true [0, 1, 2] = [0] := by decide

theorem n10_authorization_binds_full_payload :
    Authorization.authorized [grant (payload 1)] gamma debt.obligor 0 0
      (.relation debt.relation) (some (payload 1 9)) = false := by decide

theorem n04_zero_variance_not_finite_count :
    Probability.u04_4_variance_equivalent 2 (-1) = .degenerateZeroVariance := by decide

theorem n05_raising_score_threshold_increases_risk :
    Harness.conditionalRisk (1/10) 1 = .known (1/10) ∧
    Harness.conditionalRisk (1/10) (1/10) = .known 1 := by decide

def riskyAlternative : Decision.Alternative :=
  { alternative with id := 1, outcomes := [⟨1/2, ⟨.rational (-1), some tag⟩, []⟩,
    ⟨1/2, ⟨.rational 11, some tag⟩, []⟩] }
def decisionValues : List Decision.DecisionIR :=
  [riskyAlternative, alternative].filterMap fun a =>
    match Decision.evaluate gamma id 0 (1/10) a with | .known v => some v | _ => none
theorem a06_risk_gate_precedes_expected_value :
    (Decision.proposed_decision [0, 1] decisionValues).map (fun d => d.action.id) = some 0 := by decide

theorem n06_probability_has_no_money_dimension :
    Decision.evaluate gamma id 0 (1/10)
      { alternative with outcomes := [⟨1, ⟨.rational (4/5), none⟩, []⟩] } =
      .rejected .mixedCurrency := by decide

theorem n06_duplicate_cash_identity :
    Decision.evaluate gamma id 0 (1/10)
      { alternative with outcomes := [⟨1, ⟨.rational 4, some tag⟩, [⟨1⟩, ⟨1⟩]⟩] } =
      .rejected .duplicateCash := by decide

theorem n11_window_not_mature_negative_unknown :
    Behavior.proposed_measurement 0 { input.observation with outcome := some false } =
      .unknown .missingEvidence := by decide

theorem n12_support_gap_not_smoothed :
    Policy.proposed_off_policy_value { input.policy with loggingProbability := 0 } =
      .unknown .notIdentified := by decide

theorem n13_absent_is_not_half_probability :
    RSI.proposed_checkpoint_service ⟨⟨1⟩, 0, 0, 0, 0, 0, 0⟩ none none none none =
      .unknown .missingEvidence := by decide

theorem n14_evaluated_is_not_loaded :
    Feedback.loadAccepted gamma [] (assessed 0 (1/2)) (assessed 1 0) 0
      (checkpoint 1) ⟨205⟩ = .unknown .authorityUnresolved := by decide

theorem n14_wrong_bytes_do_not_load :
    Feedback.loadAccepted gamma [] (assessed 0 (1/2)) (assessed 1 0) 0
      { checkpoint 1 with bytes := [1] } ⟨205⟩ = .rejected .scopeMismatch := by decide

theorem n14_self_suggestion_is_not_external_label :
    Feedback.addLabel ⟨[], [], []⟩ ⟨⟨1⟩, 0, true, ⟨206⟩, .suggestion⟩ =
      .rejected .missingEvidence := by decide

end JurisLean.Candidates.Final20261021.Acceptance
