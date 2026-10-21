import JurisLean.Candidates.Final20261021.Iteration

namespace JurisLean.Candidates.Final20261021.Pipeline

inductive Exit where
  | success | rejected | undecided
  deriving DecidableEq, Repr

structure PaymentRun where
  exit : Exit
  current : Option Ledger.Handle
  outcomes : List Ledger.Outcome
  obligations : List Error
  deriving DecidableEq, Repr

def finishPayment (before : Ledger.Handle) (out : Ledger.Outcome) : PaymentRun :=
  match out with
  | .committed _ h => ⟨.success, some h, [out], []⟩
  | .replay _ => ⟨.success, some before, [out], []⟩
  | .rejectedNoCommit _ e => ⟨.rejected, some before, [out], [e]⟩
  | .conflict _ _ => ⟨.undecided, some before, [out], [.versionConflict]⟩
  | .unknownCommit _ _ => ⟨.undecided, none, [out], [.missingEvidence]⟩
  | .pending e => ⟨.undecided, some before, [out], [e]⟩

theorem finishPayment_outcomes (before : Ledger.Handle) (out : Ledger.Outcome) :
    (finishPayment before out).outcomes = [out] := by cases out <;> rfl

structure RefreshInput where
  gamma : Gamma
  event : Temporal.VersionRecord
  actor : PartyId
  deriving DecidableEq, Repr

def refresh (grants : List Authorization.Grant) (h : Ledger.Handle)
    (change : RefreshInput) : Result Ledger.Handle :=
  if change.gamma.caseId ≠ h.gamma.caseId then .rejected .scopeMismatch
  else if Authorization.authorized grants h.gamma change.actor 1 change.event.version
      (.document change.event.version) none (some change.gamma) = false then
    .unknown .authorityUnresolved
  else .known ⟨change.gamma, h.revision + 1,
    { h.state with normHistory := h.state.normHistory ++ [change.event],
      env := Temporal.proposed_applicability change.gamma (h.state.normHistory ++ [change.event]) }⟩

def executePayments (initial : Ledger.Handle) (first second : PaymentRequest)
    (grants : List Authorization.Grant) (mode2 : Ledger.Submission)
    (change : Option RefreshInput) : PaymentRun :=
  let permission1 := Authorization.authorized grants initial.gamma first.payload.payer 0 first.payload.normVersion
    (.relation first.payload.relation) (some first.payload)
  let out1 := Ledger.consume_ext initial initial first permission1 .submit
  match out1 with
  | .committed _ actualPost1 =>
      let prepared := match change with | none => .known actualPost1 | some c => refresh grants actualPost1 c
      match prepared with
      | .known previous_output_ref =>
          let permission2 := Authorization.authorized grants previous_output_ref.gamma second.payload.payer
            0 second.payload.normVersion (.relation second.payload.relation) (some second.payload)
          let out2 := Ledger.consume_ext previous_output_ref previous_output_ref second permission2 mode2
          let result := finishPayment previous_output_ref out2
          { result with outcomes := out1 :: result.outcomes }
      | .unknown e => ⟨.undecided, some actualPost1, [out1], [e]⟩
      | .rejected e => ⟨.rejected, some actualPost1, [out1], [e]⟩
      | .conflict _ _ => ⟨.undecided, some actualPost1, [out1], [.versionConflict]⟩
  | _ => finishPayment initial out1

theorem u00_pipeline_wires_handles (initial : Ledger.Handle)
    (first second : PaymentRequest) (grants : List Authorization.Grant)
    (mode2 : Ledger.Submission) (r1 : Ledger.Receipt) (actualPost1 : Ledger.Handle)
    (firstCommitted : Ledger.consume_ext initial initial first
      (Authorization.authorized grants initial.gamma first.payload.payer 0 first.payload.normVersion
        (.relation first.payload.relation) (some first.payload))
      -- The same full payload is used by the authorization check and executor.
      .submit = .committed r1 actualPost1) :
    executePayments initial first second grants mode2 none =
      let out2 := Ledger.consume_ext actualPost1 actualPost1 second
        (Authorization.authorized grants actualPost1.gamma second.payload.payer 0 second.payload.normVersion
          (.relation second.payload.relation) (some second.payload)) mode2
      { finishPayment actualPost1 out2 with outcomes := .committed r1 actualPost1 :: [out2] } := by
  simp [executePayments, firstCommitted, finishPayment_outcomes]

def interpretPayment (view : Representation.SourceView) (p : PaymentPayload) : Option PaymentId :=
  match view.objectMap.filter (fun pair => pair.1 == p.source) with
  | [(_, .payment id)] => some id
  | _ => none

def checkFacts (table : List (SourceRef × Nat)) : List Compiler.SupportedAtom → Result (List Nat)
  | [] => .known []
  | a :: rest =>
      match Compiler.proposed_fact_checker (fun source atom => (source, atom) ∈ table) a,
        checkFacts table rest with
      | .known atom, .known atoms => .known (atom :: atoms)
      | .unknown e, _ => .unknown e
      | _, .unknown e => .unknown e
      | _, _ => .rejected .missingEvidence

structure Input where
  view : Representation.SourceView
  debt : DebtRecord
  normHistory : List Temporal.VersionRecord
  facts : List Compiler.SupportedAtom
  supportTable : List (SourceRef × Nat)
  rules : List (Compiler.Rule Nat)
  closureFuel : Nat
  permissionAtom : Nat
  world0Actions : List Nat
  world1Actions : List Nat
  evidence : List EvidenceProcedure.EvidenceItem
  process : EvidenceProcedure.ProcessInput
  grants : List Authorization.Grant
  firstIndex : Nat
  secondIndex : Nat
  firstKey : PaymentId
  secondKey : PaymentId
  secondSubmission : Ledger.Submission
  secondRefresh : Option RefreshInput
  fitExpected : Learning.FitContract
  fitSupplied : Learning.FitContract
  calibration : Calibration.BoundPrediction
  supported : Bool
  alternatives : List Decision.Alternative
  utility : ℚ → ℚ
  utilityVersion : Nat
  riskLimit : ℚ
  observation : Behavior.MeasurementLog
  policy : Policy.PolicyRequest
  oldModel : Feedback.Assessed
  candidate : Feedback.Assessed
  secondCandidate : Feedback.Assessed
  labelStore : Feedback.LabelStore

structure Output where
  payment : PaymentRun
  judgmentProcess : Judgment × Procedure
  prediction : Result Calibration.BoundPrediction
  decision : Option Decision.DecisionIR
  observation : Result Bool
  policyValue : Result ℚ
  feedback : Result Feedback.LabelStore
  modelAfterRounds : Feedback.Assessed

def stop (i : Input) (exit : Exit) (reason : Error) : Output :=
  { payment := ⟨exit, none, [], [reason]⟩
    judgmentProcess := EvidenceProcedure.proposed_judgment_and_process i.view.gamma.question i.evidence i.process
    prediction := .unknown reason, decision := none, observation := .unknown reason,
    policyValue := .unknown reason, feedback := .unknown reason, modelAfterRounds := i.oldModel }

def runBound (i : Input) (p1 p2 : PaymentPayload) (facts : List Nat) : Output :=
  let g := i.view.gamma
  let derived := Compiler.proposed_rule_input i.rules i.closureFuel facts
  let candidates := if i.permissionAtom ∈ derived then i.world0Actions else []
  let allowed := Harness.proposed_harness_gate (W := Bool) (S := Bool)
    (fun _ => true)
    (fun world _ action => decide (action ∈ if world then i.world1Actions else i.world0Actions))
    (fun _ _ _ after => after) (fun _ after => after) true candidates
  let fit := Learning.proposed_fit_contract i.fitExpected i.fitSupplied
  let checkpointRequest : RSI.PredictionRequest :=
    ⟨i.oldModel.scope.principal, i.fitExpected.task, i.fitExpected.target,
      i.fitExpected.featureVersion, g.normVersion, g.mechanismVersion, i.oldModel.model.scope⟩
  let checkpoint := RSI.proposed_checkpoint_service checkpointRequest (some i.oldModel.model) none none none
  let prediction := match fit, checkpoint with
    | .known _, .known model =>
        if model.version = i.fitExpected.modelVersion then
          Calibration.proposed_calibration_support_gate i.fitExpected i.calibration i.riskLimit i.supported
        else .unknown .scopeMismatch
    | _, _ => .unknown .targetMismatch
  let values := i.alternatives.filterMap fun a => match Decision.evaluate g i.utility i.utilityVersion i.riskLimit a with
    | .known value => some value | _ => none
  let chosen := match prediction with
    | .known _ => Decision.proposed_decision allowed values | _ => none
  if chosen.isNone then
    { stop i .undecided .notIdentified with prediction := prediction, decision := chosen }
  else if chosen.any (fun ir => decide (ir.action.execution ≠ [p1, p2])) then
    { stop i .rejected .scopeMismatch with prediction := prediction, decision := chosen }
  else
    let base := Trace.initial g i.debt
    let initial := { base with state := { base.state with normHistory := i.normHistory,
      env := Temporal.proposed_applicability g i.normHistory } }
    match initial.state.env with
    | .known version =>
      if version ≠ g.normVersion then stop i .undecided .scopeMismatch
      else
        let req1 : PaymentRequest := ⟨i.firstKey, ⟨1⟩, p1, .yes, interpretPayment i.view p1⟩
        let req2 : PaymentRequest := ⟨i.secondKey, ⟨2⟩, p2, .yes, interpretPayment i.view p2⟩
        let payments := executePayments initial req1 req2 i.grants i.secondSubmission i.secondRefresh
        let observation := match payments.current with
          | none => .unknown .missingEvidence
          | some current =>
              let log := { i.observation with outcome :=
                if Ledger.balance current.state = 0 then some true else i.observation.outcome }
              Behavior.proposed_measurement i.fitExpected.target log
        let policyValue := match observation with
          | .known y => Policy.proposed_off_policy_value { i.policy with outcome := Behavior.indicator y }
          | _ => .unknown .notIdentified
        let feedback := match observation with
          | .known y => Feedback.addLabel i.labelStore
              ⟨i.observation.unit, i.fitExpected.target, y, i.observation.externalSource, .external⟩
          | _ => .unknown .missingEvidence
        let updated := match feedback, policyValue with
          | .known _, .known _ => Iteration.twoRounds i.oldModel i.candidate i.secondCandidate
          | _, _ => i.oldModel
        { payment := payments,
          judgmentProcess := EvidenceProcedure.proposed_judgment_and_process g.question i.evidence i.process,
          prediction := prediction, decision := chosen, observation := observation,
          policyValue := policyValue, feedback := feedback, modelAfterRounds := updated }
    | .unknown e => stop i .undecided e
    | .rejected e => stop i .rejected e
    | .conflict _ _ => stop i .undecided .versionConflict

def run (i : Input) : Output :=
  match Representation.proposed_common_model i.view i.firstIndex,
    Representation.proposed_common_model i.view i.secondIndex, checkFacts i.supportTable i.facts with
  | .known p1, .known p2, .known facts => runBound i p1 p2 facts
  | .rejected e, _, _ => stop i .rejected e
  | _, .rejected e, _ => stop i .rejected e
  | .conflict _ _, _, _ => stop i .undecided .versionConflict
  | _, .conflict _ _, _ => stop i .undecided .versionConflict
  | _, _, .rejected e => stop i .rejected e
  | _, _, .conflict _ _ => stop i .undecided .versionConflict
  | .unknown e, _, _ => stop i .undecided e
  | _, .unknown e, _ => stop i .undecided e
  | _, _, .unknown e => stop i .undecided e

end JurisLean.Candidates.Final20261021.Pipeline
