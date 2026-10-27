import JurisLean.Candidates.LoadedLegalConsumer20261027
import JurisLean.Candidates.LegalActionDomainAudit20261027
import JurisLean.Candidates.ValidatedFeedbackLoadAudit20261027

#check JurisLean.Candidates.LoadedLegalConsumer20261027.known_probability_binds_actual_loaded_and_sample
#print axioms JurisLean.Candidates.LoadedLegalConsumer20261027.known_probability_binds_actual_loaded_and_sample
#check JurisLean.Candidates.LoadedLegalConsumer20261027.changed_loaded_contents_refuse_old_calibration
#print axioms JurisLean.Candidates.LoadedLegalConsumer20261027.changed_loaded_contents_refuse_old_calibration
#check JurisLean.Candidates.LoadedLegalConsumer20261027.missing_calibration_attestation_stays_unknown
#print axioms JurisLean.Candidates.LoadedLegalConsumer20261027.missing_calibration_attestation_stays_unknown
#check JurisLean.Candidates.LoadedLegalConsumer20261027.selected_decision_reads_same_probability_and_quote
#print axioms JurisLean.Candidates.LoadedLegalConsumer20261027.selected_decision_reads_same_probability_and_quote
#check JurisLean.Candidates.LoadedLegalConsumer20261027.loaded_run_uses_actual_legal_validation
#print axioms JurisLean.Candidates.LoadedLegalConsumer20261027.loaded_run_uses_actual_legal_validation
#check JurisLean.Candidates.LoadedLegalConsumer20261027.loaded_run_choice_uses_current_model
#print axioms JurisLean.Candidates.LoadedLegalConsumer20261027.loaded_run_choice_uses_current_model
#check JurisLean.Candidates.LoadedLegalConsumer20261027.loaded_run_preserves_reported_business_invariant
#print axioms JurisLean.Candidates.LoadedLegalConsumer20261027.loaded_run_preserves_reported_business_invariant
#check JurisLean.Candidates.LoadedLegalConsumer20261027.unknown_loaded_probability_has_no_transaction_effect
#print axioms JurisLean.Candidates.LoadedLegalConsumer20261027.unknown_loaded_probability_has_no_transaction_effect
#check JurisLean.Candidates.LoadedLegalConsumer20261027.frozen_family_probability_confidence
#print axioms JurisLean.Candidates.LoadedLegalConsumer20261027.frozen_family_probability_confidence

open JurisLean.Candidates.Final20261021
open JurisLean.Candidates.LearningConsumer20261027
open JurisLean.Candidates.SampleCalibrationConsumer20261027
open JurisLean.Candidates.ProbabilityIntervalConsumer20261027
open JurisLean.Candidates.IntervalDecisionConsumer20261027
open JurisLean.Candidates.DecisionTrajectoryConsumer20261027
open JurisLean.Candidates.EventFeedbackConsumer20261027
open JurisLean.Candidates.ProtectedFeedback20261027
open JurisLean.Candidates.ValidatedFeedbackLoad20261027
open JurisLean.Candidates.AdaptiveRoundLedger20261027
open JurisLean.Candidates.LegalActionDomain20261027
open JurisLean.Candidates.LoadedLegalConsumer20261027

namespace JurisLean.Candidates.LoadedLegalConsumer20261027.Audit

def base (service : Service 2) : RoundState 2 :=
  ⟨{service with gamma := intervalDecisionGamma}, ⟨1, [[1, 1]]⟩, 55, 3, 1/5, [10, 20], [], none, []⟩

def request (state : RoundState 2) : DecisionRequest 2 :=
  {intervalDecisionRequest with protocol := (readLoaded state.service).fitted.protocol}

def rows : List (SampleObservation 2 Bool) := List.ofFn fun i : Fin 400 =>
  ⟨⟨10000 + i.val⟩, if i.val < 200 then 0 else 1, decide (200 ≤ i.val)⟩

def packet (state : RoundState 2) : CalibrationPacket 2 :=
  ⟨state.service.gamma, readLoaded state.service, [[0, 0], [0, 1]], rows, 100,
    ⟨0⟩, ⟨10⟩, ⟨80⟩, true⟩

def probability (state : RoundState 2) (p : CalibrationPacket 2)
    (catalog : List (CalibrationPacket 2)) : Result (SampleProbability 2) :=
  loadedProbability state (request state) p catalog (1/10) 8

def fixture (state : RoundState 2) : LoadedRun (List Nat) 2 :=
  runLoaded LegalActionDomain20261027.Audit.legalInput LegalActionDomain20261027.Audit.actionModel
    LegalActionDomain20261027.Audit.proposals state (request state) (packet state) [packet state]
    (1/10) 8 id trajectoryGrants trajectoryOpening

-- The actual loaded parent is [0,0]; a learner proposing [1,1] cannot replace it.
/-- info: true -/
#guard_msgs in
#eval ValidatedFeedbackLoadFixture.check (fun service _ =>
  let state := base service
  let out := fixture state
  match out.probability, out.decision, out.execution.payment.current with
  | .known p, .known d, some post => decide (p.fitted = (readLoaded state.service).fitted ∧
      p.fitted.table = [0, 0] ∧ p.estimate = 1/2 ∧ d.nominal.action.id = 2 ∧
      post.state.allocated = 10 ∧ post.state.paid = 14 ∧ post.state.surplus = 4 ∧
      Ledger.balance post.state = 0)
  | _, _, _ => false)

/-- info: true -/
#guard_msgs in
#eval ValidatedFeedbackLoadFixture.check (fun service _ =>
  let state := base service
  decide ((fixture {state with learner := ⟨99, [[1, 0], [1, 1]]⟩}).probability = (fixture state).probability))

/-- info: true -/
#guard_msgs in
#eval ValidatedFeedbackLoadFixture.check (fun service _ =>
  let state := base service
  decide (probability state (packet state) [] = .unknown .scopeMismatch))

/-- info: true -/
#guard_msgs in
#eval ValidatedFeedbackLoadFixture.check (fun service _ =>
  let state := base service
  let changed := {packet state with loaded := {state.service.loaded with
    fitted := {state.service.loaded.fitted with table := [0, 1]}}}
  decide (probability state changed [changed] = .unknown .scopeMismatch))

/-- info: true -/
#guard_msgs in
#eval ValidatedFeedbackLoadFixture.check (fun service _ =>
  let state := base service
  let changed := {packet state with context := {state.service.gamma with caseId := ⟨99⟩}}
  decide (probability state changed [changed] = .unknown .scopeMismatch))

/-- info: true -/
#guard_msgs in
#eval ValidatedFeedbackLoadFixture.check (fun service _ =>
  let state := base service
  let changed := {packet state with snapshot := 101}
  decide (probability state changed [changed] = .unknown .scopeMismatch))

/-- info: true -/
#guard_msgs in
#eval ValidatedFeedbackLoadFixture.check (fun service _ =>
  let state := base service
  let changed := {packet state with rows := [⟨⟨10000⟩, 0, false⟩, ⟨⟨10000⟩, 1, true⟩]}
  decide (probability state changed [changed] = .unknown .scopeMismatch))

/-- info: true -/
#guard_msgs in
#eval ValidatedFeedbackLoadFixture.check (fun service _ =>
  let state := base service
  let changed := {packet state with rows := [⟨⟨1⟩, 0, false⟩]}
  decide (probability state changed [changed] = .unknown .scopeMismatch))

/-- info: true -/
#guard_msgs in
#eval ValidatedFeedbackLoadFixture.check (fun service _ =>
  let state := base service
  let changed := {packet state with rows := rows.map fun row => {row with label := !row.label}}
  decide (probability state changed [packet state] = .unknown .scopeMismatch))

/-- info: true -/
#guard_msgs in
#eval ValidatedFeedbackLoadFixture.check (fun service _ =>
  let state := base service
  let changed := {packet state with rows := []}
  decide (probability state changed [changed] = .unknown .missingEvidence))

/-- info: true -/
#guard_msgs in
#eval ValidatedFeedbackLoadFixture.check (fun service _ =>
  let state := base service
  let changed := {packet state with models := [[0, 1]]}
  decide (probability state changed [changed] = .unknown .scopeMismatch))

/-- info: true -/
#guard_msgs in
#eval ValidatedFeedbackLoadFixture.check (fun service _ =>
  let state := base service
  let changed := {packet state with models := [[0, 0], [0]]}
  decide (probability state changed [changed] = .unknown .scopeMismatch))

/-- info: true -/
#guard_msgs in
#eval ValidatedFeedbackLoadFixture.check (fun service _ =>
  let state := base service
  let changed := {packet state with supported := false}
  decide (probability state changed [changed] = .unknown .unsupported))

/-- info: true -/
#guard_msgs in
#eval ValidatedFeedbackLoadFixture.check (fun service _ =>
  let state := base service
  let changed := {packet state with declaredAt := ⟨10⟩}
  decide (probability state changed [changed] = .unknown .scopeMismatch))

/-- info: true -/
#guard_msgs in
#eval ValidatedFeedbackLoadFixture.check (fun service _ =>
  let state := base service
  let changed := {packet state with acquiredAt := ⟨11⟩}
  decide (probability state changed [changed] = .unknown .scopeMismatch))

-- This is an actual activation, with the existing exact sampling and load gates.
-- An old packet is refused, and a newly bound packet reads the changed bin.
/-- info: true -/
#guard_msgs in
#eval ValidatedFeedbackLoadFixture.check (fun service evaluation =>
  let before := base service
  let sampling := ValidatedFeedbackLoadFixture.sampling evaluation
  let permit := ValidatedFeedbackLoadFixture.permit before.service evaluation
  let loaded := activate before.service evaluation [sampling] sampling [permit] permit
  let after := {before with service := loaded.post}
  let old := packet before
  let fresh := packet after
  match probability before old [old], probability after fresh [fresh] with
  | .known p0, .known p1 => decide (loaded.status = .loaded ∧
      probability after old [old] = .unknown .scopeMismatch ∧ p0.estimate = 1/2 ∧
      p1.estimate = 1 ∧ p1.fitted = (readLoaded loaded.post).fitted)
  | _, _ => false)

/-- info: true -/
#guard_msgs in
#eval ValidatedFeedbackLoadFixture.check (fun service evaluation =>
  let before := base service
  let sampling := ValidatedFeedbackLoadFixture.sampling evaluation
  let permit := ValidatedFeedbackLoadFixture.permit before.service evaluation
  let loaded := activate before.service evaluation [sampling] sampling [permit] permit
  let after := {before with service := loaded.post}
  let actual := runLoaded LegalActionDomain20261027.Audit.legalInput
    LegalActionDomain20261027.Audit.actionModel LegalActionDomain20261027.Audit.proposals after
    {request after with riskLimit := 2/5} (packet after) [packet after] (1/10) 8 id
    trajectoryGrants trajectoryOpening
  match actual.decision with
  | .known d => decide (loaded.status = .loaded ∧ d.nominal.action.id = 1 ∧
      d.probability.fitted = (readLoaded loaded.post).fitted)
  | _ => false)

/-- info: true -/
#guard_msgs in
#eval ValidatedFeedbackLoadFixture.check (fun service _ =>
  let state := base service
  let actual := runLoaded {LegalActionDomain20261027.Audit.legalInput with branches := []}
    LegalActionDomain20261027.Audit.actionModel LegalActionDomain20261027.Audit.proposals state
    (request state) (packet state) [packet state] (1/10) 8 id trajectoryGrants trajectoryOpening
  decide (actual.execution.proposal = none ∧ actual.execution.payment.current = some trajectoryOpening ∧
    actual.execution.payment.outcomes = []))

/-- info: true -/
#guard_msgs in
#eval ValidatedFeedbackLoadFixture.check (fun service _ =>
  let state := base service
  let actual := runLoaded LegalActionDomain20261027.Audit.legalInput
    LegalActionDomain20261027.Audit.actionModel LegalActionDomain20261027.Audit.proposals state
    (request state) (packet state) [] (1/10) 8 id trajectoryGrants trajectoryOpening
  decide (actual.probability = .unknown .scopeMismatch ∧ actual.execution.proposal = none ∧
    actual.execution.payment.current = some trajectoryOpening ∧ actual.execution.payment.outcomes = []))

/-- info: true -/
#guard_msgs in
#eval ValidatedFeedbackLoadFixture.check (fun service _ =>
  let state := base service
  let actual := runLoaded LegalActionDomain20261027.Audit.legalInput
    LegalActionDomain20261027.Audit.actionModel LegalActionDomain20261027.Audit.proposals state
    (request state) (packet state) [packet state] (1/10) 8 id [] trajectoryOpening
  decide (actual.execution.payment.current = some trajectoryOpening ∧
    actual.execution.payment.exit = Pipeline.Exit.rejected))

end JurisLean.Candidates.LoadedLegalConsumer20261027.Audit
