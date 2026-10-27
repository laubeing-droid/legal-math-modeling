import JurisLean.Candidates.MeasuredPolicy20261027
import JurisLean.Candidates.BusinessMeasurementAudit20261027
import JurisLean.Candidates.AdaptiveRoundLedgerAudit20261027

#check JurisLean.Candidates.MeasuredPolicy20261027.measured_policy_row_preserves_actual_output
#print axioms JurisLean.Candidates.MeasuredPolicy20261027.measured_policy_row_preserves_actual_output
#check JurisLean.Candidates.MeasuredPolicy20261027.measured_policy_pipeline_reads_actual_measurement
#print axioms JurisLean.Candidates.MeasuredPolicy20261027.measured_policy_pipeline_reads_actual_measurement
#check JurisLean.Candidates.MeasuredPolicy20261027.selected_policy_reads_numeric_bounds_and_permission
#print axioms JurisLean.Candidates.MeasuredPolicy20261027.selected_policy_reads_numeric_bounds_and_permission
#check JurisLean.Candidates.MeasuredPolicy20261027.supported_scores_are_bounded
#print axioms JurisLean.Candidates.MeasuredPolicy20261027.supported_scores_are_bounded
#check JurisLean.Candidates.MeasuredPolicy20261027.scaled_policy_score_mean
#print axioms JurisLean.Candidates.MeasuredPolicy20261027.scaled_policy_score_mean
#check JurisLean.Candidates.MeasuredPolicy20261027.actual_policy_advice_confidence
#print axioms JurisLean.Candidates.MeasuredPolicy20261027.actual_policy_advice_confidence
#check JurisLean.Candidates.MeasuredPolicy20261027.advice_consumes_actual_measured_values_and_allowed_policy
#print axioms JurisLean.Candidates.MeasuredPolicy20261027.advice_consumes_actual_measured_values_and_allowed_policy
#check JurisLean.Candidates.MeasuredPolicy20261027.feedback_reads_actual_external_label
#print axioms JurisLean.Candidates.MeasuredPolicy20261027.feedback_reads_actual_external_label
#check JurisLean.Candidates.MeasuredPolicy20261027.measured_feedback_enters_actual_next_learner
#print axioms JurisLean.Candidates.MeasuredPolicy20261027.measured_feedback_enters_actual_next_learner
#check JurisLean.Candidates.MeasuredPolicy20261027.measured_feedback_prepares_from_actual_loaded_and_journal
#print axioms JurisLean.Candidates.MeasuredPolicy20261027.measured_feedback_prepares_from_actual_loaded_and_journal
#check JurisLean.Candidates.MeasuredPolicy20261027.measured_data_update_keeps_rules_loaded_and_budget
#print axioms JurisLean.Candidates.MeasuredPolicy20261027.measured_data_update_keeps_rules_loaded_and_budget

open JurisLean.Candidates.Final20261021
open JurisLean.Candidates.BusinessMeasurement20261027
open JurisLean.Candidates.MeasuredPolicy20261027
open JurisLean.Candidates.LearningERM20261027
open JurisLean.Candidates.EventFeedbackConsumer20261027
open JurisLean.Candidates.ValidatedFeedbackLoad20261027
open JurisLean.Candidates.AdaptiveRoundLedger20261027

namespace MeasuredPolicyFixture

def environment : PolicyEnvironment :=
  ⟨ValidatedFeedbackLoadFixture.scope, intervalDecisionGamma.jurisdiction,
    intervalDecisionGamma.interpretation, 1, 1, 1, 10, "UTC", 1, .procedure⟩

def plan : PolicyPlan :=
  ⟨environment, [1/2, 1/2], [[0, 0], [1, 1]], [0, 0], 2, 1/20, 1/5, 8, 0, ⟨-10⟩⟩

def datum (i : Fin 400) : PolicyDatum 2 :=
  (0, decide (i.val % 2 = 0), decide (i.val % 2 = 0))

def dictionary (id : Nat) : MeasurementDictionary :=
  { procedureDictionary with
    event := ⟨100 + id⟩
    opportunity := id
    unit := ⟨200 + id⟩
    resultRecord := ⟨300 + id⟩
    targetVersion := 2 }

def treatment (id : Nat) : TreatmentRecord 2 :=
  ⟨environment, dictionary id, 0, ⟨-2⟩, ⟨40⟩, decide (id % 2 = 0), ⟨-1⟩, ⟨50⟩, ⟨60⟩⟩

-- Every synthetic row is produced by the actual empty trajectory -> complete
-- window measurement -> treatment binding. A repeated case would not prove iid.
def produced (id : Nat) : MeasuredPolicyRun 2 :=
  let d := dictionary id
  let raw := [measurementStamp d (500 + id) 1
    (.procedureChoice ⟨8⟩ (if id % 2 = 0 then 4 else 5))]
  runMeasurementPolicy [] trajectoryOpening [] d ⟨20⟩ (attestRows raw) (closeWindow d raw)
    raw environment (treatment id) [treatment id]

def observations : List (PolicyObservation 2) :=
  (List.range 400).filterMap fun id => match (produced id).observation with
    | .known out => some out
    | _ => none

def design : PolicyDesignReceipt 2 :=
  ⟨plan, observations, ⟨20⟩, ⟨70⟩, ⟨71⟩, ⟨72⟩, ⟨73⟩, ⟨74⟩⟩

def permission : PolicyPermission := ⟨intervalDecisionGamma, environment, [[0, 0], [1, 1]], ⟨80⟩⟩

def advice : Result (PolicyAdvice 2) :=
  adviseMeasured intervalDecisionGamma plan observations design [design] permission [permission]

/-- info: true -/
#guard_msgs in
#eval decide (policyClassSupported 2 plan = true ∧ policyNumericsValid 2 400 plan = true ∧
  empiricalScore (policyScore plan.logging) datum [0, 0] = 0 ∧
  empiricalScore (policyScore plan.logging) datum [1, 1] = 1 ∧
  choosePolicy plan datum permission.policies = some [1, 1])

/-- info: true -/
#guard_msgs in
#eval decide (choosePolicy plan datum [[0, 0]] = none)

/-- info: true -/
#guard_msgs in
#eval decide (choosePolicy {plan with logging := [0, 1/2]} datum permission.policies = none)

/-- info: true -/
#guard_msgs in
#eval decide (choosePolicy {plan with radius := 1/100} datum permission.policies = none)

/-- info: true -/
#guard_msgs in
#eval decide (choosePolicy {plan with family := [[1, 1]]} datum permission.policies = none)

/-- info: true -/
#guard_msgs in
#eval
  match (produced 0).observation with
  | .known row => decide (observationDatum row = ((0 : Fin 2), true, true) ∧
      row.measured.dictionary.event = ⟨100⟩ ∧ row.measured.actualPost = trajectoryOpening)
  | _ => false

/-- info: true -/
#guard_msgs in
#eval
  match advice with
  | .known out => decide (observations.length = 400 ∧ out.oldEstimate = 0 ∧ out.newEstimate = 1 ∧
      out.chosen = [1, 1] ∧ out.observations = observations ∧ out.permitted = permission)
  | _ => false

/-- info: true -/
#guard_msgs in
#eval decide (adviseMeasured intervalDecisionGamma plan observations design [] permission [permission] =
  .unknown .notIdentified)

/-- info: true -/
#guard_msgs in
#eval decide (adviseMeasured intervalDecisionGamma plan observations design [design] permission [] =
  .unknown .authorityUnresolved)

/-- info: true -/
#guard_msgs in
#eval decide (adviseMeasured {intervalDecisionGamma with mechanismVersion := 99}
  plan observations design [design] permission [permission] = .unknown .scopeMismatch)

/-- info: true -/
#guard_msgs in
#eval
  match (produced 0).observation with
  | .known row => decide (adviseMeasured intervalDecisionGamma plan [row, row] design [design]
      permission [permission] = .unknown .scopeMismatch)
  | _ => false

/-- info: true -/
#guard_msgs in
#eval
  let afterTreatment := {treatment 0 with baselineAt := ⟨0⟩}
  decide (consumeMeasurement environment (produced 0).business.measurement
    afterTreatment [afterTreatment] = .unknown .scopeMismatch)

/-- info: true -/
#guard_msgs in
#eval decide (consumeMeasurement environment (.unknown .unknownCommit) (treatment 0) [treatment 0] =
  .unknown .missingEvidence)

def feedbackCheck (confirmed : Bool) (f : RoundState 2 → RoundState 2 → PolicyObservation 2 → Bool) : Bool :=
  match (produced 0).observation, ValidatedFeedbackLoadFixture.built with
  | .known row, .known (service, _) =>
      let state := AdaptiveRoundLedgerFixture.base {service with
        gamma := row.measured.actualPost.gamma
        journal := {service.journal with confirmations :=
          (if confirmed then [⟨measuredFeedback row, ⟨90⟩⟩] else []) ++ service.journal.confirmations}}
      let out := beginMeasuredRound state ⟨20⟩ row [] ValidatedFeedbackLoadFixture.protocol
        ValidatedFeedbackLoadFixture.plan
      f state out row
  | _, _ => false

/-- info: true -/
#guard_msgs in
#eval feedbackCheck true (fun before after row =>
  decide (after.pending.isSome ∧ after.service.gamma = before.service.gamma ∧
    after.service.loaded = before.service.loaded ∧ after.records = before.records ∧
    (lookup after.service.journal row.measured.dictionary.event).map (fun c => c.state) =
      some (.active row.treatment.feature row.measured.label)))

/-- info: true -/
#guard_msgs in
#eval feedbackCheck true (fun before after _ =>
  match after.pending with
  | some pending => decide (pending.prepared.parent = before.service.loaded ∧
      pending.prepared.post.journal = after.service.journal ∧
      pending.prepared.models = before.service.loaded.fitted.table :: before.learner.proposals ∧
      (trainingRows after.service.journal).length = 3)
  | none => false)

/-- info: true -/
#guard_msgs in
#eval feedbackCheck false (fun before after row =>
  decide (lookup after.service.journal row.measured.dictionary.event = none ∧
    after.service.journal = before.service.journal ∧ after.service.loaded = before.service.loaded))

end MeasuredPolicyFixture
