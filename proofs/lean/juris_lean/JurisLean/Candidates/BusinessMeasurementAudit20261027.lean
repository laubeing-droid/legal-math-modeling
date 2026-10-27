import JurisLean.Candidates.BusinessMeasurement20261027
import JurisLean.Candidates.DecisionTrajectoryConsumerAudit20261027

#check JurisLean.Candidates.BusinessMeasurement20261027.measurement_reads_actual_state_and_rows
#print axioms JurisLean.Candidates.BusinessMeasurement20261027.measurement_reads_actual_state_and_rows
#check JurisLean.Candidates.BusinessMeasurement20261027.negative_requires_complete_closed_window
#print axioms JurisLean.Candidates.BusinessMeasurement20261027.negative_requires_complete_closed_window
#check JurisLean.Candidates.BusinessMeasurement20261027.duplicate_events_refused
#print axioms JurisLean.Candidates.BusinessMeasurement20261027.duplicate_events_refused
#check JurisLean.Candidates.BusinessMeasurement20261027.accepted_rows_are_external_and_current
#print axioms JurisLean.Candidates.BusinessMeasurement20261027.accepted_rows_are_external_and_current
#check JurisLean.Candidates.BusinessMeasurement20261027.positive_means_actual_total_reaches_threshold
#print axioms JurisLean.Candidates.BusinessMeasurement20261027.positive_means_actual_total_reaches_threshold
#check JurisLean.Candidates.BusinessMeasurement20261027.revocation_does_not_supply_defect_measurement
#print axioms JurisLean.Candidates.BusinessMeasurement20261027.revocation_does_not_supply_defect_measurement
#check JurisLean.Candidates.BusinessMeasurement20261027.missing_payment_receipt_cannot_measure_performance
#print axioms JurisLean.Candidates.BusinessMeasurement20261027.missing_payment_receipt_cannot_measure_performance
#check JurisLean.Candidates.BusinessMeasurement20261027.performance_magnitude_is_actual_allocation
#print axioms JurisLean.Candidates.BusinessMeasurement20261027.performance_magnitude_is_actual_allocation
#check JurisLean.Candidates.BusinessMeasurement20261027.trajectory_measurement_uses_reported_post
#print axioms JurisLean.Candidates.BusinessMeasurement20261027.trajectory_measurement_uses_reported_post
#check JurisLean.Candidates.BusinessMeasurement20261027.unknown_commit_has_no_behavior_label
#print axioms JurisLean.Candidates.BusinessMeasurement20261027.unknown_commit_has_no_behavior_label
#check JurisLean.Candidates.BusinessMeasurement20261027.accepted_measurement_keeps_actual_trace_invariant
#print axioms JurisLean.Candidates.BusinessMeasurement20261027.accepted_measurement_keeps_actual_trace_invariant
#check JurisLean.Candidates.BusinessMeasurement20261027.original_appeal_frequencies
#print axioms JurisLean.Candidates.BusinessMeasurement20261027.original_appeal_frequencies
#check JurisLean.Candidates.BusinessMeasurement20261027.unknown_appeal_labels_have_sharp_bounds
#print axioms JurisLean.Candidates.BusinessMeasurement20261027.unknown_appeal_labels_have_sharp_bounds
#check JurisLean.Candidates.BusinessMeasurement20261027.appeal_observations_cannot_identify_population_rate
#print axioms JurisLean.Candidates.BusinessMeasurement20261027.appeal_observations_cannot_identify_population_rate

open JurisLean.Candidates.Final20261021
open JurisLean.Candidates.DecisionTrajectoryConsumer20261027
open JurisLean.Candidates.BusinessMeasurement20261027

def performanceDictionary : MeasurementDictionary :=
  { context := intervalDecisionGamma
    stage := 1
    opportunity := 1
    event := ⟨100⟩
    unit := ⟨200⟩
    resultRecord := ⟨300⟩
    targetVersion := 1
    windowStart := ⟨0⟩
    windowEnd := ⟨10⟩
    timezone := "UTC"
    clockVersion := 1
    construct := .timelyPerformance trajectoryDebt.relation trajectoryDebt.obligor
      trajectoryDebt.creditor trajectoryDebt.amount }

def measurementStamp (d : MeasurementDictionary) (key : Nat) (time : Int)
    (body : BehaviorRecord) : MeasurementRow :=
  ⟨d, ⟨key⟩, ⟨1000 + key⟩, ⟨time⟩, ⟨time⟩, ⟨key⟩, body⟩

def performanceRowOne : MeasurementRow := measurementStamp performanceDictionary 1 1 (.payment ⟨1⟩)
def performanceRowTwo : MeasurementRow := measurementStamp performanceDictionary 2 2 (.payment ⟨2⟩)
def performanceRows : List MeasurementRow := [performanceRowOne, performanceRowTwo]

def attestRows (rows : List MeasurementRow) : List ObservationAttestation :=
  rows.map fun row => ⟨row, ⟨900⟩⟩

def closeWindow (d : MeasurementDictionary) (rows : List MeasurementRow) : List WindowClosure :=
  [⟨d, rows, ⟨20⟩, ⟨901⟩⟩]

def performanceFixture (steps : List Instruction) (rows : List MeasurementRow)
    (now : Int) (closed : Bool) : MeasuredTrajectory :=
  measureTrajectory trajectoryGrants trajectoryOpening steps performanceDictionary ⟨now⟩
    (attestRows rows) (if closed then closeWindow performanceDictionary rows else []) rows

def measurementHas (result : MeasurementResult) (label : Bool) (total : ℚ) : Bool :=
  match result with
  | .measured receipt => decide (receipt.label = label ∧ receipt.measuredTotal = total)
  | _ => false

/-- info: true -/
#guard_msgs in
#eval
  let out := performanceFixture trajectorySteps performanceRows 3 false
  match out.measurement with
  | .measured m => decide (m.label = true ∧ m.measuredTotal = 10 ∧
      m.actualPost.state.paid = 14 ∧ m.actualPost.state.surplus = 4 ∧
      out.trajectory.current = some m.actualPost)
  | _ => false

/-- info: true -/
#guard_msgs in
#eval measurementHas (performanceFixture
  (trajectorySteps ++ [.pay (trajectoryRequest 1) .submit]) performanceRows 3 false).measurement true 10

/-- info: true -/
#guard_msgs in
#eval decide ((performanceFixture [.pay (trajectoryRequest 1) .submit]
  [performanceRowOne] 3 false).measurement = .unknown .incompleteWindow)

/-- info: true -/
#guard_msgs in
#eval measurementHas (performanceFixture [.pay (trajectoryRequest 1) .submit]
  [performanceRowOne] 20 true).measurement false 7

/-- info: true -/
#guard_msgs in
#eval decide ((performanceFixture [.pay (trajectoryRequest 1) .submit,
  .pay (trajectoryRequest 2) .unknownCommit] performanceRows 20 true).measurement = .unknown .unknownCommit)

/-- info: true -/
#guard_msgs in
#eval
  let duplicate := {performanceRowOne with record := ⟨5000⟩}
  decide ((performanceFixture [.pay (trajectoryRequest 1) .submit]
    [performanceRowOne, duplicate] 20 true).measurement = .unknown .scopeMismatch)

/-- info: true -/
#guard_msgs in
#eval decide ((performanceFixture [] performanceRows 20 true).measurement = .unknown .measurementBridgeMissing)

/-- info: true -/
#guard_msgs in
#eval
  let late := [{performanceRowOne with occurredAt := ⟨11⟩, recordedAt := ⟨11⟩}, performanceRowTwo]
  measurementHas (performanceFixture trajectorySteps late 20 true).measurement false 3

/-- info: true -/
#guard_msgs in
#eval
  let wrong := [{performanceRowOne with source := ⟨999⟩}, performanceRowTwo]
  decide ((performanceFixture trajectorySteps wrong 20 true).measurement = .unknown .measurementBridgeMissing)

def procedureDictionary : MeasurementDictionary :=
  { performanceDictionary with construct := .procedureChoice ⟨8⟩ 4 }

def simpleMeasurement (d : MeasurementDictionary) (body : BehaviorRecord) (time now : Int)
    (closed : Bool := false) : MeasurementResult :=
  let rows := [measurementStamp d 10 time body]
  measureBusiness trajectoryOpening d ⟨now⟩ (attestRows rows)
    (if closed then closeWindow d rows else []) rows

/-- info: true -/
#guard_msgs in
#eval measurementHas (simpleMeasurement procedureDictionary (.procedureChoice ⟨8⟩ 4) 1 3) true 1

/-- info: true -/
#guard_msgs in
#eval measurementHas (simpleMeasurement procedureDictionary (.procedureChoice ⟨8⟩ 5) 1 20 true) false 0

/-- info: true -/
#guard_msgs in
#eval decide (simpleMeasurement procedureDictionary (.procedureChoice ⟨9⟩ 4) 1 3 =
  .unknown .measurementBridgeMissing)

/-- info: true -/
#guard_msgs in
#eval measurementHas (simpleMeasurement {performanceDictionary with construct := .timelyFiling ⟨8⟩}
  (.filing ⟨8⟩) 10 10) true 1

/-- info: true -/
#guard_msgs in
#eval measurementHas (simpleMeasurement {performanceDictionary with construct := .timelyFiling ⟨8⟩}
  (.filing ⟨8⟩) 11 20 true) false 0

/-- info: true -/
#guard_msgs in
#eval decide (simpleMeasurement {performanceDictionary with construct := .reviewedDefect}
  .revocation 1 20 true = .unknown .measurementBridgeMissing)

/-- info: true -/
#guard_msgs in
#eval measurementHas (simpleMeasurement {performanceDictionary with construct := .reviewedDefect}
  (.reviewedFinding true ⟨55⟩) 1 3) true 1

/-- info: true -/
#guard_msgs in
#eval
  let d := {performanceDictionary with context := {intervalDecisionGamma with caseId := ⟨99⟩}}
  decide (simpleMeasurement d (.payment ⟨1⟩) 1 3 = .unknown .scopeMismatch)

/-- info: true -/
#guard_msgs in
#eval decide (appealCompletionRate 2 = 1/10 ∧ appealCompletionRate 0 = 2/25 ∧
  appealCompletionRate 80 = 22/25)
