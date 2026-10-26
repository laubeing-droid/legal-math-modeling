import JurisLean.Candidates.SampleCalibrationConsumer20261027

#check JurisLean.Candidates.SampleCalibrationConsumer20261027.event_guard_uses_real_identity
#print axioms JurisLean.Candidates.SampleCalibrationConsumer20261027.event_guard_uses_real_identity
#check JurisLean.Candidates.SampleCalibrationConsumer20261027.changed_sample_scope_refused
#print axioms JurisLean.Candidates.SampleCalibrationConsumer20261027.changed_sample_scope_refused
#check JurisLean.Candidates.SampleCalibrationConsumer20261027.actual_sample_produces_the_certificate
#print axioms JurisLean.Candidates.SampleCalibrationConsumer20261027.actual_sample_produces_the_certificate
#check JurisLean.Candidates.SampleCalibrationConsumer20261027.query_outside_selected_rule_refused
#print axioms JurisLean.Candidates.SampleCalibrationConsumer20261027.query_outside_selected_rule_refused
#check JurisLean.Candidates.SampleCalibrationConsumer20261027.prediction_reads_actual_fitted_table
#print axioms JurisLean.Candidates.SampleCalibrationConsumer20261027.prediction_reads_actual_fitted_table
#check JurisLean.Candidates.SampleCalibrationConsumer20261027.pipeline_consumes_the_actual_empirical_minimizer
#print axioms JurisLean.Candidates.SampleCalibrationConsumer20261027.pipeline_consumes_the_actual_empirical_minimizer
#check JurisLean.Candidates.SampleCalibrationConsumer20261027.actual_certificate_consumes_population_risk_bound
#print axioms JurisLean.Candidates.SampleCalibrationConsumer20261027.actual_certificate_consumes_population_risk_bound
#check JurisLean.Candidates.SampleCalibrationConsumer20261027.whole_pipeline_joint_family_risk_bound
#print axioms JurisLean.Candidates.SampleCalibrationConsumer20261027.whole_pipeline_joint_family_risk_bound

#check JurisLean.Candidates.SampleCalibrationConsumer20261027.radius_verification_sound
#print axioms JurisLean.Candidates.SampleCalibrationConsumer20261027.radius_verification_sound
#check JurisLean.Candidates.SampleCalibrationConsumer20261027.pipeline_checks_joint_radius
#print axioms JurisLean.Candidates.SampleCalibrationConsumer20261027.pipeline_checks_joint_radius

open JurisLean.Candidates.Final20261021
open JurisLean.Candidates.LearningConsumer20261027
open JurisLean.Candidates.SampleCalibrationConsumer20261027

def sampleFixtureProtocol : LearningProtocol :=
  ⟨⟨1, 2, 3, 4, 5, ⟨10⟩, ⟨99⟩⟩, 6, 7, 8, 9, 10, 11, 12, 1/10⟩

def sampleFixtureLoss (score : ℚ) (label : Bool) : ℚ :=
  if (score = 1 ↔ label = true) then 0 else 1

def trainingFixture : Fin 2 → SampleObservation 1 Bool :=
  fun i => ⟨⟨i.val⟩, 0, true⟩

def calibrationFixture : Fin 4000 → SampleObservation 1 Bool :=
  fun i => ⟨⟨i.val + 2⟩, 0, true⟩

def sampleFixtureRun : Result (SampleCalibration × TaskScore) :=
  runSamples sampleFixtureProtocol sampleFixtureProtocol sampleFixtureLoss [[0], [1]] [0, 1]
    trainingFixture calibrationFixture 0 (1/10) (1/4) 100 101 8 true

/-- info: true -/
#guard_msgs in
#eval (match sampleFixtureRun with
  | .known out => decide (out.1.fitted.table = [1] ∧ out.2.value = 1 ∧
      out.1.calibrationRows = 4000 ∧ out.2.bounds.lowerCoverage = 9/10 ∧
      out.2.bounds.upperRisk = 1/9)
  | _ => false)

/-- info: true -/
#guard_msgs in
#eval decide (runSamples sampleFixtureProtocol sampleFixtureProtocol sampleFixtureLoss
  [[0], [1]] [0, 1] trainingFixture (fun _ : Fin 2 => ⟨⟨0⟩, 0, true⟩)
  0 (1/10) (1/4) 100 101 8 true = .unknown .scopeMismatch)

/-- info: true -/
#guard_msgs in
#eval decide (runSamples sampleFixtureProtocol sampleFixtureProtocol sampleFixtureLoss
  [[0], [1]] [0, 1] trainingFixture (fun _ : Fin 2 => ⟨⟨100⟩, 0, true⟩)
  0 (1/10) (1/4) 100 101 8 true = .unknown .scopeMismatch)

/-- info: true -/
#guard_msgs in
#eval decide (produceCalibration {sampleFixtureProtocol with labelVersion := 99}
  ⟨sampleFixtureProtocol, [1], 2, 0⟩ sampleFixtureLoss [0, 1]
  calibrationFixture (1/10) (1/4) 100 101 8 = .unknown .targetMismatch)

/-- info: true -/
#guard_msgs in
#eval decide (runSamples sampleFixtureProtocol sampleFixtureProtocol sampleFixtureLoss [[0], [1]] [0, 1]
  trainingFixture (fun i : Fin 4000 => {calibrationFixture i with label := false})
  0 (1/10) (1/4) 100 101 8 true = .unknown .missingEvidence)

/-- info: true -/
#guard_msgs in
#eval (match runSamples sampleFixtureProtocol sampleFixtureProtocol sampleFixtureLoss [[0], [1]] [0, 1]
  (fun i : Fin 2 => {trainingFixture i with label := false})
  (fun i : Fin 4000 => {calibrationFixture i with label := false}) 0 (1/10) (1/4) 100 101 8 true with
  | .known out => decide (out.1.fitted.table = [0] ∧ out.2.value = 0 ∧ out.2.bounds.upperRisk = 1/9)
  | _ => false)

-- Zero radius cannot be certified, even with zero observed loss.
/-- info: true -/
#guard_msgs in
#eval decide (runSamples sampleFixtureProtocol sampleFixtureProtocol sampleFixtureLoss [[0], [1]] [0, 1]
  trainingFixture calibrationFixture 0 0 (1/4) 100 101 8 true = .unknown .missingEvidence)

-- Exponent 7 pays for two cutoffs at one model, but not the full 2x2 family.
/-- info: true -/
#guard_msgs in
#eval decide (radiusVerified 4000 2 (1/10) (1/10) 7 = true ∧
  runSamples sampleFixtureProtocol sampleFixtureProtocol sampleFixtureLoss [[0], [1]] [0, 1]
    trainingFixture calibrationFixture 0 (1/10) (1/4) 100 101 7 true = .unknown .missingEvidence)
