import JurisLean.Candidates.ProbabilityIntervalConsumer20261027

#check JurisLean.Candidates.ProbabilityIntervalConsumer20261027.actual_fitted_score_selects_the_bin
#print axioms JurisLean.Candidates.ProbabilityIntervalConsumer20261027.actual_fitted_score_selects_the_bin
#check JurisLean.Candidates.ProbabilityIntervalConsumer20261027.full_model_bin_family_is_counted
#print axioms JurisLean.Candidates.ProbabilityIntervalConsumer20261027.full_model_bin_family_is_counted
#check JurisLean.Candidates.ProbabilityIntervalConsumer20261027.changed_probability_scope_refused
#print axioms JurisLean.Candidates.ProbabilityIntervalConsumer20261027.changed_probability_scope_refused
#check JurisLean.Candidates.ProbabilityIntervalConsumer20261027.actual_samples_determine_probability
#print axioms JurisLean.Candidates.ProbabilityIntervalConsumer20261027.actual_samples_determine_probability
#check JurisLean.Candidates.ProbabilityIntervalConsumer20261027.empirical_success_bounded_by_coverage
#print axioms JurisLean.Candidates.ProbabilityIntervalConsumer20261027.empirical_success_bounded_by_coverage
#check JurisLean.Candidates.ProbabilityIntervalConsumer20261027.actual_interval_contains_empirical_probability
#print axioms JurisLean.Candidates.ProbabilityIntervalConsumer20261027.actual_interval_contains_empirical_probability
#check JurisLean.Candidates.ProbabilityIntervalConsumer20261027.pipeline_consumes_actual_fit_and_sample
#print axioms JurisLean.Candidates.ProbabilityIntervalConsumer20261027.pipeline_consumes_actual_fit_and_sample
#check JurisLean.Candidates.ProbabilityIntervalConsumer20261027.population_bin_integrals
#print axioms JurisLean.Candidates.ProbabilityIntervalConsumer20261027.population_bin_integrals
#check JurisLean.Candidates.ProbabilityIntervalConsumer20261027.whole_pipeline_bin_probability_confidence
#print axioms JurisLean.Candidates.ProbabilityIntervalConsumer20261027.whole_pipeline_bin_probability_confidence

open JurisLean.Candidates.Final20261021
open JurisLean.Candidates.LearningConsumer20261027
open JurisLean.Candidates.SampleCalibrationConsumer20261027
open JurisLean.Candidates.ProbabilityIntervalConsumer20261027

def probabilityFixtureProtocol : LearningProtocol :=
  ⟨⟨1, 2, 3, 4, 5, ⟨10⟩, ⟨99⟩⟩, 6, 7, 8, 9, 10, 11, 12, 1/10⟩

def probabilityFixtureLoss (score : ℚ) (label : Bool) : ℚ :=
  (score - if label then 1 else 0) ^ 2

def probabilityTraining : Fin 2 → SampleObservation 2 Bool :=
  fun i => ⟨⟨i.val⟩, i, decide (i.val = 1)⟩

def probabilityCalibration : Fin 4000 → SampleObservation 2 Bool :=
  fun i => ⟨⟨i.val + 2⟩, if i.val < 2000 then 0 else 1, decide (2000 ≤ i.val)⟩

def probabilityFixture (query : Fin 2) : Result (SampleProbability 2) :=
  runProbability probabilityFixtureProtocol probabilityFixtureProtocol probabilityFixtureLoss
    [[0, 1], [0, 0]] probabilityTraining probabilityCalibration query (1/10) 8 100 true

/-- info: true -/
#guard_msgs in
#eval (match probabilityFixture 1 with
  | .known out => decide (out.fitted.table = [0, 1] ∧ out.query = 1 ∧
      out.coverage = 1/2 ∧ out.successMass = 1/2 ∧ out.estimate = 1 ∧
      out.lower = 2/3 ∧ out.upper = 1)
  | _ => false)

/-- info: true -/
#guard_msgs in
#eval (match probabilityFixture 0 with
  | .known out => decide (out.coverage = 1/2 ∧ out.successMass = 0 ∧
      out.estimate = 0 ∧ out.lower = 0 ∧ out.upper = 1/4)
  | _ => false)

-- Changing the actual training labels changes the fitted table and score bin.
/-- info: true -/
#guard_msgs in
#eval (match runProbability probabilityFixtureProtocol probabilityFixtureProtocol probabilityFixtureLoss
  [[0, 1], [0, 0]] (fun i => {probabilityTraining i with label := false})
  probabilityCalibration 1 (1/10) 8 100 true with
  | .known out => decide (out.fitted.table = [0, 0] ∧ out.coverage = 1 ∧
      out.successMass = 1/2 ∧ out.estimate = 1/2 ∧ out.lower = 4/11 ∧ out.upper = 2/3)
  | _ => false)

/-- info: true -/
#guard_msgs in
#eval decide (runProbability probabilityFixtureProtocol probabilityFixtureProtocol probabilityFixtureLoss
  [[0, 1], [0, 0]] probabilityTraining (fun i => {probabilityCalibration i with feature := 0})
  1 (1/10) 8 100 true = .unknown .missingEvidence)

/-- info: true -/
#guard_msgs in
#eval decide (runProbability probabilityFixtureProtocol {probabilityFixtureProtocol with labelVersion := 99}
  probabilityFixtureLoss [[0, 1], [0, 0]] probabilityTraining probabilityCalibration
  1 (1/10) 8 100 true = .unknown .targetMismatch)

/-- info: true -/
#guard_msgs in
#eval decide (runProbability probabilityFixtureProtocol probabilityFixtureProtocol probabilityFixtureLoss
  [[0, 1], [0, 0]] probabilityTraining probabilityCalibration
  1 (1/10) 8 100 false = .unknown .unsupported)

/-- info: true -/
#guard_msgs in
#eval decide (radiusVerified 4000 2 (1/10) (1/10) 7 = true ∧
  runProbability probabilityFixtureProtocol probabilityFixtureProtocol probabilityFixtureLoss
    [[0, 1], [0, 0]] probabilityTraining probabilityCalibration
    1 (1/10) 7 100 true = .unknown .missingEvidence)

/-- info: true -/
#guard_msgs in
#eval decide (runProbability probabilityFixtureProtocol probabilityFixtureProtocol probabilityFixtureLoss
  [[0, 1], [0, 0]] probabilityTraining (fun i => {probabilityCalibration i with event := ⟨0⟩})
  1 (1/10) 8 100 true = .unknown .scopeMismatch)
