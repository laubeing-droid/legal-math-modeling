import JurisLean.Candidates.IntervalDecisionConsumer20261027
import JurisLean.Candidates.ProbabilityIntervalConsumerAudit20261027

#check JurisLean.Candidates.IntervalDecisionConsumer20261027.actual_probability_fills_both_outcomes
#print axioms JurisLean.Candidates.IntervalDecisionConsumer20261027.actual_probability_fills_both_outcomes
#check JurisLean.Candidates.IntervalDecisionConsumer20261027.binary_evaluation_uses_exact_amount_and_one_cost
#print axioms JurisLean.Candidates.IntervalDecisionConsumer20261027.binary_evaluation_uses_exact_amount_and_one_cost
#check JurisLean.Candidates.IntervalDecisionConsumer20261027.affine_interval_bounds
#print axioms JurisLean.Candidates.IntervalDecisionConsumer20261027.affine_interval_bounds
#check JurisLean.Candidates.IntervalDecisionConsumer20261027.interval_evaluation_reads_the_receipt
#print axioms JurisLean.Candidates.IntervalDecisionConsumer20261027.interval_evaluation_reads_the_receipt
#check JurisLean.Candidates.IntervalDecisionConsumer20261027.computed_decision_encloses_cash_utility_and_risk
#print axioms JurisLean.Candidates.IntervalDecisionConsumer20261027.computed_decision_encloses_cash_utility_and_risk
#check JurisLean.Candidates.IntervalDecisionConsumer20261027.missing_identification_cannot_succeed
#print axioms JurisLean.Candidates.IntervalDecisionConsumer20261027.missing_identification_cannot_succeed
#check JurisLean.Candidates.IntervalDecisionConsumer20261027.fit_to_decision_passes_the_actual_probability
#print axioms JurisLean.Candidates.IntervalDecisionConsumer20261027.fit_to_decision_passes_the_actual_probability
#check JurisLean.Candidates.IntervalDecisionConsumer20261027.explicit_maximin_preserves_permission_and_risk
#print axioms JurisLean.Candidates.IntervalDecisionConsumer20261027.explicit_maximin_preserves_permission_and_risk

open JurisLean.Candidates.Final20261021
open JurisLean.Candidates.Final20261021.Decision
open JurisLean.Candidates.LearningConsumer20261027
open JurisLean.Candidates.SampleCalibrationConsumer20261027
open JurisLean.Candidates.ProbabilityIntervalConsumer20261027
open JurisLean.Candidates.IntervalDecisionConsumer20261027

def intervalDecisionGamma : Gamma :=
  ⟨⟨1⟩, 0, 5, "synthetic", 1, 1, 1, ⟨0⟩, ⟨10⟩, ⟨10⟩, 1, 1, 1⟩

def intervalDecisionRequest : DecisionRequest 2 :=
  ⟨intervalDecisionGamma, probabilityFixtureProtocol, 1, 100, 1, 1/10⟩

def intervalDecisionTag : AmountTag := ⟨"CNY", "yuan", 1⟩

def riskyQuote : BinaryQuote :=
  { gamma := intervalDecisionGamma, id := 1, conditions := [⟨1⟩], causalBridge := some ⟨2⟩
    success := ledgerAmount ⟨11, intervalDecisionTag⟩
    failure := ledgerAmount ⟨-1, intervalDecisionTag⟩
    successEvents := [⟨10⟩], failureEvents := [⟨11⟩]
    cost := ⟨0, intervalDecisionTag⟩, execution := [] }

def settlementQuote : BinaryQuote :=
  { riskyQuote with id := 2, success := ledgerAmount ⟨4, intervalDecisionTag⟩
    failure := ledgerAmount ⟨4, intervalDecisionTag⟩ }

def actualDecisionFixture (a : BinaryQuote) : Result (IntervalDecision 2) :=
  fitToDecision intervalDecisionRequest probabilityFixtureProtocol probabilityFixtureLoss [[0, 1], [0, 0]]
    (fun i => {probabilityTraining i with label := false}) probabilityCalibration (1/10) 8 true id a

/-- info: true -/
#guard_msgs in
#eval (match actualDecisionFixture riskyQuote with
  | .known out => decide (out.probability.fitted.table = [0, 0] ∧ out.probability.estimate = 1/2 ∧
      out.nominal.expectedNet.value = 5 ∧ out.nominal.expectedUtility = 5 ∧
      out.nominal.probabilityOfLoss = 1/2 ∧ out.netLower = 37/11 ∧ out.netUpper = 7 ∧
      out.riskUpper = 7/11)
  | _ => false)

/-- info: true -/
#guard_msgs in
#eval (match actualDecisionFixture riskyQuote, actualDecisionFixture settlementQuote with
  | .known risky, .known settlement =>
      decide (chooseMaximin intervalDecisionGamma 1 (1/10) [1, 2] [risky, settlement] = some settlement ∧
        chooseMaximin intervalDecisionGamma 1 (1/10) [1] [risky, settlement] = none)
  | _, _ => false)

-- Costs are deducted once; they do not change the probability receipt.
/-- info: true -/
#guard_msgs in
#eval (match actualDecisionFixture {riskyQuote with cost := ⟨1, intervalDecisionTag⟩} with
  | .known out => decide (out.probability.estimate = 1/2 ∧ out.nominal.expectedNet.value = 4 ∧
      out.netLower = 26/11 ∧ out.netUpper = 6)
  | _ => false)

/-- info: true -/
#guard_msgs in
#eval decide (actualDecisionFixture {riskyQuote with causalBridge := none} = .unknown .notIdentified)

/-- info: true -/
#guard_msgs in
#eval decide (actualDecisionFixture {riskyQuote with
  failure := ledgerAmount ⟨-1, ⟨"USD", "yuan", 1⟩⟩} = .rejected .mixedCurrency)

/-- info: true -/
#guard_msgs in
#eval decide (actualDecisionFixture {riskyQuote with successEvents := [⟨10⟩, ⟨10⟩]} = .rejected .duplicateCash)

/-- info: true -/
#guard_msgs in
#eval decide (actualDecisionFixture {riskyQuote with gamma := {intervalDecisionGamma with caseId := ⟨2⟩}} =
  .unknown .scopeMismatch)

/-- info: true -/
#guard_msgs in
#eval (match probabilityFixture 1 with
  | .known p => decide (evaluateInterval {intervalDecisionRequest with query := 0} id p riskyQuote =
      .unknown .targetMismatch)
  | _ => false)

/-- info: true -/
#guard_msgs in
#eval (match probabilityFixture 1 with
  | .known p =>
      let earlier := {intervalDecisionGamma with knowledgeCutoff := ⟨9⟩}
      decide (evaluateInterval {intervalDecisionRequest with gamma := earlier} id p
        {riskyQuote with gamma := earlier} = .unknown .scopeMismatch)
  | _ => false)

/-- info: true -/
#guard_msgs in
#eval (match probabilityFixture 1 with
  | .known p => decide (evaluateInterval {intervalDecisionRequest with calibrationSnapshot := 101}
      id p riskyQuote = .unknown .targetMismatch)
  | _ => false)
