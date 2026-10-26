import JurisLean.Candidates.ProbabilityIntervalConsumer20261027
import JurisLean.Candidates.Final20261021.Decision

/-!
Original 06 and the numerical 04/05 -> 06 edge. Binary alternatives have exact
payoffs and a once-only cost, but no separately supplied probability. Evaluation
reads the actual probability receipt and propagates its interval to cash, utility
and loss risk. Maximin selection is an explicitly named caller-chosen criterion.

A score-bin observational probability is not automatically an action's outcome
law. The causal/source reference remains a named external identification premise;
checking its presence does not prove it. The bounds below quantify over any
outcome probability in the supplied interval. Legal permission and the chosen
utility remain external inputs. No weights are assigned to legal branches.
-/

namespace JurisLean.Candidates.IntervalDecisionConsumer20261027

open MeasureTheory ProbabilityTheory
open JurisLean.Candidates.Final20261021
open JurisLean.Candidates.Final20261021.Decision
open JurisLean.Candidates.LearningConsumer20261027
open JurisLean.Candidates.SampleCalibrationConsumer20261027
open JurisLean.Candidates.ProbabilityIntervalConsumer20261027

structure DecisionRequest (m : ℕ) where
  gamma : Gamma
  protocol : LearningProtocol
  query : Fin m
  calibrationSnapshot : ℕ
  utilityVersion : ℕ
  riskLimit : ℚ
  deriving DecidableEq, Repr

structure BinaryQuote where
  gamma : Gamma
  id : ℕ
  conditions : List SourceRef
  causalBridge : Option SourceRef
  success : TypedValue
  failure : TypedValue
  successEvents : List EventId
  failureEvents : List EventId
  cost : Amount
  execution : List PaymentPayload
  deriving DecidableEq, Repr

def BinaryQuote.atProbability (a : BinaryQuote) (p : ℚ) : Alternative :=
  { id := a.id, conditions := a.conditions, causalBridge := a.causalBridge
    outcomes := [⟨p, a.success, a.successEvents⟩, ⟨1 - p, a.failure, a.failureEvents⟩]
    cost := a.cost, execution := a.execution }

def cashAt (a : BinaryQuote) (p : ℚ) : ℚ :=
  p * evalExact a.success.expr + (1 - p) * evalExact a.failure.expr - a.cost.value

def utilityAt (utility : ℚ → ℚ) (a : BinaryQuote) (p : ℚ) : ℚ :=
  p * utility (evalExact a.success.expr - a.cost.value) +
    (1 - p) * utility (evalExact a.failure.expr - a.cost.value)

def lossAt (a : BinaryQuote) (p : ℚ) : ℚ :=
  p * (if evalExact a.success.expr - a.cost.value < 0 then 1 else 0) +
    (1 - p) * (if evalExact a.failure.expr - a.cost.value < 0 then 1 else 0)

structure IntervalDecision (m : ℕ) where
  probability : SampleProbability m
  nominal : DecisionIR
  netLower : ℚ
  netUpper : ℚ
  utilityLower : ℚ
  utilityUpper : ℚ
  riskUpper : ℚ
  deriving DecidableEq, Repr

def evaluateInterval {m : ℕ} (request : DecisionRequest m) (utility : ℚ → ℚ)
    (p : SampleProbability m) (a : BinaryQuote) : Result (IntervalDecision m) :=
  if a.gamma ≠ request.gamma then .unknown .scopeMismatch
  else if p.fitted.protocol ≠ request.protocol ∨ p.query ≠ request.query ∨
      p.snapshot ≠ request.calibrationSnapshot then .unknown .targetMismatch
  else if request.gamma.knowledgeCutoff.ticks < p.fitted.protocol.fit.windowEnd.ticks then
    .unknown .scopeMismatch
  else if ¬ (0 ≤ p.lower ∧ p.lower ≤ p.estimate ∧ p.estimate ≤ p.upper ∧ p.upper ≤ 1) then
    .unknown .missingEvidence
  else
    match evaluate request.gamma utility request.utilityVersion request.riskLimit
      (a.atProbability p.estimate) with
    | .known nominal => .known
        { probability := p, nominal := nominal
          netLower := min (cashAt a p.lower) (cashAt a p.upper)
          netUpper := max (cashAt a p.lower) (cashAt a p.upper)
          utilityLower := min (utilityAt utility a p.lower) (utilityAt utility a p.upper)
          utilityUpper := max (utilityAt utility a p.lower) (utilityAt utility a p.upper)
          riskUpper := max (lossAt a p.lower) (lossAt a p.upper) }
    | .unknown e => .unknown e
    | .rejected e => .rejected e
    | .conflict x y => .conflict x y

def fitToDecision {m n k : ℕ} (request : DecisionRequest m) (sampleProtocol : LearningProtocol)
    (loss : ℚ → Bool → ℚ) (models : List (List ℚ))
    (training : Fin n → SampleObservation m Bool) (calibration : Fin k → SampleObservation m Bool)
    (radius : ℚ) (exponent : ℕ) (supported : Bool) (utility : ℚ → ℚ) (a : BinaryQuote) :
    Result (IntervalDecision m) :=
  match runProbability request.protocol sampleProtocol loss models training calibration
      request.query radius exponent request.calibrationSnapshot supported with
  | .known p => evaluateInterval request utility p a
  | .unknown e => .unknown e
  | .rejected e => .rejected e
  | .conflict x y => .conflict x y

-- This explicitly selects the maximin criterion; it does not make that choice
-- for a caller who has not supplied a preference. Empty feasible lists stay none.
def chooseMaximin {m : ℕ} (g : Gamma) (utilityVersion : ℕ) (riskLimit : ℚ)
    (allowed : List ℕ) (values : List (IntervalDecision m)) : Option (IntervalDecision m) :=
  legalBest (·.utilityLower)
    (fun v => decide (v.nominal.gamma = g ∧ v.nominal.utilityVersion = utilityVersion ∧
      v.nominal.riskLimit = riskLimit ∧ v.nominal.action.id ∈ allowed ∧ v.riskUpper ≤ riskLimit)) values

theorem actual_probability_fills_both_outcomes (a : BinaryQuote) (p : ℚ) :
    (a.atProbability p).outcomes.map (·.probability) = [p, 1 - p] := rfl

theorem binary_evaluation_uses_exact_amount_and_one_cost (g : Gamma) (utility : ℚ → ℚ)
    (utilityVersion : ℕ) (riskLimit : ℚ) (a : BinaryQuote) (p : ℚ) (out : DecisionIR)
    (accepted : evaluate g utility utilityVersion riskLimit (a.atProbability p) = .known out) :
    out.gamma = g ∧ out.action = a.atProbability p ∧
    out.expectedNet.value = cashAt a p ∧ out.expectedUtility = utilityAt utility a p ∧
    out.probabilityOfLoss = lossAt a p := by
  unfold evaluate at accepted
  split at accepted
  · cases accepted
  · split at accepted
    · cases accepted
    · split at accepted
      · cases accepted
      · split at accepted
        · cases accepted
        · split at accepted
          · cases accepted
          · cases accepted
            refine ⟨rfl, rfl, ?_, ?_, ?_⟩
            · simp [BinaryQuote.atProbability, cashAt]
            · simp [BinaryQuote.atProbability, utilityAt]
            · by_cases hs : evalExact a.success.expr < a.cost.value <;>
                by_cases hf : evalExact a.failure.expr < a.cost.value <;>
                simp [BinaryQuote.atProbability, lossAt, sub_neg, hs, hf]

theorem affine_interval_bounds (p lo hi b l k : ℝ) (lower : lo ≤ p) (upper : p ≤ hi) :
    min (lo*b + (1-lo)*l-k) (hi*b + (1-hi)*l-k) ≤ p*b + (1-p)*l-k ∧
    p*b + (1-p)*l-k ≤ max (lo*b + (1-lo)*l-k) (hi*b + (1-hi)*l-k) := by
  by_cases slope : l ≤ b
  · have lowerProduct := mul_nonneg (sub_nonneg.mpr lower) (sub_nonneg.mpr slope)
    have upperProduct := mul_nonneg (sub_nonneg.mpr upper) (sub_nonneg.mpr slope)
    constructor
    · exact le_trans (min_le_left _ _) (by nlinarith)
    · exact le_trans (by nlinarith) (le_max_right _ _)
  · have decreasing : b ≤ l := le_of_not_ge slope
    have lowerProduct := mul_nonneg (sub_nonneg.mpr lower) (sub_nonneg.mpr decreasing)
    have upperProduct := mul_nonneg (sub_nonneg.mpr upper) (sub_nonneg.mpr decreasing)
    constructor
    · exact le_trans (min_le_right _ _) (by nlinarith)
    · exact le_trans (by nlinarith) (le_max_left _ _)

theorem interval_evaluation_reads_the_receipt {m : ℕ} (request : DecisionRequest m)
    (utility : ℚ → ℚ) (p : SampleProbability m) (a : BinaryQuote) (out : IntervalDecision m)
    (accepted : evaluateInterval request utility p a = .known out) :
    out.probability = p ∧
    evaluate request.gamma utility request.utilityVersion request.riskLimit
      (a.atProbability p.estimate) = .known out.nominal ∧
    out.netLower = min (cashAt a p.lower) (cashAt a p.upper) ∧
    out.netUpper = max (cashAt a p.lower) (cashAt a p.upper) ∧
    out.utilityLower = min (utilityAt utility a p.lower) (utilityAt utility a p.upper) ∧
    out.utilityUpper = max (utilityAt utility a p.lower) (utilityAt utility a p.upper) ∧
    out.riskUpper = max (lossAt a p.lower) (lossAt a p.upper) := by
  unfold evaluateInterval at accepted
  split at accepted
  · cases accepted
  · split at accepted
    · cases accepted
    · split at accepted
      · cases accepted
      · split at accepted
        · cases accepted
        · cases evaluated : evaluate request.gamma utility request.utilityVersion request.riskLimit
              (a.atProbability p.estimate) with
          | unknown e => simp [evaluated] at accepted
          | rejected e => simp [evaluated] at accepted
          | conflict x y => simp [evaluated] at accepted
          | known nominal =>
              simp only [evaluated] at accepted
              cases accepted
              exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

-- A statement about every true outcome probability within the confidence
-- interval. Linking an observational bin rate to this outcome is an additional
-- identification premise, never inferred from the presence of a SourceRef.
theorem computed_decision_encloses_cash_utility_and_risk {m : ℕ}
    (request : DecisionRequest m) (utility : ℚ → ℚ) (p : SampleProbability m)
    (a : BinaryQuote) (out : IntervalDecision m)
    (accepted : evaluateInterval request utility p a = .known out)
    (q : ℝ) (lower : (p.lower : ℝ) ≤ q) (upper : q ≤ (p.upper : ℝ)) :
    (out.netLower : ℝ) ≤ q * (evalExact a.success.expr : ℝ) +
        (1-q) * (evalExact a.failure.expr : ℝ) - (a.cost.value : ℝ) ∧
    q * (evalExact a.success.expr : ℝ) + (1-q) * (evalExact a.failure.expr : ℝ) -
        (a.cost.value : ℝ) ≤ (out.netUpper : ℝ) ∧
    (out.utilityLower : ℝ) ≤ q * (utility (evalExact a.success.expr - a.cost.value) : ℝ) +
        (1-q) * (utility (evalExact a.failure.expr - a.cost.value) : ℝ) ∧
    q * (utility (evalExact a.success.expr - a.cost.value) : ℝ) +
        (1-q) * (utility (evalExact a.failure.expr - a.cost.value) : ℝ) ≤ (out.utilityUpper : ℝ) ∧
    q * (if evalExact a.success.expr - a.cost.value < 0 then (1 : ℝ) else 0) +
        (1-q) * (if evalExact a.failure.expr - a.cost.value < 0 then (1 : ℝ) else 0) ≤
      (out.riskUpper : ℝ) := by
  obtain ⟨_, _, nL, nU, uL, uU, rU⟩ := interval_evaluation_reads_the_receipt
    request utility p a out accepted
  have cash := affine_interval_bounds q (p.lower : ℝ) (p.upper : ℝ)
    (evalExact a.success.expr : ℝ) (evalExact a.failure.expr : ℝ) (a.cost.value : ℝ) lower upper
  have util := affine_interval_bounds q (p.lower : ℝ) (p.upper : ℝ)
    (utility (evalExact a.success.expr - a.cost.value) : ℝ)
    (utility (evalExact a.failure.expr - a.cost.value) : ℝ) 0 lower upper
  have risk := affine_interval_bounds q (p.lower : ℝ) (p.upper : ℝ)
    (if evalExact a.success.expr - a.cost.value < 0 then 1 else 0)
    (if evalExact a.failure.expr - a.cost.value < 0 then 1 else 0) 0 lower upper
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simpa [nL, cashAt] using cash.1
  · simpa [nU, cashAt] using cash.2
  · simpa [uL, utilityAt] using util.1
  · simpa [uU, utilityAt] using util.2
  · by_cases hs : evalExact a.success.expr - a.cost.value < 0 <;>
      by_cases hf : evalExact a.failure.expr - a.cost.value < 0 <;>
      simpa [rU, lossAt, hs, hf] using risk.2

theorem missing_identification_cannot_succeed {m : ℕ} (request : DecisionRequest m)
    (utility : ℚ → ℚ) (p : SampleProbability m) (a : BinaryQuote)
    (missing : a.causalBridge = none) (out : IntervalDecision m) :
    evaluateInterval request utility p a ≠ .known out := by
  intro accepted
  have evaluated := (interval_evaluation_reads_the_receipt request utility p a out accepted).2.1
  simp [evaluate, BinaryQuote.atProbability, missing] at evaluated

theorem fit_to_decision_passes_the_actual_probability {m n k : ℕ}
    (request : DecisionRequest m) (sampleProtocol : LearningProtocol) (loss : ℚ → Bool → ℚ)
    (models : List (List ℚ)) (training : Fin n → SampleObservation m Bool)
    (calibration : Fin k → SampleObservation m Bool) (radius : ℚ) (exponent : ℕ)
    (supported : Bool) (utility : ℚ → ℚ) (a : BinaryQuote) (out : IntervalDecision m)
    (accepted : fitToDecision request sampleProtocol loss models training calibration
      radius exponent supported utility a = .known out) :
    ∃ p, runProbability request.protocol sampleProtocol loss models training calibration
        request.query radius exponent request.calibrationSnapshot supported = .known p ∧
      evaluateInterval request utility p a = .known out ∧ out.probability = p := by
  unfold fitToDecision at accepted
  cases predicted : runProbability request.protocol sampleProtocol loss models training calibration
      request.query radius exponent request.calibrationSnapshot supported with
  | unknown e => simp [predicted] at accepted
  | rejected e => simp [predicted] at accepted
  | conflict x y => simp [predicted] at accepted
  | known p =>
      simp only [predicted] at accepted
      exact ⟨p, rfl, accepted, (interval_evaluation_reads_the_receipt request utility p a out accepted).1⟩

theorem explicit_maximin_preserves_permission_and_risk {m : ℕ} (g : Gamma)
    (utilityVersion : ℕ) (riskLimit : ℚ) (allowed : List ℕ)
    (values : List (IntervalDecision m)) (selected : IntervalDecision m)
    (chosen : chooseMaximin g utilityVersion riskLimit allowed values = some selected) :
    selected ∈ values ∧ selected.nominal.gamma = g ∧
    selected.nominal.utilityVersion = utilityVersion ∧ selected.nominal.riskLimit = riskLimit ∧
    selected.nominal.action.id ∈ allowed ∧
    selected.riskUpper ≤ riskLimit ∧
    ∀ other ∈ values, other.nominal.gamma = g → other.nominal.utilityVersion = utilityVersion →
      other.nominal.riskLimit = riskLimit → other.nominal.action.id ∈ allowed → other.riskUpper ≤ riskLimit →
      other.utilityLower ≤ selected.utilityLower := by
  obtain ⟨member, feasible, optimal⟩ := legal_best_sound _ _ values selected chosen
  have checks : selected.nominal.gamma = g ∧ selected.nominal.utilityVersion = utilityVersion ∧
      selected.nominal.riskLimit = riskLimit ∧ selected.nominal.action.id ∈ allowed ∧
      selected.riskUpper ≤ riskLimit := by simpa using feasible
  refine ⟨member, checks.1, checks.2.1, checks.2.2.1, checks.2.2.2.1, checks.2.2.2.2, ?_⟩
  intro other hm hg hu hl ha hr
  exact optimal other hm (by simp [hg, hu, hl, ha, hr])

theorem maximin_none_exactly_when_infeasible {m : ℕ} (g : Gamma)
    (utilityVersion : ℕ) (riskLimit : ℚ) (allowed : List ℕ)
    (values : List (IntervalDecision m)) :
    chooseMaximin g utilityVersion riskLimit allowed values = none ↔
      ∀ v ∈ values, ¬ (v.nominal.gamma = g ∧ v.nominal.utilityVersion = utilityVersion ∧
        v.nominal.riskLimit = riskLimit ∧ v.nominal.action.id ∈ allowed ∧ v.riskUpper ≤ riskLimit) := by
  unfold chooseMaximin legalBest
  rw [best_none]
  simp

-- The same measurable confidence event now reaches the actual computed decision,
-- not merely a separately supplied interval. q is explicitly the observed bin
-- law. Its interpretation as an intervention law still needs identification.
theorem whole_computed_decision_bin_law_confidence {Ω : Type*} {m n k : ℕ}
    [MeasurableSpace Ω] [MeasurableSpace (Fin m × Bool)]
    [MeasurableSingletonClass (Fin m × Bool)]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (P : Measure (Fin m × Bool)) [IsProbabilityMeasure P] (hm : 0 < m) (hn : 0 < n)
    (request : DecisionRequest m) (loss : ℚ → Bool → ℚ)
    (first : List ℚ) (rest : List (List ℚ))
    (sample : Fin n → Ω → Fin m × Bool) (sampleMeasurable : ∀ i, Measurable (sample i))
    (independent : iIndepFun sample μ) (law : ∀ i, IdentDistrib (sample i) id μ P)
    (hδ : 0 < request.protocol.failureBudget) (hδ1 : request.protocol.failureBudget < 1) :
    ∃ confidence : Set Ω, MeasurableSet confidence ∧
      1 - (request.protocol.failureBudget : ℝ) ≤ μ.real confidence ∧
      ∀ w ∈ confidence, ∀ (training : Fin k → SampleObservation m Bool)
        (events : Fin n → EventId) (radius : ℚ) (exponent : ℕ) (supported : Bool)
        (utility : ℚ → ℚ) (a : BinaryQuote) (out : IntervalDecision m),
        fitToDecision request request.protocol loss (first :: rest) training
          (fun i => ⟨events i, (sample i w).1, (sample i w).2⟩)
          radius exponent supported utility a = .known out →
        let bin := scoreBin (out.probability.fitted.table, out.probability.query)
        let q := P.real {z | bin z = true ∧ z.2 = true} / P.real {z | bin z = true}
        0 < P.real {z | bin z = true} ∧
        (out.netLower : ℝ) ≤ q * (evalExact a.success.expr : ℝ) +
          (1-q) * (evalExact a.failure.expr : ℝ) - (a.cost.value : ℝ) ∧
        q * (evalExact a.success.expr : ℝ) + (1-q) * (evalExact a.failure.expr : ℝ) -
          (a.cost.value : ℝ) ≤ (out.netUpper : ℝ) ∧
        (out.utilityLower : ℝ) ≤ q * (utility (evalExact a.success.expr - a.cost.value) : ℝ) +
          (1-q) * (utility (evalExact a.failure.expr - a.cost.value) : ℝ) ∧
        q * (utility (evalExact a.success.expr - a.cost.value) : ℝ) +
          (1-q) * (utility (evalExact a.failure.expr - a.cost.value) : ℝ) ≤ (out.utilityUpper : ℝ) ∧
        q * (if evalExact a.success.expr - a.cost.value < 0 then (1 : ℝ) else 0) +
          (1-q) * (if evalExact a.failure.expr - a.cost.value < 0 then (1 : ℝ) else 0) ≤
          (out.riskUpper : ℝ) := by
  obtain ⟨confidence, measurable, probability, sound⟩ := whole_pipeline_bin_probability_confidence
    (k := k) μ P hm hn request.protocol loss first rest sample sampleMeasurable independent law hδ hδ1
  refine ⟨confidence, measurable, probability, ?_⟩
  intro w hw training events radius exponent supported utility a out accepted
  obtain ⟨p, predicted, evaluated, same⟩ := fit_to_decision_passes_the_actual_probability
    request request.protocol loss (first :: rest) training _ radius exponent supported utility a out accepted
  have interval := sound w hw training events request.query radius exponent
    request.calibrationSnapshot supported p predicted
  have propagated := computed_decision_encloses_cash_utility_and_risk request utility p a out evaluated
    _ interval.2.1 interval.2.2
  simpa only [same] using And.intro interval.1 propagated

end JurisLean.Candidates.IntervalDecisionConsumer20261027
