import JurisLean.Candidates.IntervalDecisionConsumer20261027
import JurisLean.Candidates.Final20261021.Pipeline

/-!
Original 04 edges 6--9 and the finite payment/refresh fragment of U00/U10.
The actual sample produces the probability used by every quote; an explicitly
chosen maximin rule selects an evaluated quote, whose exact payment sequence is
checked before execution. Every new payment checks the current full context and
payload grant. The interpreter threads actual committed/refresh poststates,
continues a replay from the current state, and stops on an unknown commit.

This is a mathematical-repository consumer, not a database or external payment
service. Source identity, legal-branch completeness, action-outcome identification,
and the interpretation of quoted payoffs remain external premises. Statistical
bounds concern the decision's initial scope; a later authorized context change
does not renew that statistical certificate. No full fifteen-edge U00 claim is
made by this payment/refresh fragment.
-/

namespace JurisLean.Candidates.DecisionTrajectoryConsumer20261027

open JurisLean.Candidates.Final20261021
open JurisLean.Candidates.LearningConsumer20261027
open JurisLean.Candidates.SampleCalibrationConsumer20261027
open JurisLean.Candidates.ProbabilityIntervalConsumer20261027
open JurisLean.Candidates.IntervalDecisionConsumer20261027

inductive Instruction where
  | pay (request : PaymentRequest) (mode : Ledger.Submission)
  | refresh (change : Pipeline.RefreshInput)
  deriving DecidableEq, Repr

def paymentPayloads : List Instruction → List PaymentPayload
  | [] => []
  | .pay req _ :: rest => req.payload :: paymentPayloads rest
  | .refresh _ :: rest => paymentPayloads rest

def runTrajectory (grants : List Authorization.Grant) (current : Ledger.Handle) :
    List Instruction → Pipeline.PaymentRun
  | [] => ⟨.success, some current, [], []⟩
  | .pay req mode :: rest =>
      let permission := Authorization.authorized grants current.gamma req.payload.payer 0
        req.payload.normVersion (.relation req.payload.relation) (some req.payload)
      let outcome := Ledger.consume_ext current current req permission mode
      match outcome with
      | .committed _ actualPost =>
          let tail := runTrajectory grants actualPost rest
          { tail with outcomes := outcome :: tail.outcomes }
      | .replay _ =>
          let tail := runTrajectory grants current rest
          { tail with outcomes := outcome :: tail.outcomes }
      | _ => Pipeline.finishPayment current outcome
  | .refresh change :: rest =>
      match Pipeline.refresh grants current change with
      | .known actualPost => runTrajectory grants actualPost rest
      | .unknown e => ⟨.undecided, some current, [], [e]⟩
      | .rejected e => ⟨.rejected, some current, [], [e]⟩
      | .conflict _ _ => ⟨.undecided, some current, [], [.versionConflict]⟩

theorem committed_head_feeds_actual_tail (grants : List Authorization.Grant)
    (before actualPost : Ledger.Handle) (req : PaymentRequest) (mode : Ledger.Submission)
    (receipt : Ledger.Receipt) (rest : List Instruction)
    (committed : Ledger.consume_ext before before req
      (Authorization.authorized grants before.gamma req.payload.payer 0 req.payload.normVersion
        (.relation req.payload.relation) (some req.payload)) mode = .committed receipt actualPost) :
    runTrajectory grants before (.pay req mode :: rest) =
      let tail := runTrajectory grants actualPost rest
      { tail with outcomes := .committed receipt actualPost :: tail.outcomes } := by
  simp only [runTrajectory, committed]

theorem replay_continues_from_current_state (grants : List Authorization.Grant)
    (current : Ledger.Handle) (req : PaymentRequest) (mode : Ledger.Submission)
    (receipt : Ledger.Receipt) (rest : List Instruction)
    (replayed : Ledger.consume_ext current current req
      (Authorization.authorized grants current.gamma req.payload.payer 0 req.payload.normVersion
        (.relation req.payload.relation) (some req.payload)) mode = .replay receipt) :
    runTrajectory grants current (.pay req mode :: rest) =
      let tail := runTrajectory grants current rest
      { tail with outcomes := .replay receipt :: tail.outcomes } := by
  simp only [runTrajectory, replayed]

theorem unknown_commit_stops_the_tail (grants : List Authorization.Grant)
    (current : Ledger.Handle) (req : PaymentRequest) (mode : Ledger.Submission)
    (key : PaymentId) (attempt : AttemptId) (rest : List Instruction)
    (unknown : Ledger.consume_ext current current req
      (Authorization.authorized grants current.gamma req.payload.payer 0 req.payload.normVersion
        (.relation req.payload.relation) (some req.payload)) mode = .unknownCommit key attempt) :
    runTrajectory grants current (.pay req mode :: rest) =
      ⟨.undecided, none, [.unknownCommit key attempt], [.missingEvidence]⟩ := by
  simp only [runTrajectory, unknown, Pipeline.finishPayment]

theorem authorized_refresh_feeds_actual_tail (grants : List Authorization.Grant)
    (current actualPost : Ledger.Handle) (change : Pipeline.RefreshInput) (rest : List Instruction)
    (refreshed : Pipeline.refresh grants current change = .known actualPost) :
    runTrajectory grants current (.refresh change :: rest) = runTrajectory grants actualPost rest := by
  simp only [runTrajectory, refreshed]

-- The path is derived from the executable interpreter for any finite list,
-- rather than supplied as an extra premise about a separately chosen trace.
theorem every_reported_post_has_an_actual_path (grants : List Authorization.Grant)
    (steps : List Instruction) (initial final : Ledger.Handle)
    (reported : (runTrajectory grants initial steps).current = some final) :
    Trace.Path initial final := by
  induction steps generalizing initial with
  | nil =>
      have same : initial = final := by simpa [runTrajectory] using reported
      subst final
      exact .nil initial
  | cons step rest ih =>
      cases step with
      | pay req mode =>
          cases executed : Ledger.consume_ext initial initial req
              (Authorization.authorized grants initial.gamma req.payload.payer 0 req.payload.normVersion
                (.relation req.payload.relation) (some req.payload)) mode with
          | committed receipt actualPost =>
              have tail := ih actualPost (by simpa only [runTrajectory, executed] using reported)
              exact .cons (Trace.u10_2_committed_executor_is_step initial initial req _ mode
                receipt actualPost executed) tail
          | replay receipt =>
              exact ih initial (by simpa only [runTrajectory, executed] using reported)
          | unknownCommit key attempt =>
              simp [runTrajectory, executed, Pipeline.finishPayment] at reported
          | rejectedNoCommit attempt e =>
              have same : initial = final := by
                simpa [runTrajectory, executed, Pipeline.finishPayment] using reported
              subst final
              exact .nil initial
          | conflict registered requested =>
              have same : initial = final := by
                simpa [runTrajectory, executed, Pipeline.finishPayment] using reported
              subst final
              exact .nil initial
          | pending e =>
              have same : initial = final := by
                simpa [runTrajectory, executed, Pipeline.finishPayment] using reported
              subst final
              exact .nil initial
      | refresh change =>
          cases refreshed : Pipeline.refresh grants initial change with
          | known actualPost =>
              exact .cons (Pipeline.u10_1_authorized_refresh_is_step grants initial actualPost change refreshed)
                (ih actualPost (by simpa only [runTrajectory, refreshed] using reported))
          | unknown e =>
              have same : initial = final := by simpa [runTrajectory, refreshed] using reported
              subst final
              exact .nil initial
          | rejected e =>
              have same : initial = final := by simpa [runTrajectory, refreshed] using reported
              subst final
              exact .nil initial
          | conflict x y =>
              have same : initial = final := by simpa [runTrajectory, refreshed] using reported
              subst final
              exact .nil initial

theorem finite_interpreter_preserves_full_invariant (grants : List Authorization.Grant)
    (steps : List Instruction) (initial final : Ledger.Handle) (valid : Trace.Invariant initial)
    (reported : (runTrajectory grants initial steps).current = some final) :
    Trace.Invariant final ∧ initial.state.used ⊆ final.state.used := by
  have path := every_reported_post_has_an_actual_path grants steps initial final reported
  exact ⟨Trace.u10_2_finite_trace_composition path valid, Trace.used_monotone_path path⟩

def evaluatedQuotes {m : ℕ} (request : DecisionRequest m) (utility : ℚ → ℚ)
    (p : SampleProbability m) (quotes : List BinaryQuote) : List (IntervalDecision m) :=
  quotes.filterMap fun quote => match evaluateInterval request utility p quote with
    | .known value => some value
    | _ => none

def fitChooseMaximin {m n k : ℕ} (request : DecisionRequest m) (sampleProtocol : LearningProtocol)
    (loss : ℚ → Bool → ℚ) (models : List (List ℚ))
    (training : Fin n → SampleObservation m Bool) (calibration : Fin k → SampleObservation m Bool)
    (radius : ℚ) (exponent : ℕ) (supported : Bool) (utility : ℚ → ℚ)
    (allowed : List ℕ) (quotes : List BinaryQuote) : Result (IntervalDecision m) :=
  match runProbability request.protocol sampleProtocol loss models training calibration
      request.query radius exponent request.calibrationSnapshot supported with
  | .known p =>
      match chooseMaximin request.gamma request.utilityVersion request.riskLimit allowed
          (evaluatedQuotes request utility p quotes) with
      | some chosen => .known chosen
      | none => .unknown .notIdentified
  | .unknown e => .unknown e
  | .rejected e => .rejected e
  | .conflict x y => .conflict x y

theorem selection_reads_actual_sample_and_quote {m n k : ℕ}
    (request : DecisionRequest m) (sampleProtocol : LearningProtocol) (loss : ℚ → Bool → ℚ)
    (models : List (List ℚ)) (training : Fin n → SampleObservation m Bool)
    (calibration : Fin k → SampleObservation m Bool) (radius : ℚ) (exponent : ℕ)
    (supported : Bool) (utility : ℚ → ℚ) (allowed : List ℕ) (quotes : List BinaryQuote)
    (selected : IntervalDecision m)
    (accepted : fitChooseMaximin request sampleProtocol loss models training calibration
      radius exponent supported utility allowed quotes = .known selected) :
    ∃ p quote, quote ∈ quotes ∧
      runProbability request.protocol sampleProtocol loss models training calibration
        request.query radius exponent request.calibrationSnapshot supported = .known p ∧
      evaluateInterval request utility p quote = .known selected ∧ selected.probability = p ∧
      selected.nominal.action.execution = quote.execution ∧ selected.nominal.gamma = request.gamma ∧
      selected.nominal.action.id ∈ allowed ∧ selected.riskUpper ≤ request.riskLimit := by
  unfold fitChooseMaximin at accepted
  cases predicted : runProbability request.protocol sampleProtocol loss models training calibration
      request.query radius exponent request.calibrationSnapshot supported with
  | unknown e => simp [predicted] at accepted
  | rejected e => simp [predicted] at accepted
  | conflict x y => simp [predicted] at accepted
  | known p =>
      simp only [predicted] at accepted
      cases choice : chooseMaximin request.gamma request.utilityVersion request.riskLimit allowed
          (evaluatedQuotes request utility p quotes) with
      | none => simp [choice] at accepted
      | some chosen =>
          simp only [choice, Result.known.injEq] at accepted
          subst chosen
          obtain ⟨member, context, _, _, permitted, risk, _⟩ :=
            explicit_maximin_preserves_permission_and_risk request.gamma request.utilityVersion
              request.riskLimit allowed _ selected choice
          obtain ⟨quote, included, evaluated⟩ := List.mem_filterMap.mp member
          cases evaluation : evaluateInterval request utility p quote with
          | unknown e => simp [evaluation] at evaluated
          | rejected e => simp [evaluation] at evaluated
          | conflict x y => simp [evaluation] at evaluated
          | known value =>
              simp only [evaluation, Option.some.injEq] at evaluated
              subst value
              have read := interval_evaluation_reads_the_receipt request utility p quote selected evaluation
              have action := (binary_evaluation_uses_exact_amount_and_one_cost request.gamma utility
                request.utilityVersion request.riskLimit quote p.estimate selected.nominal read.2.1).2.1
              refine ⟨p, quote, included, rfl, evaluation, read.1, ?_, context, permitted, risk⟩
              simp only [action, BinaryQuote.atProbability]

-- A failed decision has no transaction effect. A successful decision still
-- requires an exact plan match and the independently checked dynamic grants.
def executeSelected {m : ℕ} (selected : IntervalDecision m) (grants : List Authorization.Grant)
    (initial : Ledger.Handle) (steps : List Instruction) : Pipeline.PaymentRun :=
  if initial.gamma ≠ selected.nominal.gamma then
    ⟨.rejected, some initial, [], [.scopeMismatch]⟩
  else if paymentPayloads steps ≠ selected.nominal.action.execution then
    ⟨.rejected, some initial, [], [.scopeMismatch]⟩
  else runTrajectory grants initial steps

structure DecisionRun (m : ℕ) where
  decision : Result (IntervalDecision m)
  payment : Pipeline.PaymentRun
  deriving DecidableEq

def runSampledDecision {m n k : ℕ} (request : DecisionRequest m) (sampleProtocol : LearningProtocol)
    (loss : ℚ → Bool → ℚ) (models : List (List ℚ))
    (training : Fin n → SampleObservation m Bool) (calibration : Fin k → SampleObservation m Bool)
    (radius : ℚ) (exponent : ℕ) (supported : Bool) (utility : ℚ → ℚ)
    (allowed : List ℕ) (quotes : List BinaryQuote) (grants : List Authorization.Grant)
    (initial : Ledger.Handle) (steps : List Instruction) : DecisionRun m :=
  let decision := fitChooseMaximin request sampleProtocol loss models training calibration
    radius exponent supported utility allowed quotes
  let payment := match decision with
    | .known selected => executeSelected selected grants initial steps
    | .unknown e => ⟨.undecided, some initial, [], [e]⟩
    | .rejected e => ⟨.rejected, some initial, [], [e]⟩
    | .conflict _ _ => ⟨.undecided, some initial, [], [.versionConflict]⟩
  ⟨decision, payment⟩

theorem substituted_execution_is_refused {m : ℕ} (selected : IntervalDecision m)
    (grants : List Authorization.Grant) (initial : Ledger.Handle) (steps : List Instruction)
    (changed : paymentPayloads steps ≠ selected.nominal.action.execution) :
    executeSelected selected grants initial steps =
      ⟨.rejected, some initial, [], [.scopeMismatch]⟩ := by
  simp [executeSelected, changed]

theorem selected_execution_preserves_full_invariant {m : ℕ} (selected : IntervalDecision m)
    (grants : List Authorization.Grant) (initial final : Ledger.Handle) (steps : List Instruction)
    (valid : Trace.Invariant initial)
    (reported : (executeSelected selected grants initial steps).current = some final) :
    Trace.Invariant final := by
  unfold executeSelected at reported
  split at reported
  · have same : initial = final := by simpa using reported
    subst final
    exact valid
  · split at reported
    · have same : initial = final := by simpa using reported
      subst final
      exact valid
    · exact (finite_interpreter_preserves_full_invariant grants steps initial final valid reported).1

theorem complete_consumer_uses_the_chosen_execution {m n k : ℕ}
    (request : DecisionRequest m) (sampleProtocol : LearningProtocol) (loss : ℚ → Bool → ℚ)
    (models : List (List ℚ)) (training : Fin n → SampleObservation m Bool)
    (calibration : Fin k → SampleObservation m Bool) (radius : ℚ) (exponent : ℕ)
    (supported : Bool) (utility : ℚ → ℚ) (allowed : List ℕ) (quotes : List BinaryQuote)
    (grants : List Authorization.Grant) (initial : Ledger.Handle) (steps : List Instruction)
    (selected : IntervalDecision m)
    (accepted : (runSampledDecision request sampleProtocol loss models training calibration
      radius exponent supported utility allowed quotes grants initial steps).decision = .known selected) :
    (runSampledDecision request sampleProtocol loss models training calibration
      radius exponent supported utility allowed quotes grants initial steps).payment =
      executeSelected selected grants initial steps := by
  change fitChooseMaximin request sampleProtocol loss models training calibration
    radius exponent supported utility allowed quotes = .known selected at accepted
  simp only [runSampledDecision, accepted]

theorem successful_execution_is_the_selected_plan {m : ℕ} (selected : IntervalDecision m)
    (grants : List Authorization.Grant) (initial : Ledger.Handle) (steps : List Instruction)
    (success : (executeSelected selected grants initial steps).exit = .success) :
    initial.gamma = selected.nominal.gamma ∧
      paymentPayloads steps = selected.nominal.action.execution ∧
      executeSelected selected grants initial steps = runTrajectory grants initial steps := by
  unfold executeSelected at success
  split at success
  · cases success
  · rename_i context
    split at success
    · cases success
    · rename_i payloads
      have sameContext : initial.gamma = selected.nominal.gamma := by simpa using context
      have samePlan : paymentPayloads steps = selected.nominal.action.execution := by simpa using payloads
      exact ⟨sameContext, samePlan, by simp [executeSelected, sameContext, samePlan]⟩

theorem sampled_consumer_preserves_known_state {m n k : ℕ}
    (request : DecisionRequest m) (sampleProtocol : LearningProtocol) (loss : ℚ → Bool → ℚ)
    (models : List (List ℚ)) (training : Fin n → SampleObservation m Bool)
    (calibration : Fin k → SampleObservation m Bool) (radius : ℚ) (exponent : ℕ)
    (supported : Bool) (utility : ℚ → ℚ) (allowed : List ℕ) (quotes : List BinaryQuote)
    (grants : List Authorization.Grant) (initial final : Ledger.Handle) (steps : List Instruction)
    (valid : Trace.Invariant initial)
    (reported : (runSampledDecision request sampleProtocol loss models training calibration
      radius exponent supported utility allowed quotes grants initial steps).payment.current = some final) :
    Trace.Invariant final := by
  cases choice : fitChooseMaximin request sampleProtocol loss models training calibration
      radius exponent supported utility allowed quotes with
  | known selected =>
      exact selected_execution_preserves_full_invariant selected grants initial final steps valid
        (by simpa only [runSampledDecision, choice] using reported)
  | unknown e =>
      have same : initial = final := by simpa [runSampledDecision, choice] using reported
      subst final
      exact valid
  | rejected e =>
      have same : initial = final := by simpa [runSampledDecision, choice] using reported
      subst final
      exact valid
  | conflict x y =>
      have same : initial = final := by simpa [runSampledDecision, choice] using reported
      subst final
      exact valid

end JurisLean.Candidates.DecisionTrajectoryConsumer20261027
