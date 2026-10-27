import JurisLean.Candidates.LegalActionDomain20261027
import JurisLean.Candidates.AdaptiveRoundLedger20261027

/-!
The production decision path reads the actually loaded model. A separately
attested calibration packet binds its full contents, context, sample and fixed
model family. Candidate generation and activation remain the existing separate
state transitions. This function neither refits a candidate nor loads one.

The catalog is an external attestation input, not a proof of its own authority.
The population theorem retains measurable iid observations under one declared
law and a fixed finite family. Its interval is conditional on a score bin, not
an individual-case truth probability or an identified intervention effect.
-/

namespace JurisLean.Candidates.LoadedLegalConsumer20261027

open MeasureTheory ProbabilityTheory
open JurisLean.Candidates.Final20261021
open JurisLean.Candidates.LearningConsumer20261027
open JurisLean.Candidates.LearningERM20261027
open JurisLean.Candidates.LearningFiniteClass20261027
open JurisLean.Candidates.SelectiveCalibration20261027
open JurisLean.Candidates.SampleCalibrationConsumer20261027
open JurisLean.Candidates.ProbabilityIntervalConsumer20261027
open JurisLean.Candidates.IntervalDecisionConsumer20261027
open JurisLean.Candidates.DecisionTrajectoryConsumer20261027
open JurisLean.Candidates.EventFeedbackConsumer20261027
open JurisLean.Candidates.ProtectedFeedback20261027
open JurisLean.Candidates.ValidatedFeedbackLoad20261027
open JurisLean.Candidates.AdaptiveRoundLedger20261027
open JurisLean.Candidates.LegalActionDomain20261027

structure CalibrationPacket (m : Nat) where
  context : Gamma
  loaded : TrainingCandidate m
  models : List (List ℚ)
  rows : List (SampleObservation m Bool)
  snapshot : Nat
  declaredAt : Instant
  acquiredAt : Instant
  modelAvailableAt : Instant
  source : SourceRef
  supported : Bool
  deriving DecidableEq, Repr

def calibrationData {m : Nat} (packet : CalibrationPacket m) :
    Fin packet.rows.length → Fin m × Bool :=
  fun i => let row := packet.rows.get i; (row.feature, row.label)

-- An effective date is not an acquisition date. Correction/removal availability
-- is covered by the independent attestation of the complete loaded package.
def historyKnownBy {m : Nat} (cutoff : Instant) (history : List (Change m)) : Bool :=
  history.all fun change => match change with
    | .observed row => decide (row.observedAt.ticks ≤ cutoff.ticks)
    | .corrected edit => match edit.replacement with
        | some row => decide (row.observedAt.ticks ≤ cutoff.ticks)
        | none => true

def calibrationTimeReady {m : Nat} (g : Gamma) (packet : CalibrationPacket m) : Bool :=
  decide (packet.modelAvailableAt.ticks ≤ g.knowledgeCutoff.ticks ∧
    packet.modelAvailableAt.ticks ≤ g.recordCutoff.ticks ∧
    packet.acquiredAt.ticks ≤ g.knowledgeCutoff.ticks ∧
    packet.acquiredAt.ticks ≤ g.recordCutoff.ticks) &&
  historyKnownBy g.knowledgeCutoff packet.loaded.snapshot.history

def calibrationReady {m : Nat} (state : RoundState m) (request : DecisionRequest m)
    (packet : CalibrationPacket m) (catalog : List (CalibrationPacket m)) : Bool :=
  decide (packet ∈ catalog ∧ packet.loaded = readLoaded state.service ∧
    packet.context = state.service.gamma ∧ request.gamma = state.service.gamma ∧
    request.protocol = (readLoaded state.service).fitted.protocol ∧
    packet.snapshot = request.calibrationSnapshot ∧
    packet.loaded.snapshot.scope = state.service.journal.scope ∧
    protocolMatches state.service.journal.scope request.protocol = true ∧
    request.protocol.lossVersion = state.service.lossVersion ∧
    state.service.journal.scope.ruleVersion = request.gamma.normVersion ∧
    state.service.journal.scope.mechanismVersion = request.gamma.mechanismVersion ∧
    packet.declaredAt.ticks < packet.acquiredAt.ticks ∧
    calibrationTimeReady request.gamma packet = true ∧
    (∀ table ∈ packet.models, table.length = m) ∧
    packet.rows.Pairwise (fun a b => a.event ≠ b.event) ∧
    ∀ row ∈ packet.rows, row.event ∉ trainingEvents state.service.journal ∧
      row.event ∉ trainingEvents (readLoaded state.service).snapshot ∧
      row.event ∉ exposedRoundEvents state)

def loadedProbability {m : Nat} (state : RoundState m) (request : DecisionRequest m)
    (packet : CalibrationPacket m) (catalog : List (CalibrationPacket m))
    (radius : ℚ) (exponent : Nat) : Result (SampleProbability m) :=
  if calibrationReady state request packet catalog = false then .unknown .scopeMismatch
  else produceInterval request.protocol (readLoaded state.service).fitted packet.models
    (calibrationData packet) request.query radius exponent packet.snapshot packet.supported

theorem known_probability_binds_actual_loaded_and_sample {m : Nat}
    (state : RoundState m) (request : DecisionRequest m) (packet : CalibrationPacket m)
    (catalog : List (CalibrationPacket m)) (radius : ℚ) (exponent : Nat)
    (out : SampleProbability m)
    (known : loadedProbability state request packet catalog radius exponent = .known out) :
    calibrationReady state request packet catalog = true ∧
    produceInterval request.protocol (readLoaded state.service).fitted packet.models
      (calibrationData packet) request.query radius exponent packet.snapshot packet.supported = .known out ∧
    packet ∈ catalog ∧ packet.loaded = readLoaded state.service ∧
    out.fitted = (readLoaded state.service).fitted ∧
    out.fitted.table.getD request.query.val 0 = predictLoaded state.service request.query := by
  unfold loadedProbability at known
  split at known
  · cases known
  · rename_i ready
    have accepted : calibrationReady state request packet catalog = true := by simpa using ready
    have bindings := accepted
    simp only [calibrationReady, decide_eq_true_eq] at bindings
    obtain ⟨same, _, _, _, _⟩ := actual_samples_determine_probability request.protocol
      (readLoaded state.service).fitted packet.models (calibrationData packet) request.query
      radius exponent packet.snapshot packet.supported out known
    exact ⟨accepted, known, bindings.1, bindings.2.1, by rw [same], by rw [same]; rfl⟩

theorem changed_loaded_contents_refuse_old_calibration {m : Nat}
    (state : RoundState m) (request : DecisionRequest m) (packet : CalibrationPacket m)
    (catalog : List (CalibrationPacket m)) (radius : ℚ) (exponent : Nat)
    (changed : packet.loaded ≠ readLoaded state.service) :
    loadedProbability state request packet catalog radius exponent = .unknown .scopeMismatch := by
  simp [loadedProbability, calibrationReady, changed]

theorem known_probability_respects_cutoffs {m : Nat}
    (state : RoundState m) (request : DecisionRequest m) (packet : CalibrationPacket m)
    (catalog : List (CalibrationPacket m)) (radius : ℚ) (exponent : Nat)
    (out : SampleProbability m)
    (known : loadedProbability state request packet catalog radius exponent = .known out) :
    (packet.modelAvailableAt.ticks ≤ request.gamma.knowledgeCutoff.ticks ∧
      packet.modelAvailableAt.ticks ≤ request.gamma.recordCutoff.ticks ∧
      packet.acquiredAt.ticks ≤ request.gamma.knowledgeCutoff.ticks ∧
      packet.acquiredAt.ticks ≤ request.gamma.recordCutoff.ticks) ∧
    historyKnownBy request.gamma.knowledgeCutoff packet.loaded.snapshot.history = true := by
  have ready := (known_probability_binds_actual_loaded_and_sample state request packet
    catalog radius exponent out known).1
  simp only [calibrationReady, decide_eq_true_eq] at ready
  have time : calibrationTimeReady request.gamma packet = true := by tauto
  simpa only [calibrationTimeReady, Bool.and_eq_true, decide_eq_true_eq] using time

theorem future_model_is_not_available_for_prior_question {m : Nat}
    (state : RoundState m) (request : DecisionRequest m) (packet : CalibrationPacket m)
    (catalog : List (CalibrationPacket m)) (radius : ℚ) (exponent : Nat)
    (late : request.gamma.knowledgeCutoff.ticks < packet.modelAvailableAt.ticks) :
    loadedProbability state request packet catalog radius exponent = .unknown .scopeMismatch := by
  simp [loadedProbability, calibrationReady, calibrationTimeReady, not_le_of_gt late]

theorem future_loaded_observations_stay_unknown {m : Nat}
    (state : RoundState m) (request : DecisionRequest m) (packet : CalibrationPacket m)
    (catalog : List (CalibrationPacket m)) (radius : ℚ) (exponent : Nat)
    (future : historyKnownBy request.gamma.knowledgeCutoff packet.loaded.snapshot.history = false) :
    loadedProbability state request packet catalog radius exponent = .unknown .scopeMismatch := by
  simp [loadedProbability, calibrationReady, calibrationTimeReady, future]

theorem missing_calibration_attestation_stays_unknown {m : Nat}
    (state : RoundState m) (request : DecisionRequest m) (packet : CalibrationPacket m)
    (catalog : List (CalibrationPacket m)) (radius : ℚ) (exponent : Nat)
    (missing : packet ∉ catalog) :
    loadedProbability state request packet catalog radius exponent = .unknown .scopeMismatch := by
  simp [loadedProbability, calibrationReady, missing]

def chooseLoaded {m : Nat} (request : DecisionRequest m) (utility : ℚ → ℚ)
    (proposals : List Proposal) (probability : Result (SampleProbability m)) :
    Result (IntervalDecision m) :=
  match probability with
  | .known p =>
      match chooseMaximin request.gamma request.utilityVersion request.riskLimit
          (proposals.map fun q => q.quote.id) (evaluatedQuotes request utility p (proposals.map Proposal.quote)) with
      | some chosen => .known chosen
      | none => .unknown .notIdentified
  | .unknown e => .unknown e
  | .rejected e => .rejected e
  | .conflict a b => .conflict a b

theorem selected_decision_reads_same_probability_and_quote {m : Nat}
    (request : DecisionRequest m) (utility : ℚ → ℚ) (proposals : List Proposal)
    (probability : Result (SampleProbability m)) (selected : IntervalDecision m)
    (chosen : chooseLoaded request utility proposals probability = .known selected) :
    ∃ p quote, probability = .known p ∧ quote ∈ proposals.map Proposal.quote ∧
      evaluateInterval request utility p quote = .known selected ∧ selected.probability = p ∧
      selected.nominal.gamma = request.gamma ∧ selected.riskUpper ≤ request.riskLimit := by
  cases predicted : probability with
  | unknown e => simp [chooseLoaded, predicted] at chosen
  | rejected e => simp [chooseLoaded, predicted] at chosen
  | conflict a b => simp [chooseLoaded, predicted] at chosen
  | known p =>
      simp only [chooseLoaded, predicted] at chosen
      cases selection : chooseMaximin request.gamma request.utilityVersion request.riskLimit
          (proposals.map fun q => q.quote.id) (evaluatedQuotes request utility p (proposals.map Proposal.quote)) with
      | none => simp [selection] at chosen
      | some value =>
          simp only [selection, Result.known.injEq] at chosen
          subst value
          obtain ⟨member, context, _, _, _, risk, _⟩ :=
            explicit_maximin_preserves_permission_and_risk request.gamma request.utilityVersion
              request.riskLimit _ _ selected selection
          obtain ⟨quote, included, evaluated⟩ := List.mem_filterMap.mp member
          cases evaluation : evaluateInterval request utility p quote with
          | unknown e => simp [evaluation] at evaluated
          | rejected e => simp [evaluation] at evaluated
          | conflict a b => simp [evaluation] at evaluated
          | known out =>
              simp only [evaluation, Option.some.injEq] at evaluated
              subst out
              exact ⟨p, quote, rfl, included, evaluation,
                (interval_evaluation_reads_the_receipt request utility p quote selected evaluation).1,
                context, risk⟩

structure LoadedRun (W : Type) (m : Nat) where
  review : DomainReview W
  probability : Result (SampleProbability m)
  decision : Result (IntervalDecision m)
  execution : ExecutionChoice

def runLoaded {W : Type} {m : Nat} (input : LegalInput W)
    (model : ActionModel W Ledger.Handle) (proposals : List Proposal)
    (state : RoundState m) (request : DecisionRequest m) (packet : CalibrationPacket m)
    (catalog : List (CalibrationPacket m)) (radius : ℚ) (exponent : Nat)
    (utility : ℚ → ℚ) (grants : List Authorization.Grant) (initial : Ledger.Handle) : LoadedRun W m :=
  let domain := review input model initial proposals
  let probability := loadedProbability state request packet catalog radius exponent
  let decision := if input.anchor.gamma ≠ request.gamma ∨ initial.gamma ≠ request.gamma then
      Result.rejected .scopeMismatch
    else chooseLoaded request utility domain.allowed probability
  ⟨domain, probability, decision, executeDecision request utility domain.allowed decision grants initial⟩

theorem loaded_run_uses_actual_legal_validation {W : Type} {m : Nat}
    (input : LegalInput W) (model : ActionModel W Ledger.Handle) (proposals : List Proposal)
    (state : RoundState m) (request : DecisionRequest m) (packet : CalibrationPacket m)
    (catalog : List (CalibrationPacket m)) (radius : ℚ) (exponent : Nat)
    (utility : ℚ → ℚ) (grants : List Authorization.Grant) (initial : Ledger.Handle)
    (proposal : Proposal)
    (chosen : (runLoaded input model proposals state request packet catalog radius exponent utility
      grants initial).execution.proposal = some proposal) :
    ∃ branches, input.inspect = .known branches ∧ proposal ∈ proposals ∧
      accepts model input.truth initial input.anchor.gamma branches proposal = true := by
  have linked := chosen_execution_uses_the_entire_approved_instruction_list request utility
    (review input model initial proposals).allowed _ grants initial proposal chosen
  obtain ⟨selected, _, member, _, _⟩ := linked
  exact domain_consumes_actual_validator input model initial proposals proposal member

theorem loaded_run_choice_uses_current_model {W : Type} {m : Nat}
    (input : LegalInput W) (model : ActionModel W Ledger.Handle) (proposals : List Proposal)
    (state : RoundState m) (request : DecisionRequest m) (packet : CalibrationPacket m)
    (catalog : List (CalibrationPacket m)) (radius : ℚ) (exponent : Nat)
    (utility : ℚ → ℚ) (grants : List Authorization.Grant) (initial : Ledger.Handle)
    (selected : IntervalDecision m)
    (chosen : (runLoaded input model proposals state request packet catalog radius exponent utility
      grants initial).decision = .known selected) :
    selected.probability.fitted = (readLoaded state.service).fitted ∧
    selected.probability.fitted.table.getD request.query.val 0 = predictLoaded state.service request.query ∧
    selected.nominal.gamma = request.gamma ∧ selected.riskUpper ≤ request.riskLimit := by
  change (if _ then Result.rejected .scopeMismatch else _) = .known selected at chosen
  split at chosen
  · cases chosen
  · obtain ⟨p, quote, produced, _, _, same, context, risk⟩ :=
      selected_decision_reads_same_probability_and_quote request utility
        (review input model initial proposals).allowed _ selected chosen
    have actual := known_probability_binds_actual_loaded_and_sample state request packet catalog
      radius exponent p produced
    rw [same]
    exact ⟨actual.2.2.2.2.1, actual.2.2.2.2.2, context, risk⟩

theorem loaded_run_preserves_reported_business_invariant {W : Type} {m : Nat}
    (input : LegalInput W) (model : ActionModel W Ledger.Handle) (proposals : List Proposal)
    (state : RoundState m) (request : DecisionRequest m) (packet : CalibrationPacket m)
    (catalog : List (CalibrationPacket m)) (radius : ℚ) (exponent : Nat)
    (utility : ℚ → ℚ) (grants : List Authorization.Grant) (initial final : Ledger.Handle)
    (valid : Trace.Invariant initial)
    (reported : (runLoaded input model proposals state request packet catalog radius exponent utility
      grants initial).execution.payment.current = some final) : Trace.Invariant final := by
  exact execution_choice_preserves_reported_state_invariant request utility
    (review input model initial proposals).allowed _ grants initial final valid reported

theorem unknown_loaded_probability_has_no_transaction_effect {m : Nat}
    (request : DecisionRequest m) (utility : ℚ → ℚ) (proposals : List Proposal)
    (grants : List Authorization.Grant) (initial : Ledger.Handle) (reason : Error) :
    (executeDecision request utility proposals (chooseLoaded request utility proposals (.unknown reason))
      grants initial).payment.current = some initial ∧
    (executeDecision request utility proposals (chooseLoaded request utility proposals (.unknown reason))
      grants initial).payment.outcomes = [] := ⟨rfl, rfl⟩


-- The confidence event is simultaneous over every declared model and query.
-- Thus a currently loaded table can be consumed without fitting a new table.
theorem frozen_family_probability_confidence {Ω : Type*} {m n : ℕ}
    [MeasurableSpace Ω] [MeasurableSpace (Fin m × Bool)]
    [MeasurableSingletonClass (Fin m × Bool)]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (P : Measure (Fin m × Bool)) [IsProbabilityMeasure P] (hm : 0 < m) (hn : 0 < n)
    (protocol : LearningProtocol) (first : List ℚ) (rest : List (List ℚ))
    (sample : Fin n → Ω → Fin m × Bool) (sampleMeasurable : ∀ i, Measurable (sample i))
    (independent : iIndepFun sample μ) (law : ∀ i, IdentDistrib (sample i) id μ P)
    (hδ : 0 < protocol.failureBudget) (hδ1 : protocol.failureBudget < 1) :
    ∃ confidence : Set Ω, MeasurableSet confidence ∧
      1 - (protocol.failureBudget : ℝ) ≤ μ.real confidence ∧
      ∀ w ∈ confidence, ∀ (fitted : FittedTable) (query : Fin m) (radius : ℚ)
        (exponent snapshot : ℕ) (supported : Bool) (out : SampleProbability m),
        produceInterval protocol fitted (first :: rest) (fun i => sample i w)
          query radius exponent snapshot supported = .known out →
        0 < P.real {z | scoreBin (out.fitted.table, out.query) z = true} ∧
        (out.lower : ℝ) ≤
          P.real {z | scoreBin (out.fitted.table, out.query) z = true ∧ z.2 = true} /
            P.real {z | scoreBin (out.fitted.table, out.query) z = true} ∧
        P.real {z | scoreBin (out.fitted.table, out.query) z = true ∧ z.2 = true} /
            P.real {z | scoreBin (out.fitted.table, out.query) z = true} ≤ (out.upper : ℝ) := by
  let bins := modelBins (m := m) (first :: rest)
  have nonempty : bins.Nonempty := ⟨(first, ⟨0, hm⟩), by simp [bins, modelBins]⟩
  have numeratorMeasurable : ∀ c ∈ bins,
      Measurable (fun z => (numeratorLoss successLabel scoreBin c z : ℝ)) :=
    fun _ _ => measurable_of_finite _
  have denominatorMeasurable : ∀ c ∈ bins,
      Measurable (fun z => (coverageLoss scoreBin c z : ℝ)) :=
    fun _ _ => measurable_of_finite _
  have bounded : ∀ c ∈ bins, ∀ z, (successLabel c z : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by
    intro c _ z
    cases hy : z.2 <;> simp [successLabel, hy]
  have hd : (0 : ℝ) < (protocol.failureBudget : ℝ) := by exact_mod_cast hδ
  have hd1 : (protocol.failureBudget : ℝ) < 1 := by exact_mod_cast hδ1
  have uniform := q05_3_simultaneous_numerator_and_coverage μ P hn bins nonempty
    sample sampleMeasurable independent law successLabel scoreBin
    numeratorMeasurable denominatorMeasurable bounded (protocol.failureBudget : ℝ) hd hd1
  refine ⟨_, q05_3_joint_confidence_event_measurable P bins sample sampleMeasurable
    successLabel scoreBin numeratorMeasurable denominatorMeasurable _, uniform, ?_⟩
  intro w hw fitted query radius exponent snapshot supported out accepted
  obtain ⟨rfl, scope, member, verified, positive⟩ := actual_samples_determine_probability
    protocol fitted (first :: rest) (fun i => sample i w) query radius exponent snapshot supported out accepted
  have candidateMember : (fitted.table, query) ∈ bins :=
    Finset.mem_product.mpr ⟨List.mem_toFinset.mpr member, Finset.mem_univ query⟩
  have deviation := hw (fitted.table, query) candidateMember
  have conservative := radius_verification_sound n bins.card
    fitted.protocol.failureBudget radius exponent verified
  rw [← scope] at conservative
  let N := ∫ z, (numeratorLoss successLabel scoreBin (fitted.table, query) z : ℝ) ∂P
  let C := ∫ z, (coverageLoss scoreBin (fitted.table, query) z : ℝ) ∂P
  let nh := empiricalScore (numeratorLoss successLabel scoreBin) (fun i => sample i w) (fitted.table, query)
  let ch := empiricalScore (coverageLoss scoreBin) (fun i => sample i w) (fitted.table, query)
  have hnL : (nh : ℝ) - radius ≤ N := by have h := (abs_le.mp deviation.1).2; dsimp [N, nh]; linarith
  have hnU : N ≤ (nh : ℝ) + radius := by have h := (abs_le.mp deviation.1).1; dsimp [N, nh]; linarith
  have hcL : (ch : ℝ) - radius ≤ C := by have h := (abs_le.mp deviation.2).2; dsimp [C, ch]; linarith
  have hcU : C ≤ (ch : ℝ) + radius := by have h := (abs_le.mp deviation.2).1; dsimp [C, ch]; linarith
  have hpos : (0 : ℝ) < (ch : ℝ) - radius := by exact_mod_cast positive
  have integrals := population_bin_integrals P (fitted.table, query)
  have nNonnegative : 0 ≤ N := by rw [show N = _ from integrals.1]; exact measureReal_nonneg
  have nBelowC : N ≤ C := by
    rw [show N = _ from integrals.1, show C = _ from integrals.2]
    exact measureReal_mono (h₂ := measure_ne_top P _) (fun _ h => h.1)
  have enclosed := Probability.u04_2_enclosed_propagation N C
    ((nh : ℝ) - radius) ((nh : ℝ) + radius) ((ch : ℝ) - radius) ((ch : ℝ) + radius)
    nNonnegative nBelowC hnL hnU hpos hcL hcU
  have coveragePositive : 0 < C := lt_of_lt_of_le hpos hcL
  rw [show N = _ from integrals.1, show C = _ from integrals.2] at enclosed
  rw [show C = _ from integrals.2] at coveragePositive
  exact ⟨coveragePositive, by simpa [SampleProbability.lower, nh, ch] using enclosed.1,
    by simpa [SampleProbability.upper, nh, ch] using enclosed.2⟩

end JurisLean.Candidates.LoadedLegalConsumer20261027
