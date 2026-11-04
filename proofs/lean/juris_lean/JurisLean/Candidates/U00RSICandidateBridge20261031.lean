import JurisLean.Candidates.Final20261021.RSI
import JurisLean.Candidates.AdaptiveRoundLedger20261027

noncomputable section

namespace JurisLean.Candidates.U00RSICandidateBridge20261031

open JurisLean.Candidates.Final20261021
open JurisLean.Candidates.LearningConsumer20261027
open JurisLean.Candidates.EventFeedbackConsumer20261027
open JurisLean.Candidates.ProtectedFeedback20261027
open JurisLean.Candidates.ValidatedFeedbackLoad20261027

/-!
U00 L734/L756/L759, consumer edge 13.
The catalog contains complete finite candidates. Its unary index codec is not
a compiler for arbitrary programs. Log meanings are declared extraction inputs;
their external truth is not manufactured by lookup or fitting.
-/

def encodeIndex {k : Nat} (i : Fin k) : List UInt8 :=
  List.replicate (i.val + 1) 0

def decodeIndex {k : Nat} (bytes : List UInt8) : Option (Fin k) :=
  if h : bytes.length - 1 < k then
    let i : Fin k := ⟨bytes.length - 1, h⟩
    if bytes = encodeIndex i then some i else none
  else none

/-- Edge 13 content binding: actual decoding in the same finite catalog
recovers the encoded index, without a decoder-correctness assumption. -/
private theorem index_codec_roundtrip {k : Nat} (i : Fin k) :
    decodeIndex (encodeIndex i) = some i := by
  simp [decodeIndex, encodeIndex, i.isLt]

def checkpointFor {m k : Nat} (catalog : Fin k → TrainingCandidate m)
    (i : Fin k) (principal : PartyId) (query : Fin m) (evidence : SourceRef) :
    RSI.Checkpoint :=
  let parent := catalog i
  { principal := principal
    task := parent.fitted.protocol.fit.task
    target := parent.fitted.protocol.fit.target
    feature := parent.fitted.protocol.fit.featureVersion
    ruleVersion := parent.snapshot.scope.ruleVersion
    mechanism := parent.snapshot.scope.mechanismVersion
    scope := parent.snapshot.scope.effectiveDomain
    version := parent.fitted.protocol.fit.modelVersion
    bytes := encodeIndex i
    prediction := parent.fitted.table.getD query.val 0
    evidence := evidence }

abbrev validSelection {m k : Nat} (catalog : Fin k → TrainingCandidate m)
    (state : RSI.State) (request : RSI.PredictionRequest) (query : Fin m)
    (checkpoint : RSI.Checkpoint) (i : Fin k) : Prop :=
  RSI.checkpointMatches request checkpoint = true ∧
    checkpoint = checkpointFor catalog i request.principal query checkpoint.evidence ∧
    state.rules = request.ruleVersion ∧ state.mechanism = request.mechanism ∧
    protocolMatches (catalog i).snapshot.scope (catalog i).fitted.protocol = true

def selectIndex {m k : Nat} (catalog : Fin k → TrainingCandidate m)
    (state : RSI.State) (request : RSI.PredictionRequest) (query : Fin m)
    (population prior retrieved : Option RSI.Checkpoint) :
    Result (RSI.Checkpoint × Fin k) :=
  match RSI.proposed_checkpoint_service request (state.personal request.principal)
      population prior retrieved with
  | .known checkpoint =>
      match decodeIndex checkpoint.bytes with
      | none => .unknown .unsupported
      | some i =>
          if validSelection catalog state request query checkpoint i then
            .known (checkpoint, i)
          else .unknown .targetMismatch
  | .unknown e => .unknown e
  | .rejected e => .rejected e
  | .conflict a b => .conflict a b

/-- Edge 13 selection: the original selector reads the actual personal slot;
decoding reads its actual output bytes and binds the complete catalog item. -/
private theorem selected_checkpoint_reads_actual_catalog {m k : Nat}
    (catalog : Fin k → TrainingCandidate m) (state : RSI.State)
    (request : RSI.PredictionRequest) (query : Fin m)
    (population prior retrieved : Option RSI.Checkpoint)
    (checkpoint : RSI.Checkpoint) (i : Fin k)
    (selected : selectIndex catalog state request query population prior retrieved =
      .known (checkpoint, i)) :
    RSI.proposed_checkpoint_service request (state.personal request.principal)
        population prior retrieved = .known checkpoint ∧
      decodeIndex checkpoint.bytes = some i ∧
      validSelection catalog state request query checkpoint i := by
  cases source : RSI.proposed_checkpoint_service request (state.personal request.principal)
      population prior retrieved with
  | unknown e => simp [selectIndex, source] at selected
  | rejected e => simp [selectIndex, source] at selected
  | conflict a b => simp [selectIndex, source] at selected
  | known actual =>
      cases decoded : decodeIndex actual.bytes with
      | none =>
          simp only [selectIndex, source] at selected
          rw [decoded] at selected
          cases selected
      | some j =>
          by_cases valid : validSelection catalog state request query actual j
          · have same : (actual, j) = (checkpoint, i) := by
              simp only [selectIndex, source] at selected
              rw [decoded] at selected
              dsimp only at selected
              rw [if_pos valid] at selected
              exact Result.known.inj selected
            have checkpoints : actual = checkpoint := congrArg Prod.fst same
            have indices : j = i := congrArg Prod.snd same
            subst checkpoint
            subst i
            exact ⟨rfl, decoded, valid⟩
          · simp only [selectIndex, source] at selected
            rw [decoded] at selected
            dsimp only at selected
            rw [if_neg valid] at selected
            cases selected

structure LogMeaning (m : Nat) where
  log : Behavior.MeasurementLog
  caseId : CaseId
  feature : Fin m
  deriving DecidableEq, Repr

def interpretLog {m : Nat} (scope : DataScope) (meanings : List (LogMeaning m))
    (log : Behavior.MeasurementLog) : Result (Observation m) :=
  match Behavior.proposed_measurement scope.target log with
  | .known label =>
      if log.mechanismVersion ≠ scope.mechanismVersion then .unknown .targetMismatch
      else match meanings.filter (fun entry => decide (entry.log = log)) with
        | [] => .unknown .missingEvidence
        | [entry] => .known
            { scope := scope
              caseId := entry.caseId
              event := log.event
              measurement := log.unit
              record := log.record
              feature := entry.feature
              label := label
              source := log.externalSource
              origin := .external
              observedAt := log.observedAt }
        | _ => .unknown .unsupported
  | .unknown e => .unknown e
  | .rejected e => .rejected e
  | .conflict a b => .conflict a b

def interpretLogs {m : Nat} (scope : DataScope) (meanings : List (LogMeaning m)) :
    List Behavior.MeasurementLog → Result (List (Observation m))
  | [] => .known []
  | log :: rest =>
      match interpretLog scope meanings log with
      | .known row =>
          match interpretLogs scope meanings rest with
          | .known rows => .known (row :: rows)
          | .unknown e => .unknown e
          | .rejected e => .rejected e
          | .conflict a b => .conflict a b
      | .unknown e => .unknown e
      | .rejected e => .rejected e
      | .conflict a b => .conflict a b

def ingestRows {m : Nat} (now : Instant) :
    Store m → List (Observation m) → Result (Store m)
  | store, [] => .known store
  | store, row :: rest =>
      let receipt := applyChange now [] store (.observed row)
      if receipt.disposition = .inserted ∨ receipt.disposition = .replay then
        ingestRows now receipt.post rest
      else .unknown .missingEvidence

structure PersonalExchange (m : Nat) where
  round : AdaptiveRoundLedger20261027.RoundState m
  before : RSI.State
  query : Fin m
  evidence : SourceRef

def exchangeCatalog {m : Nat} (exchange : PersonalExchange m) :
    Fin 1 → TrainingCandidate m :=
  fun _ => readLoaded exchange.round.service

def producedCheckpoint {m : Nat} (exchange : PersonalExchange m) : RSI.Checkpoint :=
  checkpointFor (exchangeCatalog exchange) 0 exchange.round.service.principal
    exchange.query exchange.evidence

def producedState {m : Nat} (exchange : PersonalExchange m) : RSI.State :=
  RSI.prepareUpdate exchange.before
    (.personal exchange.round.service.principal (producedCheckpoint exchange))

/-- Edge 13: the actual personal producer reads the complete current Loaded
object. Its original RSI update preserves the actual data and legal frame;
this personal proposal does not authorize production loading. -/
theorem personal_producer_preserves_actual_frame {m : Nat}
    (exchange : PersonalExchange m) :
    exchangeCatalog exchange 0 = readLoaded exchange.round.service ∧
      decodeIndex (producedCheckpoint exchange).bytes = some (0 : Fin 1) ∧
      (producedState exchange).personal exchange.round.service.principal =
        some (producedCheckpoint exchange) ∧
      (producedState exchange).rules = exchange.before.rules ∧
      (producedState exchange).mechanism = exchange.before.mechanism ∧
      (producedState exchange).data = exchange.before.data ∧
      ∀ other, other ≠ exchange.round.service.principal →
        (producedState exchange).personal other = exchange.before.personal other := by
  have frame := RSI.u13_2_personal_frame exchange.before
    exchange.round.service.principal (producedCheckpoint exchange)
  refine ⟨rfl, index_codec_roundtrip 0, ?_, frame.1, frame.2.1,
    frame.2.2.1, frame.2.2.2⟩
  simp [producedState, RSI.prepareUpdate, RSI.updatePersonal]

structure NativeInput (m : Nat) where
  checkpoint : RSI.Checkpoint
  index : Fin 1
  rows : List (Observation m)
  reversePrefix : List (Observation m)
  last : Observation m
  journal : Store m

def prepareNativeInput {m : Nat} (exchange : PersonalExchange m)
    (request : RSI.PredictionRequest) (now : Instant)
    (meanings : List (LogMeaning m)) : Result (NativeInput m) :=
  if request.principal = exchange.round.service.principal then
    match selectIndex (exchangeCatalog exchange) (producedState exchange)
        request exchange.query none none none with
    | .known (checkpoint, i) =>
        match interpretLogs exchange.round.service.journal.scope meanings
            (producedState exchange).data with
        | .known rows =>
            match rows.reverse with
            | [] => .unknown .missingEvidence
            | last :: reversePrefix =>
                match ingestRows now exchange.round.service.journal reversePrefix.reverse with
                | .known journal =>
                    .known ⟨checkpoint, i, rows, reversePrefix, last, journal⟩
                | .unknown e => .unknown e
                | .rejected e => .rejected e
                | .conflict a b => .conflict a b
        | .unknown e => .unknown e
        | .rejected e => .rejected e
        | .conflict a b => .conflict a b
    | .unknown e => .unknown e
    | .rejected e => .rejected e
    | .conflict a b => .conflict a b
  else .unknown .scopeMismatch

def prefixRound {m : Nat} (exchange : PersonalExchange m) (input : NativeInput m) :
    AdaptiveRoundLedger20261027.RoundState m :=
  { exchange.round with
    service := { exchange.round.service with journal := input.journal } }

def nativeBegin {m : Nat} (exchange : PersonalExchange m) (input : NativeInput m)
    (now : Instant) (plan : ValidationPlan) :
    AdaptiveRoundLedger20261027.RoundState m :=
  AdaptiveRoundLedger20261027.beginAdaptiveRound (prefixRound exchange input) now []
    (.observed input.last) (exchangeCatalog exchange input.index).fitted.protocol plan

def startPersonalRound {m : Nat} (exchange : PersonalExchange m)
    (request : RSI.PredictionRequest) (now : Instant)
    (meanings : List (LogMeaning m)) (plan : ValidationPlan) :
    Result (AdaptiveRoundLedger20261027.RoundState m) :=
  if exchange.round.pending = none then
    if exchange.round.records.length < exchange.round.horizon then
      match prepareNativeInput exchange request now meanings with
      | .known input => .known (nativeBegin exchange input now plan)
      | .unknown e => .unknown e
      | .rejected e => .rejected e
      | .conflict a b => .conflict a b
    else .rejected .unsupported
  else .unknown .openMissingOpportunity

private theorem prepared_input_reads_actual_data {m : Nat}
    (exchange : PersonalExchange m) (request : RSI.PredictionRequest)
    (now : Instant) (meanings : List (LogMeaning m)) (input : NativeInput m)
    (known : prepareNativeInput exchange request now meanings = .known input) :
    request.principal = exchange.round.service.principal ∧
      selectIndex (exchangeCatalog exchange) (producedState exchange)
        request exchange.query none none none = .known (input.checkpoint, input.index) ∧
      interpretLogs exchange.round.service.journal.scope meanings
        (producedState exchange).data = .known input.rows ∧
      input.rows.reverse = input.last :: input.reversePrefix ∧
      ingestRows now exchange.round.service.journal input.reversePrefix.reverse =
        .known input.journal := by
  have principal : request.principal = exchange.round.service.principal := by
    by_contra different
    simp [prepareNativeInput, different] at known
  cases selected : selectIndex (exchangeCatalog exchange) (producedState exchange)
      request exchange.query none none none with
  | unknown e => simp [prepareNativeInput, principal, selected] at known
  | rejected e => simp [prepareNativeInput, principal, selected] at known
  | conflict a b => simp [prepareNativeInput, principal, selected] at known
  | known value =>
      rcases value with ⟨checkpoint, i⟩
      cases interpreted : interpretLogs exchange.round.service.journal.scope meanings
          (producedState exchange).data with
      | unknown e => simp [prepareNativeInput, principal, selected, interpreted] at known
      | rejected e => simp [prepareNativeInput, principal, selected, interpreted] at known
      | conflict a b => simp [prepareNativeInput, principal, selected, interpreted] at known
      | known rows =>
          cases reversed : rows.reverse with
          | nil => simp [prepareNativeInput, principal, selected, interpreted, reversed] at known
          | cons last reversePrefix =>
              cases ingested : ingestRows now exchange.round.service.journal reversePrefix.reverse with
              | unknown e =>
                  simp [prepareNativeInput, principal, selected, interpreted, reversed, ingested] at known
              | rejected e =>
                  simp [prepareNativeInput, principal, selected, interpreted, reversed, ingested] at known
              | conflict a b =>
                  simp [prepareNativeInput, principal, selected, interpreted, reversed, ingested] at known
              | known journal =>
                  have actual : input = ⟨checkpoint, i, rows, reversePrefix, last, journal⟩ := by
                    simpa [prepareNativeInput, principal, selected, interpreted, reversed, ingested]
                      using known.symm
                  subst input
                  exact ⟨principal, rfl, rfl, reversed, ingested⟩

private theorem started_round_reads_input {m : Nat}
    (exchange : PersonalExchange m) (request : RSI.PredictionRequest)
    (now : Instant) (meanings : List (LogMeaning m)) (plan : ValidationPlan)
    (native : AdaptiveRoundLedger20261027.RoundState m)
    (known : startPersonalRound exchange request now meanings plan = .known native) :
    ∃ input, exchange.round.pending = none ∧
      exchange.round.records.length < exchange.round.horizon ∧
      prepareNativeInput exchange request now meanings = .known input ∧
      native = nativeBegin exchange input now plan := by
  by_cases free : exchange.round.pending = none
  · by_cases room : exchange.round.records.length < exchange.round.horizon
    · cases prepared : prepareNativeInput exchange request now meanings with
      | unknown e => simp [startPersonalRound, free, room, prepared] at known
      | rejected e => simp [startPersonalRound, free, room, prepared] at known
      | conflict a b => simp [startPersonalRound, free, room, prepared] at known
      | known input =>
          refine ⟨input, free, room, rfl, ?_⟩
          simpa [startPersonalRound, free, room, prepared] using known.symm
    · simp [startPersonalRound, free, room] at known
  · simp [startPersonalRound, free] at known

/-- U00 L734/L756/L759, edge 13: the produced checkpoint is actually selected,
decoded to the complete current parent, and actual RSI data enter the current
journal before the last observation calls the original native generation entry. -/
theorem actual_personal_round_uses_native_entry {m : Nat}
    (exchange : PersonalExchange m) (request : RSI.PredictionRequest)
    (now : Instant) (meanings : List (LogMeaning m)) (plan : ValidationPlan)
    (native : AdaptiveRoundLedger20261027.RoundState m)
    (known : startPersonalRound exchange request now meanings plan = .known native) :
    ∃ input : NativeInput m,
      exchange.round.pending = none ∧
      exchange.round.records.length < exchange.round.horizon ∧
      prepareNativeInput exchange request now meanings = .known input ∧
      native = nativeBegin exchange input now plan ∧
      input.checkpoint = producedCheckpoint exchange ∧
      RSI.proposed_checkpoint_service request
        ((producedState exchange).personal request.principal) none none none =
          .known (producedCheckpoint exchange) ∧
      decodeIndex input.checkpoint.bytes = some input.index ∧
      exchangeCatalog exchange input.index = readLoaded exchange.round.service ∧
      interpretLogs exchange.round.service.journal.scope meanings exchange.before.data =
        .known input.rows ∧
      input.rows.reverse = input.last :: input.reversePrefix ∧
      ingestRows now exchange.round.service.journal input.reversePrefix.reverse =
        .known input.journal ∧
      readLoaded (prefixRound exchange input).service = readLoaded exchange.round.service := by
  obtain ⟨input, free, room, prepared, actual⟩ :=
    started_round_reads_input exchange request now meanings plan native known
  have data := prepared_input_reads_actual_data exchange request now meanings input prepared
  have selected := selected_checkpoint_reads_actual_catalog
    (exchangeCatalog exchange) (producedState exchange) request exchange.query
    none none none input.checkpoint input.index data.2.1
  have frame := personal_producer_preserves_actual_frame exchange
  have personal :
      (producedState exchange).personal request.principal =
        some (producedCheckpoint exchange) := by
    simpa only [data.1] using frame.2.2.1
  have source := selected.1
  have sameCheckpoint : input.checkpoint = producedCheckpoint exchange := by
    cases matchedCP : RSI.checkpointMatches request (producedCheckpoint exchange) with
    | false =>
        simp [RSI.proposed_checkpoint_service, personal, matchedCP] at source
    | true =>
        simpa [RSI.proposed_checkpoint_service, personal, matchedCP] using source.symm
  have dataSame : (producedState exchange).data = exchange.before.data :=
    frame.2.2.2.2.2.1
  refine ⟨input, free, room, prepared, actual, sameCheckpoint, ?_,
    selected.2.1, rfl, ?_, data.2.2.2.1, data.2.2.2.2, rfl⟩
  · simpa only [sameCheckpoint] using source
  · simpa only [dataSame] using data.2.2.1

private theorem known_prepared_candidate_reads_current_journal {m : Nat}
    (service : Service m) (now : Instant) (last : Observation m)
    (protocol : LearningProtocol) (proposals : List (List ℚ))
    (candidate : TrainingCandidate m)
    (known : (prepareNext service now [] (.observed last) protocol proposals).candidate =
      .known candidate) :
    candidate.snapshot =
        (prepareNext service now [] (.observed last) protocol proposals).post.journal ∧
      candidate.fitted.protocol = protocol ∧
      candidate.fitted.sampleSize =
        (trainingRows
          (prepareNext service now [] (.observed last) protocol proposals).post.journal).length := by
  have lossSame : protocol.lossVersion = service.lossVersion := by
    by_contra different
    simp [prepareNext, different] at known
  have link := next_candidate_consumes_current_loaded_and_actual_post
    service now [] (.observed last) protocol proposals lossSame
  have actual :
      (processAndFit now [] service.journal (.observed last) protocol binaryLoss
        ((readLoaded service).fitted.table :: proposals)).candidate = .known candidate :=
    link.2.2.1.symm.trans known
  have accepted :
      (applyChange now [] service.journal (.observed last)).disposition = .inserted ∨
      (applyChange now [] service.journal (.observed last)).disposition = .replay ∨
      (applyChange now [] service.journal (.observed last)).disposition = .corrected ∨
      (applyChange now [] service.journal (.observed last)).disposition = .withdrawn := by
    by_contra declined
    simp [processAndFit, declined] at actual
  rw [next_fit_consumes_actual_post now [] service.journal (.observed last)
    protocol binaryLoss ((readLoaded service).fitted.table :: proposals) accepted] at actual
  have fit := successful_fit_reads_current_valid_sample
    (applyChange now [] service.journal (.observed last)).post protocol binaryLoss
    ((readLoaded service).fitted.table :: proposals) candidate actual
  simp only [link.2.2.2.1]
  exact ⟨fit.1, fit.2.1, fit.2.2.1⟩

/-- U00 edge 13 enters the actual pending declaration. Native parent and family
are read from the current service and learner. Whenever its actual candidate is
known, its snapshot is the actual native journal, not the older Loaded snapshot. -/
theorem native_pending_binds_actual_parent_and_sample {m : Nat}
    (exchange : PersonalExchange m) (request : RSI.PredictionRequest)
    (now : Instant) (meanings : List (LogMeaning m)) (plan : ValidationPlan)
    (native : AdaptiveRoundLedger20261027.RoundState m)
    (known : startPersonalRound exchange request now meanings plan = .known native) :
    ∃ declaration : AdaptiveRoundLedger20261027.RoundDeclaration m,
      native.pending = some declaration ∧
      declaration.prepared.parent = readLoaded exchange.round.service ∧
      declaration.prepared.models =
        (readLoaded exchange.round.service).fitted.table :: exchange.round.learner.proposals ∧
      declaration.plan.models = declaration.prepared.models ∧
      native.service = declaration.prepared.post ∧
      ∀ candidate, declaration.prepared.candidate = .known candidate →
        candidate.snapshot = native.service.journal ∧
        candidate.fitted.protocol = (readLoaded exchange.round.service).fitted.protocol ∧
        candidate.fitted.sampleSize = (trainingRows native.service.journal).length := by
  obtain ⟨input, free, room, prepared, actual⟩ :=
    started_round_reads_input exchange request now meanings plan native known
  let prefixState := prefixRound exchange input
  let protocol := (exchangeCatalog exchange input.index).fitted.protocol
  let p := prepareNext prefixState.service now [] (.observed input.last)
    protocol prefixState.learner.proposals
  let declaration : AdaptiveRoundLedger20261027.RoundDeclaration m :=
    ⟨prefixState.learner, now, prefixState.records.length, p,
      { plan with models := (readLoaded prefixState.service).fitted.table :: prefixState.learner.proposals }⟩
  have freePrefix : prefixState.pending = none := free
  have roomPrefix : prefixState.records.length < prefixState.horizon := room
  have actualBegin :
      native = AdaptiveRoundLedger20261027.beginAdaptiveRound prefixState now []
        (.observed input.last) protocol plan := actual
  have generated := AdaptiveRoundLedger20261027.generation_uses_actual_loaded_and_learner
    prefixState now [] (.observed input.last) protocol plan freePrefix roomPrefix
  have pending : native.pending = some declaration := by
    rw [actualBegin]
    exact generated.1
  have post : native.service = p.post := by
    rw [actualBegin]
    simp [AdaptiveRoundLedger20261027.beginAdaptiveRound,
      freePrefix, Nat.not_le_of_lt roomPrefix, p]
  refine ⟨declaration, pending, rfl, rfl, rfl, post, ?_⟩
  intro candidate candidateKnown
  have properties := known_prepared_candidate_reads_current_journal
    prefixState.service now input.last protocol prefixState.learner.proposals candidate candidateKnown
  simpa only [post] using properties

end JurisLean.Candidates.U00RSICandidateBridge20261031
