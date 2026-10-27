import JurisLean.Candidates.SampleCalibrationConsumer20261027

/-!
Original 13 S14, 14 E14.1--E14.6 and question 14.1--14.2: event-keyed,
append-only observations, explicit conflict/correction/retraction, then actual
finite empirical fitting. Measurement and record identities are provenance,
not sample keys. The source and correction catalogs are external inputs;
matching their entries does not establish their real-world authority or truth.

This stage produces a candidate, not validation, acceptance or service loading.
Unique event keys do not establish statistical independence. Label meaning,
event identity and source reliability retain their external interpretations.
-/

namespace JurisLean.Candidates.EventFeedbackConsumer20261027

open JurisLean.Candidates.Final20261021
open JurisLean.Candidates.LearningConsumer20261027
open JurisLean.Candidates.LearningERM20261027
open JurisLean.Candidates.SampleCalibrationConsumer20261027

inductive LabelMeaning where
  | adoption | behavior | procedure | normative
  deriving DecidableEq, Repr

inductive Origin where
  | external | suggestion
  deriving DecidableEq, Repr

structure DataScope where
  task : Nat
  target : Nat
  featureVersion : Nat
  labelVersion : Nat
  population : Nat
  samplingDesign : Nat
  groupingVersion : Nat
  effectiveDomain : Nat
  mechanismVersion : Nat
  ruleVersion : Nat
  correctionPolicy : Nat
  meaning : LabelMeaning
  deriving DecidableEq, Repr

structure Observation (m : Nat) where
  scope : DataScope
  caseId : CaseId
  event : EventId
  measurement : MeasurementId
  record : RecordId
  feature : Fin m
  label : Bool
  source : SourceRef
  origin : Origin
  observedAt : Instant
  deriving DecidableEq, Repr

-- The caller supplies this registry from an independent external label source.
-- Equality checks its exact statement, not the reliability of that source.
structure ExternalConfirmation (m : Nat) where
  observation : Observation m
  witness : SourceRef
  deriving DecidableEq, Repr

inductive LabelState (m : Nat) where
  | active (feature : Fin m) (label : Bool)
  | conflicted
  | withdrawn
  deriving DecidableEq, Repr

structure Cell (m : Nat) where
  event : EventId
  caseId : CaseId
  revision : Nat
  state : LabelState m
  deriving DecidableEq, Repr

structure Correction (m : Nat) where
  supersedes : Cell m
  replacement : Option (Observation m)
  effectiveFrom : Instant
  policyVersion : Nat
  source : SourceRef
  deriving DecidableEq, Repr

structure CorrectionPermit (m : Nat) where
  scope : DataScope
  correction : Correction m
  validFrom : Instant
  validUntil : Instant
  authority : SourceRef
  deriving DecidableEq, Repr

inductive Change (m : Nat) where
  | observed (row : Observation m)
  | corrected (edit : Correction m)
  deriving DecidableEq, Repr

structure Store (m : Nat) where
  scope : DataScope
  confirmations : List (ExternalConfirmation m)
  history : List (Change m)
  cells : List (Cell m)
  deriving DecidableEq, Repr

inductive Disposition where
  | inserted | replay | conflict | quarantined | corrected | withdrawn
  | invalidObservation | staleCorrection | invalidCorrection | authorityUnresolved
  deriving DecidableEq, Repr

structure Receipt (m : Nat) where
  disposition : Disposition
  post : Store m
  deriving DecidableEq, Repr

def emptyStore (m : Nat) (scope : DataScope)
    (confirmations : List (ExternalConfirmation m)) : Store m := ⟨scope, confirmations, [], []⟩

def lookup {m : Nat} (s : Store m) (event : EventId) : Option (Cell m) :=
  s.cells.find? (fun cell => decide (cell.event = event))

def putCell {m : Nat} (cells : List (Cell m)) (cell : Cell m) : List (Cell m) :=
  cell :: cells.filter (fun old => decide (old.event ≠ cell.event))

def recordOnly {m : Nat} (s : Store m) (change : Change m) : Store m :=
  { s with history := s.history ++ [change] }

def recordCell {m : Nat} (s : Store m) (change : Change m) (cell : Cell m) : Store m :=
  { s with history := s.history ++ [change], cells := putCell s.cells cell }

def seenObservation {m : Nat} (s : Store m) (row : Observation m) : Bool :=
  s.history.any fun change => match change with
    | .observed old => decide (old = row)
    | .corrected edit => decide (edit.replacement = some row)

def sourceConfirmed {m : Nat} (s : Store m) (row : Observation m) : Bool :=
  s.confirmations.any (fun evidence => decide (evidence.observation = row))

def observationValid {m : Nat} (s : Store m) (now : Instant) (row : Observation m) : Bool :=
  decide (row.scope = s.scope ∧ row.origin = .external ∧ row.observedAt.ticks ≤ now.ticks) &&
    sourceConfirmed s row

def observe {m : Nat} (s : Store m) (now : Instant) (row : Observation m) : Receipt m :=
  if observationValid s now row = false then ⟨.invalidObservation, s⟩
  else if seenObservation s row then ⟨.replay, recordOnly s (.observed row)⟩
  else match lookup s row.event with
    | none => ⟨.inserted, recordCell s (.observed row)
        ⟨row.event, row.caseId, 0, .active row.feature row.label⟩⟩
    | some old =>
        if old.caseId = row.caseId ∧ old.state = .active row.feature row.label then
          ⟨.replay, recordOnly s (.observed row)⟩
        else if old.state = .conflicted ∨ old.state = .withdrawn then
          ⟨.quarantined, recordOnly s (.observed row)⟩
        else ⟨.conflict, recordCell s (.observed row)
          { old with revision := old.revision + 1, state := .conflicted }⟩

def correctionValid {m : Nat} (s : Store m) (now : Instant) (edit : Correction m) : Bool :=
  decide (edit.policyVersion = s.scope.correctionPolicy ∧ edit.effectiveFrom.ticks ≤ now.ticks) &&
  match edit.replacement with
  | none => true
  | some row => observationValid s now row &&
      decide (row.event = edit.supersedes.event ∧ row.caseId = edit.supersedes.caseId)

def correctionAuthorized {m : Nat} (s : Store m) (now : Instant)
    (permits : List (CorrectionPermit m)) (edit : Correction m) : Bool :=
  permits.any fun permit => decide (permit.scope = s.scope ∧ permit.correction = edit ∧
    permit.validFrom.ticks ≤ now.ticks ∧ now.ticks < permit.validUntil.ticks)

def correctedCell {m : Nat} (edit : Correction m) : Cell m :=
  { edit.supersedes with
    revision := edit.supersedes.revision + 1
    state := match edit.replacement with
      | none => .withdrawn
      | some row => .active row.feature row.label }

def correct {m : Nat} (s : Store m) (now : Instant)
    (permits : List (CorrectionPermit m)) (edit : Correction m) : Receipt m :=
  if s.history.contains (.corrected edit) then
    ⟨.replay, recordOnly s (.corrected edit)⟩
  else if lookup s edit.supersedes.event ≠ some edit.supersedes then ⟨.staleCorrection, s⟩
  else if correctionValid s now edit = false then ⟨.invalidCorrection, s⟩
  else if correctionAuthorized s now permits edit = false then ⟨.authorityUnresolved, s⟩
  else ⟨(if edit.replacement.isSome then .corrected else .withdrawn),
    recordCell s (.corrected edit) (correctedCell edit)⟩

def applyChange {m : Nat} (now : Instant) (permits : List (CorrectionPermit m))
    (s : Store m) (change : Change m) : Receipt m :=
  match change with
  | .observed row => observe s now row
  | .corrected edit => correct s now permits edit

def runChanges {m : Nat} (now : Instant) (permits : List (CorrectionPermit m))
    (s : Store m) : List (Change m) → Store m
  | [] => s
  | change :: rest => runChanges now permits (applyChange now permits s change).post rest

def Unique {m : Nat} (s : Store m) : Prop :=
  s.cells.Pairwise (fun a b => a.event ≠ b.event)

def Cell.toSample {m : Nat} (cell : Cell m) : Option (SampleObservation m Bool) :=
  match cell.state with
  | .active feature label => some ⟨cell.event, feature, label⟩
  | .conflicted | .withdrawn => none

def trainingRows {m : Nat} (s : Store m) : List (SampleObservation m Bool) :=
  s.cells.filterMap Cell.toSample

def trainingData {m : Nat} (s : Store m) : Fin (trainingRows s).length → Fin m × Bool :=
  fun i => let row := (trainingRows s).get i; (row.feature, row.label)

def protocolMatches (scope : DataScope) (protocol : LearningProtocol) : Bool :=
  decide (scope.task = protocol.fit.task ∧ scope.target = protocol.fit.target ∧
    scope.featureVersion = protocol.fit.featureVersion ∧ scope.labelVersion = protocol.labelVersion ∧
    scope.population = protocol.population ∧ scope.samplingDesign = protocol.samplingDesign ∧
    scope.groupingVersion = protocol.groupingVersion ∧ scope.effectiveDomain = protocol.effectiveDomain)

structure TrainingCandidate (m : Nat) where
  snapshot : Store m
  fitted : FittedTable
  deriving DecidableEq, Repr

def fitFromStore {m : Nat} (s : Store m) (protocol : LearningProtocol)
    (loss : ℚ → Bool → ℚ) (models : List (List ℚ)) : Result (TrainingCandidate m) :=
  if protocolMatches s.scope protocol = false then .unknown .targetMismatch
  else match fitTable protocol loss models (trainingData s) with
    | .known fitted => .known ⟨s, fitted⟩
    | .unknown e => .unknown e
    | .rejected e => .rejected e
    | .conflict a b => .conflict a b

structure CandidateRun (m : Nat) where
  observation : Receipt m
  candidate : Result (TrainingCandidate m)
  deriving DecidableEq, Repr

def processAndFit {m : Nat} (now : Instant) (permits : List (CorrectionPermit m))
    (s : Store m) (change : Change m) (protocol : LearningProtocol)
    (loss : ℚ → Bool → ℚ) (models : List (List ℚ)) : CandidateRun m :=
  let receipt := applyChange now permits s change
  { observation := receipt
    candidate := if receipt.disposition = .inserted ∨ receipt.disposition = .replay ∨
        receipt.disposition = .corrected ∨ receipt.disposition = .withdrawn then
      fitFromStore receipt.post protocol loss models
      else .unknown .missingEvidence }

-- List APIs checked in Lean v4.30.0, Init/Data/List/Pairwise.lean, 143--154.
theorem putCell_unique {m : Nat} (cells : List (Cell m)) (cell : Cell m)
    (unique : cells.Pairwise (fun a b => a.event ≠ b.event)) :
    (putCell cells cell).Pairwise (fun a b => a.event ≠ b.event) := by
  apply List.pairwise_cons.mpr
  constructor
  · intro old hold
    have different : old.event ≠ cell.event := by
      simpa using (List.mem_filter.mp hold).2
    exact Ne.symm different
  · exact unique.filter _

theorem observe_preserves_event_uniqueness {m : Nat} (s : Store m)
    (now : Instant) (row : Observation m) (unique : Unique s) :
    Unique (observe s now row).post := by
  unfold observe
  split
  · exact unique
  · split
    · exact unique
    · split
      · exact putCell_unique _ _ unique
      · split
        · exact unique
        · split
          · exact unique
          · exact putCell_unique _ _ unique

theorem correction_preserves_event_uniqueness {m : Nat} (s : Store m)
    (now : Instant) (permits : List (CorrectionPermit m)) (edit : Correction m)
    (unique : Unique s) : Unique (correct s now permits edit).post := by
  unfold correct
  split
  · exact unique
  · split
    · exact unique
    · split
      · exact unique
      · split
        · exact unique
        · exact putCell_unique _ _ unique

theorem finite_updates_keep_one_cell_per_event {m : Nat} (now : Instant)
    (permits : List (CorrectionPermit m)) (s : Store m) (changes : List (Change m))
    (unique : Unique s) : Unique (runChanges now permits s changes) := by
  induction changes generalizing s with
  | nil => exact unique
  | cons change rest ih =>
      apply ih
      cases change with
      | observed row => exact observe_preserves_event_uniqueness s now row unique
      | corrected edit => exact correction_preserves_event_uniqueness s now permits edit unique

theorem training_contains_no_repeated_event {m : Nat} (s : Store m) (unique : Unique s) :
    (trainingRows s).Pairwise (fun a b => a.event ≠ b.event) := by
  apply unique.filterMap Cell.toSample
  intro a b different sa ha sb hb
  cases hsa : a.state <;> cases hsb : b.state <;>
    simp [Cell.toSample, hsa, hsb] at ha hb
  cases ha
  cases hb
  exact different

theorem observed_history_is_append_only {m : Nat} (s : Store m) (now : Instant)
    (row : Observation m) :
    ∃ suffix, (observe s now row).post.history = s.history ++ suffix := by
  unfold observe
  split
  · exact ⟨[], by simp⟩
  · split
    · exact ⟨[.observed row], rfl⟩
    · split
      · exact ⟨[.observed row], rfl⟩
      · split
        · exact ⟨[.observed row], rfl⟩
        · split <;> exact ⟨[.observed row], rfl⟩

theorem corrected_history_is_append_only {m : Nat} (s : Store m) (now : Instant)
    (permits : List (CorrectionPermit m)) (edit : Correction m) :
    ∃ suffix, (correct s now permits edit).post.history = s.history ++ suffix := by
  unfold correct
  split
  · exact ⟨[.corrected edit], rfl⟩
  · split
    · exact ⟨[], by simp⟩
    · split
      · exact ⟨[], by simp⟩
      · split
        · exact ⟨[], by simp⟩
        · exact ⟨[.corrected edit], rfl⟩

theorem suggestions_do_not_enter_training {m : Nat} (s : Store m) (now : Instant)
    (row : Observation m) (suggestion : row.origin = .suggestion) :
    observe s now row = ⟨.invalidObservation, s⟩ := by
  simp [observe, observationValid, suggestion]

theorem unconfirmed_labels_do_not_enter_training {m : Nat} (s : Store m) (now : Instant)
    (row : Observation m) (missing : sourceConfirmed s row = false) :
    observe s now row = ⟨.invalidObservation, s⟩ := by
  simp [observe, observationValid, missing]

theorem replay_has_no_extra_training_row {m : Nat} (s : Store m) (now : Instant)
    (row : Observation m) (old : Cell m) (valid : observationValid s now row = true)
    (found : lookup s row.event = some old)
    (same : old.caseId = row.caseId ∧ old.state = .active row.feature row.label) :
    (observe s now row).disposition = .replay ∧
      trainingRows (observe s now row).post = trainingRows s := by
  by_cases seen : seenObservation s row = true <;>
    simp [observe, valid, seen, found, same, recordOnly, trainingRows]

theorem historical_replay_cannot_revive_superseded_label {m : Nat} (s : Store m)
    (now : Instant) (row : Observation m) (valid : observationValid s now row = true)
    (seen : seenObservation s row = true) :
    (observe s now row).post.cells = s.cells := by
  simp [observe, valid, seen, recordOnly]

theorem denied_correction_keeps_current_state {m : Nat} (s : Store m) (now : Instant)
    (permits : List (CorrectionPermit m)) (edit : Correction m)
    (fresh : s.history.contains (.corrected edit) = false)
    (found : lookup s edit.supersedes.event = some edit.supersedes)
    (valid : correctionValid s now edit = true)
    (denied : correctionAuthorized s now permits edit = false) :
    correct s now permits edit = ⟨.authorityUnresolved, s⟩ := by
  have fresh' : Change.corrected edit ∉ s.history := by simpa using fresh
  simp [correct, fresh', found, valid, denied]

theorem approved_correction_replaces_exact_prior {m : Nat} (s : Store m) (now : Instant)
    (permits : List (CorrectionPermit m)) (edit : Correction m)
    (fresh : s.history.contains (.corrected edit) = false)
    (found : lookup s edit.supersedes.event = some edit.supersedes)
    (valid : correctionValid s now edit = true)
    (allowed : correctionAuthorized s now permits edit = true) :
    lookup (correct s now permits edit).post edit.supersedes.event = some (correctedCell edit) ∧
      (correct s now permits edit).post.history = s.history ++ [.corrected edit] := by
  have fresh' : Change.corrected edit ∉ s.history := by simpa using fresh
  have transition : (correct s now permits edit).post =
      recordCell s (.corrected edit) (correctedCell edit) := by
    simp [correct, fresh', found, valid, allowed]
  rw [transition]
  constructor
  · simp [lookup, recordCell, putCell, correctedCell]
  · rfl

theorem successful_fit_reads_current_valid_sample {m : Nat} (s : Store m)
    (protocol : LearningProtocol) (loss : ℚ → Bool → ℚ) (models : List (List ℚ))
    (out : TrainingCandidate m) (accepted : fitFromStore s protocol loss models = .known out) :
    out.snapshot = s ∧ out.fitted.protocol = protocol ∧
      out.fitted.sampleSize = (trainingRows s).length ∧ out.fitted.table.length = m ∧
      out.fitted.table ∈ models ∧
      out.fitted.empiricalRisk = empiricalScore (tableLoss loss) (trainingData s) out.fitted.table ∧
      ∀ table ∈ models, empiricalScore (tableLoss loss) (trainingData s) out.fitted.table ≤
        empiricalScore (tableLoss loss) (trainingData s) table := by
  unfold fitFromStore at accepted
  split at accepted
  · cases accepted
  · cases hfit : fitTable protocol loss models (trainingData s) with
    | known fitted =>
        simp only [hfit] at accepted
        cases accepted
        exact ⟨rfl, u01_6_fit_card_minimizes_actual_sample protocol loss models
          (trainingData s) fitted hfit⟩
    | unknown e => simp [hfit] at accepted
    | rejected e => simp [hfit] at accepted
    | conflict a b => simp [hfit] at accepted

theorem next_fit_consumes_actual_post {m : Nat} (now : Instant)
    (permits : List (CorrectionPermit m)) (s : Store m) (change : Change m)
    (protocol : LearningProtocol) (loss : ℚ → Bool → ℚ) (models : List (List ℚ))
    (accepted : (applyChange now permits s change).disposition = .inserted ∨
      (applyChange now permits s change).disposition = .replay ∨
      (applyChange now permits s change).disposition = .corrected ∨
      (applyChange now permits s change).disposition = .withdrawn) :
    (processAndFit now permits s change protocol loss models).candidate =
      fitFromStore (applyChange now permits s change).post protocol loss models := by
  simp [processAndFit, accepted]

end JurisLean.Candidates.EventFeedbackConsumer20261027
