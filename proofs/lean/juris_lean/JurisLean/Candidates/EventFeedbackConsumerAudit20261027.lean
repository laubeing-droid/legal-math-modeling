import JurisLean.Candidates.EventFeedbackConsumer20261027

#check JurisLean.Candidates.EventFeedbackConsumer20261027.putCell_unique
#print axioms JurisLean.Candidates.EventFeedbackConsumer20261027.putCell_unique
#check JurisLean.Candidates.EventFeedbackConsumer20261027.observe_preserves_event_uniqueness
#print axioms JurisLean.Candidates.EventFeedbackConsumer20261027.observe_preserves_event_uniqueness
#check JurisLean.Candidates.EventFeedbackConsumer20261027.correction_preserves_event_uniqueness
#print axioms JurisLean.Candidates.EventFeedbackConsumer20261027.correction_preserves_event_uniqueness
#check JurisLean.Candidates.EventFeedbackConsumer20261027.finite_updates_keep_one_cell_per_event
#print axioms JurisLean.Candidates.EventFeedbackConsumer20261027.finite_updates_keep_one_cell_per_event
#check JurisLean.Candidates.EventFeedbackConsumer20261027.training_contains_no_repeated_event
#print axioms JurisLean.Candidates.EventFeedbackConsumer20261027.training_contains_no_repeated_event
#check JurisLean.Candidates.EventFeedbackConsumer20261027.observed_history_is_append_only
#print axioms JurisLean.Candidates.EventFeedbackConsumer20261027.observed_history_is_append_only
#check JurisLean.Candidates.EventFeedbackConsumer20261027.corrected_history_is_append_only
#print axioms JurisLean.Candidates.EventFeedbackConsumer20261027.corrected_history_is_append_only
#check JurisLean.Candidates.EventFeedbackConsumer20261027.suggestions_do_not_enter_training
#print axioms JurisLean.Candidates.EventFeedbackConsumer20261027.suggestions_do_not_enter_training
#check JurisLean.Candidates.EventFeedbackConsumer20261027.unconfirmed_labels_do_not_enter_training
#print axioms JurisLean.Candidates.EventFeedbackConsumer20261027.unconfirmed_labels_do_not_enter_training
#check JurisLean.Candidates.EventFeedbackConsumer20261027.replay_has_no_extra_training_row
#print axioms JurisLean.Candidates.EventFeedbackConsumer20261027.replay_has_no_extra_training_row
#check JurisLean.Candidates.EventFeedbackConsumer20261027.historical_replay_cannot_revive_superseded_label
#print axioms JurisLean.Candidates.EventFeedbackConsumer20261027.historical_replay_cannot_revive_superseded_label
#check JurisLean.Candidates.EventFeedbackConsumer20261027.denied_correction_keeps_current_state
#print axioms JurisLean.Candidates.EventFeedbackConsumer20261027.denied_correction_keeps_current_state
#check JurisLean.Candidates.EventFeedbackConsumer20261027.approved_correction_replaces_exact_prior
#print axioms JurisLean.Candidates.EventFeedbackConsumer20261027.approved_correction_replaces_exact_prior
#check JurisLean.Candidates.EventFeedbackConsumer20261027.successful_fit_reads_current_valid_sample
#print axioms JurisLean.Candidates.EventFeedbackConsumer20261027.successful_fit_reads_current_valid_sample
#check JurisLean.Candidates.EventFeedbackConsumer20261027.next_fit_consumes_actual_post
#print axioms JurisLean.Candidates.EventFeedbackConsumer20261027.next_fit_consumes_actual_post

open JurisLean.Candidates.Final20261021
open JurisLean.Candidates.LearningConsumer20261027
open JurisLean.Candidates.EventFeedbackConsumer20261027

namespace EventFeedbackFixture

def protocol : LearningProtocol :=
  ⟨⟨1, 2, 3, 4, 5, ⟨10⟩, ⟨1⟩⟩, 6, 7, 8, 9, 10, 11, 12, 1/10⟩

def scope : DataScope := ⟨1, 2, 3, 6, 8, 9, 10, 12, 1, 1, 1, .behavior⟩

def row (label : Bool) (event measurement record : Nat) : Observation 1 :=
  ⟨scope, ⟨1⟩, ⟨event⟩, ⟨measurement⟩, ⟨record⟩, 0, label, ⟨record⟩, .external, ⟨0⟩⟩

def first : Observation 1 := row false 1 10 100
def confirmations : List (ExternalConfirmation 1) :=
  ([first, row true 1 11 101, row true 1 12 102, row true 1 13 103,
    { row true 1 12 102 with caseId := ⟨2⟩ }] ++
    (List.range 100).map (fun i => row false 1 i (100 + i)) ++
    (List.range 100).map (fun i => row false i 1 (100 + i))).map
      (fun observed => ⟨observed, ⟨10000 + observed.record.value⟩⟩)
def initial : Store 1 := emptyStore 1 scope confirmations
def one : Store 1 := (observe initial ⟨10⟩ first).post
def oneCell : Cell 1 := ⟨⟨1⟩, ⟨1⟩, 0, .active 0 false⟩
def edit : Correction 1 := ⟨oneCell, some (row true 1 11 101), ⟨5⟩, 1, ⟨500⟩⟩
def permit (e : Correction 1) : CorrectionPermit 1 := ⟨scope, e, ⟨0⟩, ⟨20⟩, ⟨900⟩⟩
def corrected : Store 1 := (correct one ⟨10⟩ [permit edit] edit).post

def loss (score : ℚ) (truth : Bool) : ℚ :=
  if (score = 1 ↔ truth = true) then 0 else 1

def fittedValue (s : Store 1) : Result (List ℚ × Nat) :=
  match fitFromStore s protocol loss [[0], [1]] with
  | .known candidate => .known (candidate.fitted.table, candidate.fitted.sampleSize)
  | .unknown e => .unknown e
  | .rejected e => .rejected e
  | .conflict a b => .conflict a b

-- A real candidate is fitted from the single externally observed false label.
/-- info: true -/
#guard_msgs in
#eval decide (fittedValue one = Result.known ([0], 1))

-- One event with 100 distinct measurement/record references remains one row.
/-- info: true -/
#guard_msgs in
#eval
  let repeated := runChanges ⟨10⟩ [] initial
    ((List.range 100).map fun i => Change.observed (row false 1 i (100 + i)))
  decide (repeated.history.length = 100 ∧ repeated.cells.length = 1 ∧
    fittedValue repeated = Result.known ([0], 1))

-- Different event identities give 100 rows, without asserting independence.
/-- info: true -/
#guard_msgs in
#eval
  let distinct := runChanges ⟨10⟩ [] initial
    ((List.range 100).map fun i => Change.observed (row false i 1 (100 + i)))
  decide (distinct.history.length = 100 ∧ distinct.cells.length = 100 ∧
    fittedValue distinct = Result.known ([0], 100))

/-- info: true -/
#guard_msgs in
#eval decide (observe initial ⟨10⟩ { first with origin := Origin.suggestion } =
  (⟨Disposition.invalidObservation, initial⟩ : Receipt 1))

-- Merely claiming an external origin without a matching confirmation is refused.
/-- info: true -/
#guard_msgs in
#eval decide (observe initial ⟨10⟩ (row true 1 999 999) =
  (⟨Disposition.invalidObservation, initial⟩ : Receipt 1))

-- Conflicting evidence is retained, and the event leaves the training view.
/-- info: true -/
#guard_msgs in
#eval
  let conflict := observe one ⟨10⟩ (row true 1 12 102)
  decide (conflict.disposition = Disposition.conflict ∧ conflict.post.history.length = 2 ∧
    trainingRows conflict.post = [] ∧
    fittedValue conflict.post = Result.unknown Error.missingEvidence)

-- Actual approved post-correction labels change the actual selected table.
/-- info: true -/
#guard_msgs in
#eval
  let run := processAndFit ⟨10⟩ [permit edit] one (.corrected edit) protocol loss [[0], [1]]
  match run.candidate with
  | .known candidate => decide (run.observation.disposition = Disposition.corrected ∧
      candidate.snapshot = corrected ∧ candidate.snapshot.history.length = 2 ∧
      candidate.fitted.table = [1] ∧ candidate.fitted.sampleSize = 1)
  | _ => false

-- A historical old observation cannot undo the authorized correction.
/-- info: true -/
#guard_msgs in
#eval
  let replayed := observe corrected ⟨10⟩ first
  decide (replayed.disposition = Disposition.replay ∧ replayed.post.history.length = 3 ∧
    fittedValue replayed.post = Result.known ([1], 1))

-- The same correction is a replay even though its prior has been superseded.
/-- info: true -/
#guard_msgs in
#eval
  let replayed := correct corrected ⟨10⟩ [permit edit] edit
  decide (replayed.disposition = Disposition.replay ∧ replayed.post.cells = corrected.cells)

/-- info: true -/
#guard_msgs in
#eval decide (correct one ⟨10⟩ [] edit =
  (⟨Disposition.authorityUnresolved, one⟩ : Receipt 1))

/-- info: true -/
#guard_msgs in
#eval decide (correct one ⟨20⟩ [permit edit] edit =
  (⟨Disposition.authorityUnresolved, one⟩ : Receipt 1))

/-- info: true -/
#guard_msgs in
#eval decide (correct one ⟨4⟩ [permit edit] edit =
  (⟨Disposition.invalidCorrection, one⟩ : Receipt 1))

-- Retraction preserves both records but removes the label from the next fit.
/-- info: true -/
#guard_msgs in
#eval
  let retract : Correction 1 := { edit with replacement := none }
  let withdrawn := correct one ⟨10⟩ [permit retract] retract
  decide (withdrawn.disposition = Disposition.withdrawn ∧ withdrawn.post.history.length = 2 ∧
    fittedValue withdrawn.post = Result.unknown Error.missingEvidence)

-- Ordinary fresh evidence cannot bypass a prior withdrawal.
/-- info: true -/
#guard_msgs in
#eval
  let retract : Correction 1 := { edit with replacement := none }
  let withdrawn := correct one ⟨10⟩ [permit retract] retract
  let attempted := observe withdrawn.post ⟨10⟩ (row true 1 13 103)
  decide (attempted.disposition = Disposition.quarantined ∧ trainingRows attempted.post = [])

-- Resolving a conflict requires authorization for the exact conflicted prior.
/-- info: true -/
#guard_msgs in
#eval
  let conflict := observe one ⟨10⟩ (row true 1 12 102)
  let resolution : Correction 1 :=
    { edit with supersedes := { oneCell with revision := 1, state := LabelState.conflicted } }
  let resolved := correct conflict.post ⟨10⟩ [permit resolution] resolution
  decide (resolved.disposition = Disposition.corrected ∧ resolved.post.history.length = 3 ∧
    fittedValue resolved.post = Result.known ([1], 1) ∧
    (correct conflict.post ⟨10⟩ [permit edit] edit).disposition = Disposition.staleCorrection)

-- A change from behavior to adoption is a scope change, not a better label.
/-- info: true -/
#guard_msgs in
#eval decide (observe one ⟨10⟩ { first with scope := { scope with meaning := LabelMeaning.adoption } } =
  (⟨Disposition.invalidObservation, one⟩ : Receipt 1))

-- An event claiming another case is a conflict; an authorized edit still cannot relabel its case.
/-- info: true -/
#guard_msgs in
#eval
  let otherCase : Observation 1 := { row true 1 12 102 with caseId := ⟨2⟩ }
  let changedCase : Correction 1 := { edit with replacement := some otherCase }
  decide ((observe one ⟨10⟩ otherCase).disposition = Disposition.conflict ∧
    (correct one ⟨10⟩ [permit changedCase] changedCase).disposition = Disposition.invalidCorrection)

-- Different target versions cannot inherit the fitted training semantics.
/-- info: true -/
#guard_msgs in
#eval decide (fitFromStore one { protocol with fit := { protocol.fit with target := 99 } }
  loss [[0], [1]] = Result.unknown Error.targetMismatch)

end EventFeedbackFixture
