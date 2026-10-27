import JurisLean.Candidates.EventFeedbackConsumer20261027

/-!
Original 14.1 / correction S14: fixed target and externally reliable labels.
Reliability is explicitly about the supplied external confirmations and an
interpreted target, not about model self-evaluation. The executable update
sequence is then proved to preserve that target for every active label.
Nothing here proves a real source truthful, a normative target lawful, or
distinct event identifiers statistically independent.
-/

namespace JurisLean.Candidates.FeedbackLabelSemantics20261027

open JurisLean.Candidates.Final20261021
open JurisLean.Candidates.LearningConsumer20261027
open JurisLean.Candidates.LearningERM20261027
open JurisLean.Candidates.EventFeedbackConsumer20261027

abbrev Target (m : Nat) := DataScope → CaseId → EventId → Fin m → Bool

def Reliable {m : Nat} (s : Store m) (target : Target m) : Prop :=
  ∀ evidence ∈ s.confirmations, evidence.observation.scope = s.scope →
    evidence.observation.label = target s.scope evidence.observation.caseId
      evidence.observation.event evidence.observation.feature

def CellMeaning {m : Nat} (scope : DataScope) (target : Target m) (cell : Cell m) : Prop :=
  ∀ feature label, cell.state = .active feature label →
    label = target scope cell.caseId cell.event feature

def StoreMeaning {m : Nat} (s : Store m) (target : Target m) : Prop :=
  ∀ cell ∈ s.cells, CellMeaning s.scope target cell

theorem confirmed_observation_has_fixed_target {m : Nat} (s : Store m) (now : Instant)
    (row : Observation m) (target : Target m) (reliable : Reliable s target)
    (valid : observationValid s now row = true) :
    row.scope = s.scope ∧ row.label = target s.scope row.caseId row.event row.feature := by
  have checks : (row.scope = s.scope ∧ row.origin = .external ∧
      row.observedAt.ticks ≤ now.ticks) ∧ sourceConfirmed s row = true := by
    simpa [observationValid] using valid
  have scope : row.scope = s.scope := checks.1.1
  have confirmed : ∃ evidence ∈ s.confirmations, evidence.observation = row := by
    simpa [sourceConfirmed] using checks.2
  obtain ⟨evidence, member, same⟩ := confirmed
  refine ⟨scope, ?_⟩
  have truth := reliable evidence member (by simpa only [same] using scope)
  simpa only [same] using truth

theorem record_cell_preserves_target {m : Nat} (s : Store m) (change : Change m)
    (cell : Cell m) (target : Target m) (old : StoreMeaning s target)
    (inserted : CellMeaning s.scope target cell) :
    StoreMeaning (recordCell s change cell) target := by
  intro item member
  change item ∈ putCell s.cells cell at member
  simp only [putCell, List.mem_cons] at member
  rcases member with same | prior
  · subst item
    exact inserted
  · exact old item (List.mem_filter.mp prior).1

theorem observation_updates_preserve_target {m : Nat} (s : Store m) (now : Instant)
    (row : Observation m) (target : Target m) (reliable : Reliable s target)
    (old : StoreMeaning s target) : StoreMeaning (observe s now row).post target := by
  unfold observe
  split
  · exact old
  · rename_i valid
    have checked : observationValid s now row = true := by
      cases h : observationValid s now row <;> simp_all
    have truth := (confirmed_observation_has_fixed_target s now row target reliable checked).2
    split
    · exact old
    · split
      · apply record_cell_preserves_target _ _ _ _ old
        intro feature label same
        cases same
        exact truth
      · split
        · exact old
        · split
          · exact old
          · apply record_cell_preserves_target _ _ _ _ old
            intro feature label same
            cases same

theorem valid_correction_has_fixed_target {m : Nat} (s : Store m) (now : Instant)
    (edit : Correction m) (target : Target m) (reliable : Reliable s target)
    (valid : correctionValid s now edit = true) :
    CellMeaning s.scope target (correctedCell edit) := by
  cases replacement : edit.replacement with
  | none =>
      intro feature label same
      simp [correctedCell, replacement] at same
  | some row =>
      have details : (edit.policyVersion = s.scope.correctionPolicy ∧
          edit.effectiveFrom.ticks ≤ now.ticks) ∧
          observationValid s now row = true ∧
          row.event = edit.supersedes.event ∧ row.caseId = edit.supersedes.caseId := by
        simpa [correctionValid, replacement] using valid
      have checked := details.2
      have identity := checked.2
      have truth := (confirmed_observation_has_fixed_target s now row target reliable checked.1).2
      intro feature label same
      simp only [correctedCell, replacement, LabelState.active.injEq] at same
      rcases same with ⟨rfl, rfl⟩
      simpa only [identity.1, identity.2] using truth

theorem corrections_preserve_target {m : Nat} (s : Store m) (now : Instant)
    (permits : List (CorrectionPermit m)) (edit : Correction m) (target : Target m)
    (reliable : Reliable s target) (old : StoreMeaning s target) :
    StoreMeaning (correct s now permits edit).post target := by
  unfold correct
  split
  · exact old
  · split
    · exact old
    · split
      · exact old
      · rename_i valid
        have checked : correctionValid s now edit = true := by
          cases h : correctionValid s now edit <;> simp_all
        split
        · exact old
        · exact record_cell_preserves_target _ _ _ _ old
            (valid_correction_has_fixed_target s now edit target reliable checked)

theorem update_keeps_target_scope_and_external_catalog {m : Nat} (now : Instant)
    (permits : List (CorrectionPermit m)) (s : Store m) (change : Change m) :
    (applyChange now permits s change).post.scope = s.scope ∧
      (applyChange now permits s change).post.confirmations = s.confirmations := by
  cases change with
  | observed row =>
      cases found : lookup s row.event <;>
        simp only [applyChange, observe, found] <;>
        split_ifs <;> exact ⟨rfl, rfl⟩
  | corrected edit =>
      simp only [applyChange, correct]
      split_ifs <;> exact ⟨rfl, rfl⟩

theorem finite_feedback_preserves_fixed_target {m : Nat} (now : Instant)
    (permits : List (CorrectionPermit m)) (s : Store m) (changes : List (Change m))
    (target : Target m) (reliable : Reliable s target) (old : StoreMeaning s target) :
    StoreMeaning (runChanges now permits s changes) target := by
  induction changes generalizing s with
  | nil => exact old
  | cons change rest ih =>
      apply ih
      · have frame := update_keeps_target_scope_and_external_catalog now permits s change
        simpa only [Reliable, frame.1, frame.2] using reliable
      · cases change with
        | observed row => exact observation_updates_preserve_target s now row target reliable old
        | corrected edit => exact corrections_preserve_target s now permits edit target reliable old

theorem empty_journal_has_no_unreliable_active_label (m : Nat) (scope : DataScope)
    (confirmations : List (ExternalConfirmation m)) (target : Target m) :
    StoreMeaning (emptyStore m scope confirmations) target := by
  intro cell member
  cases member

theorem actual_fitted_sample_is_target_correct {m : Nat} (s : Store m) (target : Target m)
    (meaning : StoreMeaning s target) (i : Fin (trainingRows s).length) :
    ∃ cell ∈ s.cells, cell.event = ((trainingRows s).get i).event ∧
      (trainingData s i).2 = target s.scope cell.caseId cell.event (trainingData s i).1 := by
  have member : (trainingRows s).get i ∈ trainingRows s := List.get_mem _ _
  obtain ⟨cell, hc, produced⟩ := List.mem_filterMap.mp member
  refine ⟨cell, hc, ?_⟩
  cases state : cell.state with
  | active feature label =>
      simp only [Cell.toSample, state, Option.some.injEq] at produced
      have truth := meaning cell hc feature label state
      simp only [trainingData]
      rw [← produced]
      exact ⟨rfl, truth⟩
  | conflicted => simp [Cell.toSample, state] at produced
  | withdrawn => simp [Cell.toSample, state] at produced

-- A previously wrong label need not satisfy Reliable. Repair instead requires
-- the new external label to be correct and only the untouched events to retain
-- their meanings; the old label is deliberately not assumed correct.
theorem record_cell_repairs_target {m : Nat} (s : Store m) (change : Change m)
    (cell : Cell m) (target : Target m)
    (untouched : ∀ old ∈ s.cells, old.event ≠ cell.event → CellMeaning s.scope target old)
    (inserted : CellMeaning s.scope target cell) :
    StoreMeaning (recordCell s change cell) target := by
  intro item member
  change item ∈ putCell s.cells cell at member
  simp only [putCell, List.mem_cons] at member
  rcases member with same | prior
  · subst item
    exact inserted
  · have prior' := List.mem_filter.mp prior
    exact untouched item prior'.1 (by simpa using prior'.2)

theorem approved_correction_repairs_target {m : Nat} (s : Store m) (now : Instant)
    (permits : List (CorrectionPermit m)) (edit : Correction m) (row : Observation m)
    (target : Target m) (replacement : edit.replacement = some row)
    (truth : row.label = target s.scope row.caseId row.event row.feature)
    (untouched : ∀ old ∈ s.cells, old.event ≠ edit.supersedes.event →
      CellMeaning s.scope target old)
    (fresh : Change.corrected edit ∉ s.history)
    (found : lookup s edit.supersedes.event = some edit.supersedes)
    (valid : correctionValid s now edit = true)
    (allowed : correctionAuthorized s now permits edit = true) :
    StoreMeaning (correct s now permits edit).post target := by
  have details : (edit.policyVersion = s.scope.correctionPolicy ∧
      edit.effectiveFrom.ticks ≤ now.ticks) ∧
      observationValid s now row = true ∧ row.event = edit.supersedes.event ∧
      row.caseId = edit.supersedes.caseId := by
    simpa [correctionValid, replacement] using valid
  have transition : (correct s now permits edit).post =
      recordCell s (.corrected edit) (correctedCell edit) := by
    simp [correct, fresh, found, valid, allowed]
  rw [transition]
  apply record_cell_repairs_target s (.corrected edit) (correctedCell edit) target
    (by simpa only [correctedCell] using untouched)
  intro feature label same
  simp only [correctedCell, replacement, LabelState.active.injEq] at same
  rcases same with ⟨rfl, rfl⟩
  simpa only [details.2.2.1, details.2.2.2] using truth

def twoPointProtocol : LearningProtocol :=
  ⟨⟨1, 2, 3, 4, 5, ⟨10⟩, ⟨1⟩⟩, 6, 7, 8, 9, 10, 11, 12, 1/10⟩

def binaryLoss (score : ℚ) (label : Bool) : ℚ :=
  if (score = 1 ↔ label = true) then 0 else 1

def pseudoData (i : Fin 2) : Fin 2 × Bool := (i, decide (i.val = 0))
def trueData (i : Fin 2) : Fin 2 × Bool := (i, decide (i.val = 1))

def fittedOnSuggestions : Result FittedTable :=
  fitTable twoPointProtocol binaryLoss [[0, 0], [1, 0]] pseudoData

theorem suggestions_fit_better_but_true_risk_worsens :
    fittedOnSuggestions = .known ⟨twoPointProtocol, [1, 0], 2, 0⟩ ∧
    empiricalScore (tableLoss binaryLoss) pseudoData [0, 0] = 1/2 ∧
    empiricalScore (tableLoss binaryLoss) pseudoData [1, 0] = 0 ∧
    empiricalScore (tableLoss binaryLoss) trueData [0, 0] = 1/2 ∧
    empiricalScore (tableLoss binaryLoss) trueData [1, 0] = 1 := by
  norm_num [fittedOnSuggestions, fitTable, twoPointProtocol, proposed_empirical_fit,
    fitNonempty, selectMinimum, empiricalScore, tableLoss, binaryLoss, pseudoData,
    trueData, Fin.sum_univ_two]

end JurisLean.Candidates.FeedbackLabelSemantics20261027
