import JurisLean.Candidates.LearningEventSplit20261027
import JurisLean.Seams.Probability

/-!
Measurement grouping from the retained branch, on the current event/measurement/
record carrier. The bridge below states exactly when it agrees with event grouping.
-/

namespace JurisLean.Candidates.LearningSplit20261027

abbrev SplitObservation :=
  JurisLean.Candidates.LearningEventSplit20261027.EventSplitObservation

def groupedSplit (trainingUnit : Nat → Bool) (rows : List SplitObservation) :
    List SplitObservation × List SplitObservation :=
  (rows.filter fun row => trainingUnit row.measurement,
   rows.filter fun row => !(trainingUnit row.measurement))

def measurementUnits (rows : List SplitObservation) : Finset Nat :=
  (rows.map JurisLean.Candidates.LearningEventSplit20261027.EventSplitObservation.measurement).toFinset

theorem u01_3_partition_membership (trainingUnit : Nat → Bool)
    (rows : List SplitObservation) (row : SplitObservation) :
    (row ∈ (groupedSplit trainingUnit rows).1 ↔
      row ∈ rows ∧ trainingUnit row.measurement = true) ∧
    (row ∈ (groupedSplit trainingUnit rows).2 ↔
      row ∈ rows ∧ trainingUnit row.measurement = false) := by
  simp [groupedSplit]

theorem u01_3_same_measurement_cannot_cross (trainingUnit : Nat → Bool)
    (rows : List SplitObservation) (train test : SplitObservation)
    (inTrain : train ∈ (groupedSplit trainingUnit rows).1)
    (inTest : test ∈ (groupedSplit trainingUnit rows).2) :
    train.measurement ≠ test.measurement := by
  intro same
  have ht := ((u01_3_partition_membership trainingUnit rows train).1.mp inTrain).2
  have he := ((u01_3_partition_membership trainingUnit rows test).2.mp inTest).2
  rw [← same, ht] at he
  cases he

theorem u01_3_every_row_has_a_partition (trainingUnit : Nat → Bool)
    (rows : List SplitObservation) (row : SplitObservation) (member : row ∈ rows) :
    row ∈ (groupedSplit trainingUnit rows).1 ∨
      row ∈ (groupedSplit trainingUnit rows).2 := by
  cases assigned : trainingUnit row.measurement with
  | false =>
      exact Or.inr ((u01_3_partition_membership trainingUnit rows row).2.mpr ⟨member, assigned⟩)
  | true =>
      exact Or.inl ((u01_3_partition_membership trainingUnit rows row).1.mpr ⟨member, assigned⟩)

-- Counting distinct measurement identities is invariant to copying all rows.
-- This count is not asserted to be an iid or effective sample size.
theorem u01_3_duplicate_records_do_not_add_measurement_units
    (rows : List SplitObservation) :
    measurementUnits (rows ++ rows) = measurementUnits rows ∧
      (measurementUnits (rows ++ rows)).card = (measurementUnits rows).card := by
  have same : measurementUnits (rows ++ rows) = measurementUnits rows := by
    ext unit
    simp [measurementUnits]
  exact ⟨same, congrArg Finset.card same⟩

-- Relabelling a record does not change its assigned measurement partition.
theorem u01_3_record_identifier_does_not_choose_partition
    (trainingUnit : Nat → Bool) (row : SplitObservation) (newRecord : Nat) :
    trainingUnit ({ row with record := newRecord } : SplitObservation).measurement =
      trainingUnit row.measurement := rfl

def leakedTrain : SplitObservation := ⟨1, 10, 20, false, false, true, 3, 1⟩
def leakedTest : SplitObservation := ⟨2, 11, 21, true, true, false, 3, 1⟩

-- Disjoint measurement identities do not rule out future features, direct
-- label leakage or a shared systematically wrong source-label mechanism.
-- The actual assigned train/test outputs are used in this finite witness.
theorem u01_3_grouped_split_does_not_certify_information :
    groupedSplit (fun unit => unit == 10) [leakedTrain, leakedTest] =
      ([leakedTrain], [leakedTest]) ∧
    leakedTrain.measurement ≠ leakedTest.measurement ∧
    leakedTrain.event ≠ leakedTest.event ∧
    leakedTrain.record ≠ leakedTest.record ∧
    (∀ row ∈ [leakedTrain, leakedTest],
      row.predictionCutoff < row.featureTime ∧ row.feature = row.label ∧
        row.label = !row.target) := by
  decide


/-- A source-resolved measurement inherits the partition of its actual event. -/
theorem measurement_split_agrees_with_event_split
    (eventOfMeasurement : Nat → Nat) (trainingEvent : Nat → Bool)
    (rows : List SplitObservation)
    (resolved : ∀ row ∈ rows, eventOfMeasurement row.measurement = row.event) :
    groupedSplit (fun measurement => trainingEvent (eventOfMeasurement measurement)) rows =
      JurisLean.Candidates.LearningEventSplit20261027.eventSplit trainingEvent rows := by
  induction rows with
  | nil => rfl
  | cons row rows ih =>
      have head := resolved row (by simp)
      have tail : ∀ other ∈ rows,
          eventOfMeasurement other.measurement = other.event := by
        intro other member
        exact resolved other (by simp [member])
      have left := congrArg Prod.fst (ih tail)
      have right := congrArg Prod.snd (ih tail)
      simp only [groupedSplit, JurisLean.Candidates.LearningEventSplit20261027.eventSplit]
        at left right ⊢
      simp only [List.filter_cons, head]
      rw [left, right]

/-- Independent measurement assignments can split two records of one event. -/
theorem measurement_split_can_cross_one_event :
    groupedSplit (fun unit => unit == 10)
      [leakedTrain, {leakedTrain with measurement := 11, record := 21}] =
      ([leakedTrain], [{leakedTrain with measurement := 11, record := 21}]) ∧
    leakedTrain.event =
      ({leakedTrain with measurement := 11, record := 21} : SplitObservation).event := by
  decide

/-! The archived S3/S7 count bridge is consumed here by the existing event rows.
Repeated records do not add events or posterior mass. Conflicting labels for
one event are rejected before producing a posterior. -/

structure WellFormedCounts where
  successes : Nat
  trials : Nat
  bounded : successes ≤ trials

def countWeights (o : WellFormedCounts) : Fin 2 → ℚ :=
  fun i => if i.val = 0 then o.successes else (o.trials - o.successes : Nat)

def joinCounts (a b : WellFormedCounts) : WellFormedCounts :=
  ⟨a.successes + b.successes, a.trials + b.trials, Nat.add_le_add a.bounded b.bounded⟩

theorem count_weights_join (a b : WellFormedCounts) :
    countWeights (joinCounts a b) = fun i => countWeights a i + countWeights b i := by
  funext i
  fin_cases i
  · show ((a.successes + b.successes : Nat) : ℚ) = (a.successes : ℚ) + (b.successes : ℚ)
    exact Nat.cast_add _ _
  · show ((a.trials + b.trials - (a.successes + b.successes) : Nat) : ℚ) =
      ((a.trials - a.successes : Nat) : ℚ) + ((b.trials - b.successes : Nat) : ℚ)
    have subtraction : a.trials + b.trials - (a.successes + b.successes) =
        (a.trials - a.successes) + (b.trials - b.successes) := by
      have ha := a.bounded
      have hb := b.bounded
      omega
    rw [subtraction]
    exact Nat.cast_add _ _

theorem posterior_join_commutes (a b : WellFormedCounts) (prior : Fin 2 → ℚ) :
    JurisLean.FullMath.Probability.dirWeights prior (countWeights (joinCounts a b)) =
      JurisLean.FullMath.Probability.dirWeights prior (fun i => countWeights a i + countWeights b i) :=
  congrArg (JurisLean.FullMath.Probability.dirWeights prior) (count_weights_join a b)

theorem malformed_counts_uninhabited :
    ¬ ∃ o : WellFormedCounts, o.successes = 3 ∧ o.trials = 2 := by
  rintro ⟨o, hs, ht⟩
  have h := o.bounded
  omega

-- The missing invariant in the old Nat pair really changes the negative count.
theorem unbounded_count_join_counterexample :
    ((2 + 5 - (3 + 0) : Nat) : ℚ) ≠
      ((2 - 3 : Nat) : ℚ) + ((5 - 0 : Nat) : ℚ) := by decide

def successfulEvents (rows : List SplitObservation) : Finset Nat :=
  ((rows.filter fun row => row.label).map fun row => row.event).toFinset

theorem successful_events_subset (rows : List SplitObservation) :
    successfulEvents rows ⊆ JurisLean.Candidates.LearningEventSplit20261027.eventUnits rows := by
  intro event member
  obtain ⟨row, inRows, same⟩ := List.mem_map.mp (List.mem_toFinset.mp member)
  exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨row, (List.mem_filter.mp inRows).1, same⟩)

def eventCounts (rows : List SplitObservation) : WellFormedCounts :=
  ⟨(successfulEvents rows).card,
   (JurisLean.Candidates.LearningEventSplit20261027.eventUnits rows).card,
   Finset.card_le_card (successful_events_subset rows)⟩

def consistentEventLabels (rows : List SplitObservation) : Bool :=
  rows.all fun a => rows.all fun b => decide (a.event = b.event → a.label = b.label)

def eventPosterior (prior : Fin 2 → ℚ) (rows : List SplitObservation) : Option (Fin 2 → ℚ) :=
  if consistentEventLabels rows then
    some (JurisLean.FullMath.Probability.dirWeights prior (countWeights (eventCounts rows)))
  else none

theorem successful_events_copy (rows : List SplitObservation) :
    successfulEvents (rows ++ rows) = successfulEvents rows := by
  ext event
  simp [successfulEvents]

theorem consistent_labels_copy (rows : List SplitObservation) :
    consistentEventLabels (rows ++ rows) = consistentEventLabels rows := by
  simp [consistentEventLabels, List.all_append]

theorem event_posterior_replay_stable (prior : Fin 2 → ℚ) (rows : List SplitObservation) :
    eventPosterior prior (rows ++ rows) = eventPosterior prior rows := by
  have events :=
    (JurisLean.Candidates.LearningEventSplit20261027.u01_3_duplicate_records_do_not_add_events rows).1
  simp [eventPosterior, consistent_labels_copy, eventCounts, countWeights,
    successful_events_copy, events]

theorem conflicting_event_labels_refused (prior : Fin 2 → ℚ) :
    eventPosterior prior [leakedTrain, {leakedTrain with label := !leakedTrain.label}] = none := by
  simp [eventPosterior, consistentEventLabels, leakedTrain]

def eventBetaModel (model : JurisLean.Seams.Probability.BetaGenModel)
    (rows : List SplitObservation) : JurisLean.Seams.Probability.BetaGenModel :=
  { shape := model.shape
    counts := countWeights (eventCounts rows)
    hshape := model.hshape
    hcounts := by
      intro i
      fin_cases i
      · exact Nat.cast_nonneg _
      · exact Nat.cast_nonneg _
    hpos := model.hpos }

theorem accepted_event_posterior_is_existing_beta_readout
    (model : JurisLean.Seams.Probability.BetaGenModel) (rows : List SplitObservation)
    (consistent : consistentEventLabels rows = true) :
    eventPosterior model.shape rows =
      some (JurisLean.Seams.Probability.posteriorReadout (eventBetaModel model rows)) := by
  simp [eventPosterior, consistent, eventBetaModel,
    JurisLean.Seams.Probability.posteriorReadout]

end JurisLean.Candidates.LearningSplit20261027
