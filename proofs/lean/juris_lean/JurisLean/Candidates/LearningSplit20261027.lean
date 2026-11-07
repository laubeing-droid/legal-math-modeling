import JurisLean.Candidates.LearningEventSplit20261027

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

end JurisLean.Candidates.LearningSplit20261027
