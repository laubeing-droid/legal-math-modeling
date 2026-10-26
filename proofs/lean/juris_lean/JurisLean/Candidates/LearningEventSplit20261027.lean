import JurisLean.Candidates.LearningDependence20261027

/-!
Original 01.3 and correction S01 define mu as the REAL EVENT identity.
Different measurements and source records of that event inherit its partition.
The source interpreter must justify event identity and feature timestamps;
group assignment alone supplies no sampling-independence evidence.
All Boolean target examples below are synthetic, not real legal truth claims.
-/

namespace JurisLean.Candidates.LearningEventSplit20261027

structure EventSplitObservation where
  event : Nat
  measurement : Nat
  record : Nat
  feature : Bool
  label : Bool
  target : Bool
  featureTime : Nat
  predictionCutoff : Nat
  deriving DecidableEq, Repr

def eventSplit (trainingEvent : Nat → Bool) (rows : List EventSplitObservation) :
    List EventSplitObservation × List EventSplitObservation :=
  (rows.filter fun row => trainingEvent row.event,
   rows.filter fun row => !(trainingEvent row.event))

def eventUnits (rows : List EventSplitObservation) : Finset Nat :=
  (rows.map EventSplitObservation.event).toFinset

theorem u01_3_partition_membership (trainingEvent : Nat → Bool)
    (rows : List EventSplitObservation) (row : EventSplitObservation) :
    (row ∈ (eventSplit trainingEvent rows).1 ↔
      row ∈ rows ∧ trainingEvent row.event = true) ∧
    (row ∈ (eventSplit trainingEvent rows).2 ↔
      row ∈ rows ∧ trainingEvent row.event = false) := by
  simp [eventSplit]

theorem u01_3_same_event_cannot_cross (trainingEvent : Nat → Bool)
    (rows : List EventSplitObservation) (train test : EventSplitObservation)
    (inTrain : train ∈ (eventSplit trainingEvent rows).1)
    (inTest : test ∈ (eventSplit trainingEvent rows).2) :
    train.event ≠ test.event := by
  intro same
  have ht := ((u01_3_partition_membership trainingEvent rows train).1.mp inTrain).2
  have he := ((u01_3_partition_membership trainingEvent rows test).2.mp inTest).2
  rw [← same, ht] at he
  cases he

theorem u01_3_every_row_has_a_partition (trainingEvent : Nat → Bool)
    (rows : List EventSplitObservation) (row : EventSplitObservation) (member : row ∈ rows) :
    row ∈ (eventSplit trainingEvent rows).1 ∨ row ∈ (eventSplit trainingEvent rows).2 := by
  cases assigned : trainingEvent row.event with
  | false =>
      exact Or.inr ((u01_3_partition_membership trainingEvent rows row).2.mpr ⟨member, assigned⟩)
  | true =>
      exact Or.inl ((u01_3_partition_membership trainingEvent rows row).1.mpr ⟨member, assigned⟩)

-- The event count is unchanged by copying records. Independence or an
-- effective sample-size bound still requires a data-generating assumption.
theorem u01_3_duplicate_records_do_not_add_events (rows : List EventSplitObservation) :
    eventUnits (rows ++ rows) = eventUnits rows ∧
      (eventUnits (rows ++ rows)).card = (eventUnits rows).card := by
  have same : eventUnits (rows ++ rows) = eventUnits rows := by
    ext unit
    simp [eventUnits]
  exact ⟨same, congrArg Finset.card same⟩

theorem u01_3_non_event_ids_do_not_choose_partition (trainingEvent : Nat → Bool)
    (row : EventSplitObservation) (newMeasurement newRecord : Nat) :
    trainingEvent ({ row with measurement := newMeasurement, record := newRecord } :
      EventSplitObservation).event = trainingEvent row.event := rfl

def leakedTrain : EventSplitObservation := ⟨1, 10, 20, false, false, true, 3, 1⟩
def leakedTest : EventSplitObservation := ⟨2, 11, 21, true, true, false, 3, 1⟩

-- Event-disjoint output can still contain future information, the label as
-- an input feature, and the same systematically wrong labeling mechanism.
theorem u01_3_event_split_does_not_certify_information :
    eventSplit (fun event => event == 1) [leakedTrain, leakedTest] =
      ([leakedTrain], [leakedTest]) ∧
    leakedTrain.event ≠ leakedTest.event ∧
    leakedTrain.measurement ≠ leakedTest.measurement ∧
    leakedTrain.record ≠ leakedTest.record ∧
    (∀ row ∈ [leakedTrain, leakedTest],
      row.predictionCutoff < row.featureTime ∧ row.feature = row.label ∧
        row.label = !row.target) := by
  decide

end JurisLean.Candidates.LearningEventSplit20261027
