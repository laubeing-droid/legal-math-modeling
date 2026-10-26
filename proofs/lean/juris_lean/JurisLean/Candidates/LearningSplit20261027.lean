import JurisLean.Candidates.LearningDependence20261027

/-!
Original 01.3: split by measurement identity, not by record identity.
The assignment is an explicit input, not evidence of sampling independence.
The source interpreter must justify the measurement identities and timestamps.
The examples use synthetic Boolean targets, not real legal truth assertions.
-/

namespace JurisLean.Candidates.LearningSplit20261027

structure SplitObservation where
  event : Nat
  measurement : Nat
  record : Nat
  feature : Bool
  label : Bool
  target : Bool
  featureTime : Nat
  predictionCutoff : Nat
  deriving DecidableEq, Repr

def groupedSplit (trainingUnit : Nat → Bool) (rows : List SplitObservation) :
    List SplitObservation × List SplitObservation :=
  (rows.filter fun row => trainingUnit row.measurement,
   rows.filter fun row => !(trainingUnit row.measurement))

def measurementUnits (rows : List SplitObservation) : Finset Nat :=
  (rows.map SplitObservation.measurement).toFinset

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
  | false => exact Or.inr
      ((u01_3_partition_membership trainingUnit rows row).2.mpr ⟨member, assigned⟩)
  | true => exact Or.inl
      ((u01_3_partition_membership trainingUnit rows row).1.mpr ⟨member, assigned⟩)

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

end JurisLean.Candidates.LearningSplit20261027
