import JurisLean.Candidates.LearningBoundary20261027
import Mathlib.Probability.Kernel.Composition.RadonNikodym
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Measure.Dirac
import Mathlib.Tactic

/-!
Original 05.5 L119/L121/L123. The same Markov label kernel is the actual
common conditional object; its compProd projections are checked explicitly.
Transport uses the true RN weight. Estimated weights retain an error integral.
Only weighted integrability is obtained: a bounded original loss is not a
certificate that its weighted score is bounded. A bounded-score concentration
result therefore still needs its own weight bound or other tail premises.
The concrete negative worlds do not assert any shifted conformal guarantee.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace JurisLean.Candidates.U05_5OriginalShiftInstances20261101
open LearningBoundary20261027

/-- Real bounded losses on actual joint laws with one common label kernel.
The weight is the target/source input RN derivative, not a fitted substitute. -/
theorem common_label_covariate_transport {X Y : Type*}
    [MeasurableSpace X] [MeasurableSpace Y]
    (sourceInput targetInput : Measure X)
    [IsProbabilityMeasure sourceInput] [IsProbabilityMeasure targetInput]
    (labels : Kernel X Y) [IsMarkovKernel labels]
    (overlap : targetInput ≪ sourceInput)
    (loss : X × Y → ℝ) (lossMeasurable : Measurable loss)
    (lossRange : ∀ z, loss z ∈ Set.Icc (0 : ℝ) 1) :
    (sourceInput ⊗ₘ labels).fst = sourceInput ∧
    (targetInput ⊗ₘ labels).fst = targetInput ∧
    Integrable loss (targetInput ⊗ₘ labels) ∧
    Integrable (fun z : X × Y => (targetInput.rnDeriv sourceInput z.1).toReal * loss z)
      (sourceInput ⊗ₘ labels) ∧
    (∫ z, loss z ∂(targetInput ⊗ₘ labels)) =
      ∫ z, (targetInput.rnDeriv sourceInput z.1).toReal * loss z ∂(sourceInput ⊗ₘ labels) := by
  let sourceJoint := sourceInput ⊗ₘ labels
  let targetJoint := targetInput ⊗ₘ labels
  have jointOverlap : targetJoint ≪ sourceJoint := overlap.compProd_left labels
  have jointRN := ProbabilityTheory.rnDeriv_measure_compProd_left targetInput sourceInput labels
  have lossL2 : MemLp loss 2 targetJoint :=
    MemLp.of_bound lossMeasurable.aestronglyMeasurable 1 <| by
      exact Filter.Eventually.of_forall (fun z => by
        rw [Real.norm_eq_abs, abs_of_nonneg (lossRange z).1]
        exact (lossRange z).2)
  have lossIntegrable : Integrable loss targetJoint := lossL2.integrable one_le_two
  have jointWeightedIntegrable : Integrable
      (fun z : X × Y => (targetJoint.rnDeriv sourceJoint z).toReal * loss z) sourceJoint :=
    (MeasureTheory.integrable_toReal_rnDeriv_mul_iff
      (μ := targetJoint) (ν := sourceJoint) (f := loss) jointOverlap).mpr lossIntegrable
  have weightedEquality :
      (fun z : X × Y => (targetJoint.rnDeriv sourceJoint z).toReal * loss z)
        =ᵐ[sourceJoint]
      (fun z : X × Y => (targetInput.rnDeriv sourceInput z.1).toReal * loss z) := by
    filter_upwards [jointRN] with z hz
    rw [hz]
  have weightedIntegrable : Integrable
      (fun z : X × Y => (targetInput.rnDeriv sourceInput z.1).toReal * loss z) sourceJoint :=
    jointWeightedIntegrable.congr weightedEquality
  refine ⟨Measure.fst_compProd sourceInput labels, Measure.fst_compProd targetInput labels,
    lossIntegrable, weightedIntegrable, ?_⟩
  calc
    (∫ z, loss z ∂targetJoint) =
        ∫ z, (targetJoint.rnDeriv sourceJoint z).toReal * loss z ∂sourceJoint := by
      simpa only [smul_eq_mul] using
        (MeasureTheory.integral_rnDeriv_smul
          (μ := targetJoint) (ν := sourceJoint) (f := loss) jointOverlap).symm
    _ = ∫ z, (targetInput.rnDeriv sourceInput z.1).toReal * loss z ∂sourceJoint :=
      integral_congr_ae weightedEquality

/-- For a fixed estimated weight, the population error is kept explicitly.
This is error accounting, not an estimation rate or a zero-error assumption. -/
theorem estimated_weight_error_identity {X Y : Type*}
    [MeasurableSpace X] [MeasurableSpace Y]
    (sourceInput targetInput : Measure X)
    [IsProbabilityMeasure sourceInput] [IsProbabilityMeasure targetInput]
    (labels : Kernel X Y) [IsMarkovKernel labels]
    (overlap : targetInput ≪ sourceInput)
    (loss : X × Y → ℝ) (lossMeasurable : Measurable loss)
    (lossRange : ∀ z, loss z ∈ Set.Icc (0 : ℝ) 1)
    (estimated : X → ℝ)
    (estimatedIntegrable : Integrable (fun z : X × Y => estimated z.1 * loss z)
      (sourceInput ⊗ₘ labels)) :
    Integrable (fun z : X × Y =>
      (estimated z.1 - (targetInput.rnDeriv sourceInput z.1).toReal) * loss z)
      (sourceInput ⊗ₘ labels) ∧
    (∫ z, estimated z.1 * loss z ∂(sourceInput ⊗ₘ labels)) -
        (∫ z, loss z ∂(targetInput ⊗ₘ labels)) =
      ∫ z, (estimated z.1 - (targetInput.rnDeriv sourceInput z.1).toReal) * loss z
        ∂(sourceInput ⊗ₘ labels) := by
  rcases common_label_covariate_transport sourceInput targetInput labels overlap loss
    lossMeasurable lossRange with ⟨_, _, _, weightedIntegrable, meanEquality⟩
  have errorIntegrable : Integrable (fun z : X × Y =>
      (estimated z.1 - (targetInput.rnDeriv sourceInput z.1).toReal) * loss z)
      (sourceInput ⊗ₘ labels) := by
    apply (estimatedIntegrable.sub weightedIntegrable).congr
    exact Filter.Eventually.of_forall (fun z => by
      change (estimated z.1 * loss z -
        (targetInput.rnDeriv sourceInput z.1).toReal * loss z) =
        (estimated z.1 - (targetInput.rnDeriv sourceInput z.1).toReal) * loss z
      ring)
  refine ⟨errorIntegrable, ?_⟩
  rw [meanEquality, ← integral_sub estimatedIntegrable weightedIntegrable]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun z => by ring)

/-- Expected zero-one loss of a two-atom randomized prediction at the unseen
input. The two weights are proved nonnegative and normalized in the theorem. -/
def randomizedPointRisk (p : ℝ) (target : Bool → Bool) : ℝ :=
  p * pointPopulationRisk true target (fun _ => true) +
    (1 - p) * pointPopulationRisk true target (fun _ => false)

/-- Every binary randomized learner has an unseen-label world with error at
least one half, while both worlds present the exact same source data. -/
theorem randomized_unseen_input_lower_bound (n : ℕ)
    (learner : (Fin n → Bool × Bool) → Bool → ℝ)
    (valid : learner (visibleTraining n false) true ∈ Set.Icc (0 : ℝ) 1) :
    visibleTraining n false = visibleTraining n true ∧
    (let p := learner (visibleTraining n false) true
     0 ≤ p ∧ 0 ≤ 1 - p ∧ p + (1 - p) = 1 ∧
       ∃ hiddenLabel : Bool, (1 / 2 : ℝ) ≤ randomizedPointRisk
         (learner (visibleTraining n hiddenLabel) true) (worldTarget hiddenLabel)) := by
  have sameTraining :=
    (u01_3_two_worlds_same_training_uncontrolled_deployment n (fun _ _ => false)).1
  refine ⟨sameTraining, valid.1, sub_nonneg.mpr valid.2, by ring, ?_⟩
  by_cases hp : (1 / 2 : ℝ) ≤ learner (visibleTraining n false) true
  · refine ⟨false, ?_⟩
    simpa [randomizedPointRisk, pointPopulationRisk_eq, worldTarget] using hp
  · refine ⟨true, ?_⟩
    rw [← sameTraining]
    have hother : (1 / 2 : ℝ) ≤ 1 - learner (visibleTraining n false) true := by linarith
    simpa [randomizedPointRisk, pointPopulationRisk_eq, worldTarget] using hother

section ConcreteConceptShift
local instance : MeasurableSpace Bool := ⊤

/-- The two joint laws share X=true, with the two opposite labels from the
existing worldTarget object. This is separate from the unseen-X example. -/
def conceptLaw (hiddenLabel : Bool) : Measure (Bool × Bool) :=
  Measure.dirac (true, worldTarget hiddenLabel true)

/-- Same actual input marginal, positive conditioning atom, opposite actual
conditional label rates, and identical output law for any X-only Bool detector. -/
theorem same_input_marginal_different_label_mechanism :
    IsProbabilityMeasure (conceptLaw false) ∧
    IsProbabilityMeasure (conceptLaw true) ∧
    (conceptLaw false).fst = (conceptLaw true).fst ∧
    (conceptLaw false).real {z | z.1 = true} = 1 ∧
    (conceptLaw true).real {z | z.1 = true} = 1 ∧
    ((conceptLaw false).real {z | z.1 = true ∧ z.2 = true}) /
        ((conceptLaw false).real {z | z.1 = true}) = 0 ∧
    ((conceptLaw true).real {z | z.1 = true ∧ z.2 = true}) /
        ((conceptLaw true).real {z | z.1 = true}) = 1 ∧
    ∀ detector : Bool → Bool,
      (conceptLaw false).map (fun z => detector z.1) =
      (conceptLaw true).map (fun z => detector z.1) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold conceptLaw
    infer_instance
  · unfold conceptLaw
    infer_instance
  · simp [conceptLaw, Measure.fst, worldTarget]
  · change ((Measure.dirac (true, false)) {z : Bool × Bool | z.1 = true}).toReal = 1
    simp
  · change ((Measure.dirac (true, true)) {z : Bool × Bool | z.1 = true}).toReal = 1
    simp
  · change ((Measure.dirac (true, false)) {z : Bool × Bool | z.1 = true ∧ z.2 = true}).toReal /
      ((Measure.dirac (true, false)) {z : Bool × Bool | z.1 = true}).toReal = 0
    simp
  · change ((Measure.dirac (true, true)) {z : Bool × Bool | z.1 = true ∧ z.2 = true}).toReal /
      ((Measure.dirac (true, true)) {z : Bool × Bool | z.1 = true}).toReal = 1
    simp
  · intro detector
    simp [conceptLaw, worldTarget]

end ConcreteConceptShift
end JurisLean.Candidates.U05_5OriginalShiftInstances20261101