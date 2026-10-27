import JurisLean.Candidates.ExactProbability20261027
import Mathlib.Probability.Independence.Basic

/-!
U04.5 original residual: joint likelihoods under the declared hypothesis laws.
The laws and measurement identities are inputs, not conclusions about reality.
Zero reference mass produces no finite likelihood-ratio receipt. A copy is a
deterministic function of the observed measurement, not a fresh independent draw.
-/

namespace JurisLean.Candidates.MeasurementLikelihood20261027

open MeasureTheory ProbabilityTheory Set

noncomputable section

def eventLikelihoodRatio {Ω : Type*} [MeasurableSpace Ω]
    (P Q : Measure Ω) (event : Set Ω) : Option ℝ :=
  if 0 < Q.real event then some (P.real event / Q.real event) else none

theorem joint_likelihood_chain {Ω : Type*} [MeasurableSpace Ω]
    (P Q : Measure Ω) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (first second : Set Ω)
    (positiveP : 0 < P.real first) (positiveQ : 0 < Q.real first)
    (positiveJoint : 0 < Q.real (first ∩ second)) :
    eventLikelihoodRatio P Q (first ∩ second) = some
      ((P.real first / Q.real first) *
        ((P.real (first ∩ second) / P.real first) /
          (Q.real (first ∩ second) / Q.real first))) := by
  rw [eventLikelihoodRatio, if_pos positiveJoint]
  congr 1
  field_simp [ne_of_gt positiveP, ne_of_gt positiveQ, ne_of_gt positiveJoint] <;> ring

-- Independence is supplied under EACH hypothesis law; it is not read from IDs.
theorem independent_measurement_joint_mass
    {Ω A B : Type*} [MeasurableSpace Ω] [MeasurableSpace A] [MeasurableSpace B]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : Ω → A) (Y : Ω → B)
    (independent : IndepFun X Y P) (s : Set A) (t : Set B)
    (hs : MeasurableSet s) (ht : MeasurableSet t) :
    P.real (X ⁻¹' s ∩ Y ⁻¹' t) = P.real (X ⁻¹' s) * P.real (Y ⁻¹' t) := by
  have product := independent.meas_inter (s := X ⁻¹' s) (t := Y ⁻¹' t)
    ⟨s, hs, rfl⟩ ⟨t, ht, rfl⟩
  change (P (X ⁻¹' s ∩ Y ⁻¹' t)).toReal = _
  rw [product, ENNReal.toReal_mul]

theorem independent_measurement_likelihood_multiplies
    {Ω A B : Type*} [MeasurableSpace Ω] [MeasurableSpace A] [MeasurableSpace B]
    (P Q : Measure Ω) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (X : Ω → A) (Y : Ω → B)
    (independentP : IndepFun X Y P) (independentQ : IndepFun X Y Q)
    (s : Set A) (t : Set B) (hs : MeasurableSet s) (ht : MeasurableSet t)
    (positiveX : 0 < Q.real (X ⁻¹' s)) (positiveY : 0 < Q.real (Y ⁻¹' t)) :
    eventLikelihoodRatio P Q (X ⁻¹' s ∩ Y ⁻¹' t) = some
      ((P.real (X ⁻¹' s) / Q.real (X ⁻¹' s)) *
        (P.real (Y ⁻¹' t) / Q.real (Y ⁻¹' t))) := by
  have p := independent_measurement_joint_mass P X Y independentP s t hs ht
  have q := independent_measurement_joint_mass Q X Y independentQ s t hs ht
  have positive : 0 < Q.real (X ⁻¹' s ∩ Y ⁻¹' t) := by
    rw [q]
    exact mul_pos positiveX positiveY
  rw [eventLikelihoodRatio, if_pos positive, p, q, mul_div_mul_comm]

theorem deterministic_copy_observation_event {Ω A B : Type*}
    (X : Ω → A) (copy : A → B) (observed : A) :
    {w | X w = observed ∧ copy (X w) = copy observed} = {w | X w = observed} := by
  ext w
  simp only [mem_setOf_eq]
  exact ⟨And.left, fun h => ⟨h, congrArg copy h⟩⟩

theorem deterministic_copy_likelihood_unchanged
    {Ω A B : Type*} [MeasurableSpace Ω]
    (P Q : Measure Ω) (X : Ω → A) (copy : A → B) (observed : A) :
    eventLikelihoodRatio P Q {w | X w = observed ∧ copy (X w) = copy observed} =
      eventLikelihoodRatio P Q {w | X w = observed} := by
  rw [deterministic_copy_observation_event]

theorem zero_reference_mass_has_no_finite_ratio {Ω : Type*} [MeasurableSpace Ω]
    (P Q : Measure Ω) (event : Set Ω) (zero : Q.real event = 0) :
    eventLikelihoodRatio P Q event = none := by
  simp [eventLikelihoodRatio, zero]

theorem nondegenerate_measurement_is_not_independent_of_itself
    {Ω A : Type*} [MeasurableSpace Ω] [MeasurableSpace A]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : Ω → A)
    (s : Set A) (hs : MeasurableSet s)
    (positive : 0 < P.real (X ⁻¹' s)) (belowOne : P.real (X ⁻¹' s) < 1) :
    ¬ IndepFun X X P := by
  intro independent
  have product := independent_measurement_joint_mass P X X independent s s hs hs
  rw [inter_self] at product
  nlinarith

end
end JurisLean.Candidates.MeasurementLikelihood20261027
