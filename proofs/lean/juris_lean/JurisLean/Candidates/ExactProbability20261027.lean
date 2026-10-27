import JurisLean.Candidates.Final20261021.Probability
import Mathlib.MeasureTheory.MeasurableSpace.Prod
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.Probability.Distributions.Beta

/-!
Exact additions required by original topic 04. A measurable deterministic copy
has the same generated information, not merely the same finite likelihood
example. Supplied numerator/denominator enclosures have an explicit width bound.
Source identity and the mechanism producing the supplied bounds remain external;
these statements do not identify a sampling law or implement quadrature.
-/

namespace JurisLean.Candidates.ExactProbability20261027

open MeasureTheory
open JurisLean.Candidates.Final20261021

theorem deterministic_copy_preserves_generated_information
    {Ω A B : Type*} [mA : MeasurableSpace A] [mB : MeasurableSpace B]
    (X : Ω → A) (g : A → B) (measurableCopy : Measurable g) :
    (mA.prod mB).comap (fun w => (X w, g (X w))) = mA.comap X := by
  rw [MeasurableSpace.comap_prodMk]
  apply sup_eq_left.mpr
  simpa only [MeasurableSpace.comap_comp, Function.comp_def] using
    (MeasurableSpace.comap_mono (g := X) measurableCopy.comap_le)

theorem deterministic_copy_keeps_integrable_conditional_expectation
    {Ω A B : Type*} [MeasurableSpace Ω] [mA : MeasurableSpace A] [mB : MeasurableSpace B]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → A) (g : A → B)
    (_observed : Measurable X) (measurableCopy : Measurable g)
    (target : Ω → ℝ) (_integrable : Integrable target μ) :
    μ[target | (mA.prod mB).comap (fun w => (X w, g (X w)))] =ᵐ[μ]
      μ[target | mA.comap X] := by
  rw [deterministic_copy_preserves_generated_information X g measurableCopy]
  exact Filter.EventuallyEq.rfl

theorem supplied_enclosure_has_explicit_width_bound (N B nL nU bL bU : ℝ)
    (nonnegative : 0 ≤ N) (belowTotal : N ≤ B) (numeratorLower : nL ≤ N) (numeratorUpper : N ≤ nU)
    (denominatorPositive : 0 < bL) (denominatorLower : bL ≤ B) (denominatorUpper : B ≤ bU) :
    0 ≤ min 1 (nU / bL) - max 0 (nL / bU) ∧
      min 1 (nU / bL) - max 0 (nL / bU) ≤ 1 ∧
      min 1 (nU / bL) - max 0 (nL / bU) ≤
        (nU - nL) / bU + nU * (bU - bL) / (bL * bU) := by
  have enclosure := Probability.u04_2_enclosed_propagation N B nL nU bL bU
    nonnegative belowTotal numeratorLower numeratorUpper denominatorPositive denominatorLower denominatorUpper
  have upperPositive : 0 < bU := lt_of_lt_of_le denominatorPositive (denominatorLower.trans denominatorUpper)
  have unclipped : min 1 (nU / bL) - max 0 (nL / bU) ≤ nU / bL - nL / bU :=
    sub_le_sub (min_le_right _ _) (le_max_right _ _)
  have propagation : nU / bL - nL / bU =
      (nU - nL) / bU + nU * (bU - bL) / (bL * bU) := by
    field_simp [ne_of_gt denominatorPositive, ne_of_gt upperPositive]
    <;> ring
  refine ⟨sub_nonneg.mpr (enclosure.1.trans enclosure.2), ?_, unclipped.trans_eq propagation⟩
  have zeroLower : 0 ≤ max 0 (nL / bU) := le_max_left _ _
  have oneUpper : min 1 (nU / bL) ≤ 1 := min_le_left _ _
  linarith

end JurisLean.Candidates.ExactProbability20261027
