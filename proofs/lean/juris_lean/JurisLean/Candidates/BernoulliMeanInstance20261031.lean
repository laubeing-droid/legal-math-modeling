import JurisLean.Candidates.LearningFiniteClass20261027
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.MeasureTheory.Integral.Bochner.Set

namespace JurisLean.Candidates.BernoulliMeanInstance20261031

open MeasureTheory ProbabilityTheory
open JurisLean.Candidates.LearningFiniteClass20261027

noncomputable section

local instance : MeasurableSpace Bool := ⊤

private theorem parameter_le_one (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    p.toNNReal ≤ 1 := by
  change (p.toNNReal : ℝ) ≤ (1 : ℝ)
  rw [Real.coe_toNNReal p hp0]
  exact hp1

/-- The actual Bernoulli probability measure, including the endpoints. -/
def bernoulliMeasure (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) : Measure Bool :=
  (PMF.bernoulli p.toNNReal (parameter_le_one p hp0 hp1)).toMeasure

/-- The numerical value whose empirical mean is the success frequency. -/
def bitValue (b : Bool) : ℝ := if b then 1 else 0

private theorem bitValue_measurable : Measurable bitValue := by
  unfold bitValue
  fun_prop

private theorem bitValue_range (b : Bool) : bitValue b ∈ Set.Icc (0 : ℝ) 1 := by
  cases b <;> norm_num [bitValue]

private theorem bernoulli_bit_mean (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (∫ b, bitValue b ∂bernoulliMeasure p hp0 hp1) = p := by
  have indicator_eq : bitValue = ({true} : Set Bool).indicator (1 : Bool → ℝ) := by
    funext b
    cases b <;> simp [bitValue]
  rw [indicator_eq, integral_indicator_one (show MeasurableSet ({true} : Set Bool) by trivial)]
  change ((bernoulliMeasure p hp0 hp1) {true}).toReal = p
  have mass : (bernoulliMeasure p hp0 hp1) {true} = (p.toNNReal : ℝ≥0∞) := by
    unfold bernoulliMeasure
    rw [PMF.toMeasure_apply_singleton
      (PMF.bernoulli p.toNNReal (parameter_le_one p hp0 hp1)) true (by trivial)]
    simp only [PMF.bernoulli_apply, Bool.cond_true]
  rw [mass]
  simpa using Real.coe_toNNReal p hp0

/-- Fixed-parameter IID Bernoulli samples satisfy the original two-sided bound.
The Bernoulli law supplies the mean; it is not an extra mean hypothesis. -/
theorem iid_bernoulli_mean_two_tail {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (hn : 0 < n)
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (sample : Fin n → Ω → Bool) (independent : iIndepFun sample μ)
    (law : ∀ i, IdentDistrib (sample i) id μ (bernoulliMeasure p hp0 hp1))
    (ε : ℝ) (hε : 0 < ε) :
    μ.real {w | ε ≤ |empiricalMean (fun i w => bitValue (sample i w)) w - p|} ≤
      2 * Real.exp (-2 * (n : ℝ) * ε ^ 2) := by
  apply row_mean_two_tail μ hn (fun i w => bitValue (sample i w))
    (independent.comp (fun _ => bitValue) (fun _ => bitValue_measurable))
  · intro i
    simpa only [Function.comp_def] using
      ((law i).comp bitValue_measurable).aemeasurable_fst
  · intro i
    exact Filter.Eventually.of_forall (fun w => bitValue_range (sample i w))
  · intro i
    calc
      (∫ w, bitValue (sample i w) ∂μ) =
          ∫ b, bitValue b ∂bernoulliMeasure p hp0 hp1 := by
        simpa only [Function.comp_def, id_eq] using
          ((law i).comp bitValue_measurable).integral_eq
      _ = p := bernoulli_bit_mean p hp0 hp1
  · exact hε

end
end JurisLean.Candidates.BernoulliMeanInstance20261031

#print axioms JurisLean.Candidates.BernoulliMeanInstance20261031.iid_bernoulli_mean_two_tail