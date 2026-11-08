import JurisLean.ClosedLoopKernel
import JurisLean.SequentialFeedback

/-!
# The stochastic feedback kernel has the existing sequential mean dynamics

Pinned Mathlib: c5ea00351c28e24afc9f0f84379aa41082b1188f.
Build and axiom evidence is recorded for the isolated branch in the engineering appendix.

In a fixed legal context both Bool actions are permitted; the outcome records
whether a response arrived by the observation deadline. The same outcome Y
sets the response coordinate and updates the private parameter. These two real
coordinates are numeric projections, not a complete legal event history.

The probability is extended by clipping outside the invariant unit square.
Inside that square it is exactly SequentialFeedback.responseExample. No clipping
is part of the legal interpretation. The mean equations below are derived from
ClosedLoop.step and its actual measure iteration, not assumed as a contract.
The geometric conclusion concerns expectations, not convergence of sample paths.
-/

namespace LegalMath20261108.UnifiedFeedbackBridge

open MeasureTheory ProbabilityTheory
open ClosedLoop SequentialFeedback
open scoped ENNReal ProbabilityTheory

noncomputable section

abbrev State := ℝ × ℝ

def square : Set State := Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1

lemma measurable_square : MeasurableSet square := measurableSet_Icc.prod measurableSet_Icc

lemma response_bounds (s : State) (hs : s ∈ square) :
    0 ≤ responseExample s.1 s.2 ∧ responseExample s.1 s.2 ≤ 1 := by
  rcases hs with ⟨⟨hx0, hx1⟩, ⟨ht0, ht1⟩⟩
  dsimp [responseExample]
  constructor <;> linarith

def probability (s : State) : ℝ := max 0 (min 1 (responseExample s.1 s.2))

lemma probability_bounds (s : State) : 0 ≤ probability s ∧ probability s ≤ 1 :=
  ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩

lemma probability_eq_response (s : State) (hs : s ∈ square) :
    probability s = responseExample s.1 s.2 := by
  rw [probability, min_eq_right (response_bounds s hs).2,
    max_eq_right (response_bounds s hs).1]

lemma measurable_probability : Measurable probability := by
  unfold probability responseExample
  fun_prop

def coin (s : State) : Measure Bool :=
  ENNReal.ofReal (1 - probability s) • Measure.dirac false +
    ENNReal.ofReal (probability s) • Measure.dirac true

lemma measurable_coin : Measurable coin := by
  unfold coin
  exact ((ENNReal.measurable_ofReal.comp
    (measurable_const.sub measurable_probability)).smul_measure (Measure.dirac false)).add
      ((ENNReal.measurable_ofReal.comp measurable_probability).smul_measure (Measure.dirac true))

instance coin_probability (s : State) : IsProbabilityMeasure (coin s) where
  measure_univ := by
    simp only [coin, Measure.add_apply, Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
    rw [← ENNReal.ofReal_add (sub_nonneg.mpr (probability_bounds s).2)
      (probability_bounds s).1]
    simp

def outcomeKernel : Kernel (State × Bool) Bool where
  toFun := fun z => coin z.1
  measurable' := measurable_coin.comp measurable_fst

instance outcome_markov : IsMarkovKernel outcomeKernel where
  isProbabilityMeasure z := coin_probability z.1

def model : Dynamics ℝ ℝ Bool Bool ℝ where
  policy := Kernel.const State RepaymentExample.fair
  outcome := outcomeKernel
  append := fun _ _ y => RepaymentExample.bit y
  measure := fun _ _ y => RepaymentExample.bit y
  learn := learnExample
  measurable_append := RepaymentExample.measurable_bit.comp measurable_snd.snd
  measurable_measure := RepaymentExample.measurable_bit.comp measurable_snd.snd
  measurable_learn := by unfold learnExample; fun_prop

instance model_policy_markov : IsMarkovKernel model.policy := by
  change IsMarkovKernel (Kernel.const State RepaymentExample.fair)
  infer_instance

instance model_outcome_markov : IsMarkovKernel model.outcome := outcome_markov

/-- A name for the actual update, independent of which of the two permitted actions was drawn. -/
def after (s : State) (y : Bool) : State := update model (s, (false, y))

theorem update_eq_after (s : State) (a y : Bool) : update model (s, (a, y)) = after s y := rfl

theorem after_formula (s : State) (y : Bool) :
    after s y = (RepaymentExample.bit y, learnExample s.2 (RepaymentExample.bit y)) := rfl

/-- An equality of the actual ClosedLoop.step measure, not just of selected readouts. -/
theorem step_two_atoms (s : State) :
    step model s = ENNReal.ofReal (1 - probability s) • Measure.dirac (after s false) +
      ENNReal.ofReal (probability s) • Measure.dirac (after s true) := by
  ext B hB
  rw [step_apply model s hB, joint, Kernel.compProd_apply]
  · change (∫⁻ _a : Bool, coin s ((after s) ⁻¹' B) ∂model.policy s) = _
    rw [lintegral_const, measure_univ, mul_one]
    simp [coin, Measure.add_apply, smul_eq_mul, Set.indicator_apply]
  · exact ((measurable_update model).comp (measurable_const.prodMk measurable_id)) hB

lemma after_in_square (s : State) (hs : s ∈ square) (y : Bool) : after s y ∈ square := by
  rcases hs with ⟨⟨hx0, hx1⟩, ⟨ht0, ht1⟩⟩
  rw [after_formula]
  cases y <;> norm_num [square, RepaymentExample.bit, learnExample] <;>
    constructor <;> linarith

theorem step_invariant (s : State) (hs : s ∈ square) :
    ∀ᵐ t ∂step model s, t ∈ square := by
  rw [ae_iff, step_two_atoms]
  simp [Measure.add_apply, smul_eq_mul, after_in_square s hs false, after_in_square s hs true]

/-- Every real readout is integrable against this finite two-point step measure. -/
lemma integrable_step (s : State) (f : State → ℝ) : Integrable f (step model s) := by
  rw [step_two_atoms]
  exact ((integrable_dirac (f := f) (a := after s false) (by simp)).smul_measure
    (c := ENNReal.ofReal (1 - probability s)) (by simp)).add_measure
      ((integrable_dirac (f := f) (a := after s true) (by simp)).smul_measure
        (c := ENNReal.ofReal (probability s)) (by simp))

theorem integral_step (s : State) (f : State → ℝ) :
    ∫ t, f t ∂step model s =
      (1 - probability s) * f (after s false) + probability s * f (after s true) := by
  rw [step_two_atoms, integral_add_measure
    ((integrable_dirac (f := f) (a := after s false) (by simp)).smul_measure
      (c := ENNReal.ofReal (1 - probability s)) (by simp))
    ((integrable_dirac (f := f) (a := after s true) (by simp)).smul_measure
      (c := ENNReal.ofReal (probability s)) (by simp))]
  simp [ENNReal.toReal_ofReal (probability_bounds s).1,
    ENNReal.toReal_ofReal (sub_nonneg.mpr (probability_bounds s).2), smul_eq_mul]

def mean (μ : Measure State) : State := (∫ s, s.1 ∂μ, ∫ s, s.2 ∂μ)

/-- Both coordinates use one and the same step law and the same sampled outcome. -/
theorem conditional_mean (s : State) (hs : s ∈ square) :
    mean (step model s) = exampleStep s := by
  apply Prod.ext
  · change (∫ t, t.1 ∂step model s) = _
    rw [integral_step, probability_eq_response s hs]
    simp [after_formula, RepaymentExample.bit, exampleStep, advance, responseExample]
  · change (∫ t, t.2 ∂step model s) = _
    rw [integral_step, probability_eq_response s hs]
    norm_num [after_formula, RepaymentExample.bit, exampleStep, advance,
      learnExample, responseExample] <;> ring

/-- The existing cross-coupled contraction now controls the actual conditional mean. -/
theorem conditional_mean_bound (s : State) (hs : s ∈ square) :
    max |(mean (step model s)).1 - 1/2| |(mean (step model s)).2 - 1/2| ≤
      (3/4 : ℝ) * max |s.1 - 1/2| |s.2 - 1/2| := by
  rw [conditional_mean s hs]
  exact example_error_bound s.1 s.2

/-! Measure iteration: preserve support, prove integrability, then use the actual
kernel tower identity and the affine formula. No mean recursion is an assumption. -/

lemma next_supported (μ : Measure State) (hμ : ∀ᵐ s ∂μ, s ∈ square) :
    ∀ᵐ t ∂(step model ∘ₘ μ), t ∈ square := by
  apply Measure.ae_comp_of_ae_ae measurable_square
  filter_upwards [hμ] with s hs
  exact step_invariant s hs

lemma coordinates_integrable (μ : Measure State) [IsFiniteMeasure μ]
    (hμ : ∀ᵐ s ∂μ, s ∈ square) :
    Integrable (fun s : State => s.1) μ ∧ Integrable (fun s : State => s.2) μ := by
  constructor
  · apply (integrable_const (1 : ℝ)).mono' measurable_fst.aestronglyMeasurable
    filter_upwards [hμ] with s hs
    simpa only [Real.norm_eq_abs, abs_of_nonneg hs.1.1] using hs.1.2
  · apply (integrable_const (1 : ℝ)).mono' measurable_snd.aestronglyMeasurable
    filter_upwards [hμ] with s hs
    simpa only [Real.norm_eq_abs, abs_of_nonneg hs.2.1] using hs.2.2

lemma integral_next (μ : Measure State) [IsProbabilityMeasure μ] (f : State → ℝ)
    (hf : Integrable f (step model ∘ₘ μ)) :
    ∫ t, f t ∂(step model ∘ₘ μ) = ∫ s, ∫ t, f t ∂step model s ∂μ := by
  rw [Measure.comp_eq_comp_const_apply] at hf ⊢
  simpa using (Kernel.integral_comp (κ := Kernel.const Unit μ) (η := step model) (a := ()) hf)

lemma integral_affine (μ : Measure State) [IsProbabilityMeasure μ]
    (hμ : ∀ᵐ s ∂μ, s ∈ square) (a b c : ℝ) :
    ∫ s, a * s.1 + b * s.2 + c ∂μ = a * (mean μ).1 + b * (mean μ).2 + c := by
  obtain ⟨hx, ht⟩ := coordinates_integrable μ hμ
  calc
    _ = (∫ s, a * s.1 + b * s.2 ∂μ) + (∫ _s : State, c ∂μ) :=
      integral_add (f := fun s => a * s.1 + b * s.2) (g := fun _ => c)
        ((hx.const_mul a).add (ht.const_mul b)) (integrable_const c)
    _ = (∫ s, a * s.1 ∂μ) + (∫ s, b * s.2 ∂μ) + (∫ _s : State, c ∂μ) :=
      congrArg (fun r : ℝ => r + (∫ _s : State, c ∂μ))
        (integral_add (f := fun s => a * s.1) (g := fun s => b * s.2)
          (hx.const_mul a) (ht.const_mul b))
    _ = _ := by simp [mean, integral_const_mul]

theorem mean_next (μ : Measure State) [IsProbabilityMeasure μ]
    (hμ : ∀ᵐ s ∂μ, s ∈ square) :
    mean (step model ∘ₘ μ) = exampleStep (mean μ) := by
  obtain ⟨hx, ht⟩ := coordinates_integrable (step model ∘ₘ μ) (next_supported μ hμ)
  apply Prod.ext
  · change (∫ t, t.1 ∂(step model ∘ₘ μ)) = _
    rw [integral_next μ _ hx]
    calc
      _ = ∫ s, (exampleStep s).1 ∂μ := by
        apply integral_congr_ae
        filter_upwards [hμ] with s hs
        exact congrArg Prod.fst (conditional_mean s hs)
      _ = ∫ s, (1/4 : ℝ) * s.1 + (1/2 : ℝ) * s.2 + 1/8 ∂μ := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (fun s => by
          rcases s with ⟨x, t⟩
          dsimp only
          rw [example_step_formula]
          dsimp
          ring)
      _ = (1/4 : ℝ) * (mean μ).1 + (1/2 : ℝ) * (mean μ).2 + 1/8 :=
        integral_affine μ hμ _ _ _
      _ = (exampleStep (mean μ)).1 := by rw [example_step_formula]; dsimp; ring
  · change (∫ t, t.2 ∂(step model ∘ₘ μ)) = _
    rw [integral_next μ _ ht]
    calc
      _ = ∫ s, (exampleStep s).2 ∂μ := by
        apply integral_congr_ae
        filter_upwards [hμ] with s hs
        exact congrArg Prod.snd (conditional_mean s hs)
      _ = ∫ s, (1/8 : ℝ) * s.1 + (1/2 : ℝ) * s.2 + 3/16 ∂μ := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (fun s => by
          rcases s with ⟨x, t⟩
          dsimp only
          rw [example_step_formula]
          dsimp
          ring)
      _ = (1/8 : ℝ) * (mean μ).1 + (1/2 : ℝ) * (mean μ).2 + 3/16 :=
        integral_affine μ hμ _ _ _
      _ = (exampleStep (mean μ)).2 := by rw [example_step_formula]; dsimp; ring

def law (μ₀ : Measure State) : ℕ → Measure State
  | 0 => μ₀
  | n + 1 => step model ∘ₘ law μ₀ n

instance law_probability (μ₀ : Measure State) [IsProbabilityMeasure μ₀] (n : ℕ) :
    IsProbabilityMeasure (law μ₀ n) := by
  induction n with
  | zero => exact inferInstanceAs (IsProbabilityMeasure μ₀)
  | succ n ih =>
    letI := ih
    change IsProbabilityMeasure (step model ∘ₘ law μ₀ n)
    infer_instance

theorem law_supported (μ₀ : Measure State) (h₀ : ∀ᵐ s ∂μ₀, s ∈ square) (n : ℕ) :
    ∀ᵐ s ∂law μ₀ n, s ∈ square := by
  induction n with
  | zero => exact h₀
  | succ n ih => exact next_supported (law μ₀ n) ih

theorem mean_law (μ₀ : Measure State) [IsProbabilityMeasure μ₀]
    (h₀ : ∀ᵐ s ∂μ₀, s ∈ square) (n : ℕ) :
    mean (law μ₀ n) = iterateExample n (mean μ₀) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change mean (step model ∘ₘ law μ₀ n) = exampleStep (iterateExample n (mean μ₀))
    rw [mean_next (law μ₀ n) (law_supported μ₀ h₀ n), ih]

/-- The geometric mean bound is for iterates of the very same stochastic kernel. -/
theorem law_mean_geometric_bound (μ₀ : Measure State) [IsProbabilityMeasure μ₀]
    (h₀ : ∀ᵐ s ∂μ₀, s ∈ square) (n : ℕ) :
    max |(mean (law μ₀ n)).1 - 1/2| |(mean (law μ₀ n)).2 - 1/2| ≤
      (3/4 : ℝ)^n * max |(mean μ₀).1 - 1/2| |(mean μ₀).2 - 1/2| := by
  rw [mean_law μ₀ h₀ n]
  exact example_geometric_bound n (mean μ₀)

end
end LegalMath20261108.UnifiedFeedbackBridge
