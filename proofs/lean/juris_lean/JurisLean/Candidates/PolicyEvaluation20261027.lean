import JurisLean.Candidates.Final20261021.Policy
import JurisLean.Candidates.Final20261021.Behavior
import JurisLean.Candidates.LearningFiniteClass20261027
import Mathlib.Data.Fintype.BigOperators

/-!
Original 12.3--12.5 / S12: exact finite policy values, clipping and partial
identification. Means describe a frozen population and response mechanism.
Causal consistency/exchangeability and genuine logging/recording probabilities
remain premises of the interpretation; these are not inferred from fit.
-/

namespace JurisLean.Candidates.PolicyEvaluation20261027

open JurisLean.Candidates.Final20261021

def policyValue {X A : Type*} [Fintype X] [Fintype A]
    (mass : X → ℚ) (policy outcome : X → A → ℚ) : ℚ :=
  ∑ x, mass x * ∑ a, policy x a * outcome x a

def importanceValue {X A : Type*} [Fintype X] [Fintype A]
    (mass : X → ℚ) (logging target outcome : X → A → ℚ) : ℚ :=
  ∑ x, mass x * ∑ a, logging x a * (target x a / logging x a) * outcome x a

def clippedValue {X A : Type*} [Fintype X] [Fintype A]
    (mass : X → ℚ) (logging target outcome : X → A → ℚ) (cap : ℚ) : ℚ :=
  ∑ x, mass x * ∑ a, logging x a * min (target x a / logging x a) cap * outcome x a

theorem finite_policy_ipw {X A : Type} [Fintype X] [Fintype A]
    (mass : X → ℚ) (logging target outcome : X → A → ℚ)
    (support : ∀ x a, target x a ≠ 0 → logging x a ≠ 0) :
    importanceValue mass logging target outcome = policyValue mass target outcome :=
  Policy.u12_1_finite_ipw mass logging target outcome support

theorem rational_clipping_loss (w c y : ℚ) (hw : 0 ≤ w) (hc : 0 ≤ c)
    (hy : 0 ≤ y) (hy1 : y ≤ 1) :
    w*y - min w c*y = max (w-c) 0*y ∧
      0 ≤ w*y - min w c*y ∧ w*y - min w c*y ≤ max (w-c) 0 := by
  exact_mod_cast (Policy.u12_3_clipped_bias (w : ℝ) (c : ℝ) (y : ℝ)
    (by exact_mod_cast hw) (by exact_mod_cast hc)
    (by exact_mod_cast hy) (by exact_mod_cast hy1))

def discardedMass {X A : Type*} [Fintype X] [Fintype A]
    (mass : X → ℚ) (logging target : X → A → ℚ) (cap : ℚ) : ℚ :=
  ∑ x, mass x * ∑ a, logging x a * max (target x a / logging x a - cap) 0

theorem finite_clipping_bias_bound {X A : Type*} [Fintype X] [Fintype A]
    (mass : X → ℚ) (logging target outcome : X → A → ℚ) (cap : ℚ)
    (hm : ∀ x, 0 ≤ mass x) (hl : ∀ x a, 0 ≤ logging x a)
    (ht : ∀ x a, 0 ≤ target x a) (hc : 0 ≤ cap)
    (hy : ∀ x a, 0 ≤ outcome x a ∧ outcome x a ≤ 1) :
    0 ≤ importanceValue mass logging target outcome - clippedValue mass logging target outcome cap ∧
      importanceValue mass logging target outcome - clippedValue mass logging target outcome cap ≤
        discardedMass mass logging target cap := by
  have point (x : X) (a : A) := rational_clipping_loss
    (target x a / logging x a) cap (outcome x a)
    (div_nonneg (ht x a) (hl x a)) hc (hy x a).1 (hy x a).2
  have difference :
      importanceValue mass logging target outcome - clippedValue mass logging target outcome cap =
        ∑ x, mass x * ∑ a, logging x a *
          ((target x a / logging x a) * outcome x a -
            min (target x a / logging x a) cap * outcome x a) := by
    unfold importanceValue clippedValue
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro x _
    rw [← mul_sub, ← Finset.sum_sub_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro a _
    ring
  rw [difference]
  constructor
  · exact Finset.sum_nonneg fun x _ => mul_nonneg (hm x)
      (Finset.sum_nonneg fun a _ => mul_nonneg (hl x a) (point x a).2.1)
  · apply Finset.sum_le_sum
    intro x _
    apply mul_le_mul_of_nonneg_left _ (hm x)
    exact Finset.sum_le_sum fun a _ =>
      mul_le_mul_of_nonneg_left (point x a).2.2 (hl x a)

def fillUnsupported {X A : Type*} (logging observed : X → A → ℚ)
    (unknownMean : ℚ) (x : X) (a : A) : ℚ :=
  if logging x a = 0 then unknownMean else observed x a

-- Every bounded completion lies between the two extremal completions.
-- No smooth fitted value is silently assigned to an unsupported action.
theorem unsupported_value_bounds {X A : Type*} [Fintype X] [Fintype A]
    (mass : X → ℚ) (logging target outcome : X → A → ℚ)
    (hm : ∀ x, 0 ≤ mass x) (ht : ∀ x a, 0 ≤ target x a)
    (hy : ∀ x a, 0 ≤ outcome x a ∧ outcome x a ≤ 1) :
    policyValue mass target (fillUnsupported logging outcome 0) ≤ policyValue mass target outcome ∧
      policyValue mass target outcome ≤ policyValue mass target (fillUnsupported logging outcome 1) := by
  constructor
  · apply Finset.sum_le_sum
    intro x _
    apply mul_le_mul_of_nonneg_left _ (hm x)
    apply Finset.sum_le_sum
    intro a _
    apply mul_le_mul_of_nonneg_left _ (ht x a)
    by_cases zero : logging x a = 0
    · simpa [fillUnsupported, zero] using (hy x a).1
    · simp [fillUnsupported, zero]
  · apply Finset.sum_le_sum
    intro x _
    apply mul_le_mul_of_nonneg_left _ (hm x)
    apply Finset.sum_le_sum
    intro a _
    apply mul_le_mul_of_nonneg_left _ (ht x a)
    by_cases zero : logging x a = 0
    · simpa [fillUnsupported, zero] using (hy x a).2
    · simp [fillUnsupported, zero]

-- The following explicit Bernoulli law includes both possible outcomes.
def bernoulliVisibleLaw {X A : Type*} (mass : X → ℚ)
    (logging outcome : X → A → ℚ) (x : X) (a : A) (y : Bool) : ℚ :=
  mass x * logging x a * (if y then outcome x a else 1 - outcome x a)

theorem unsupported_completions_same_visible_law {X A : Type*}
    (mass : X → ℚ) (logging outcome : X → A → ℚ) (u v : ℚ)
    (x : X) (a : A) (y : Bool) :
    bernoulliVisibleLaw mass logging (fillUnsupported logging outcome u) x a y =
      bernoulliVisibleLaw mass logging (fillUnsupported logging outcome v) x a y := by
  by_cases zero : logging x a = 0 <;>
    simp [bernoulliVisibleLaw, fillUnsupported, zero]

def groupMass (_x : Bool) : ℚ := 1/2
def shiftedMass (x : Bool) : ℚ := if x then 4/5 else 1/5
def originalMean (x a : Bool) : ℚ :=
  if x then (if a then 3/10 else 7/10) else (if a then 4/5 else 2/5)
def loggingPolicy (x a : Bool) : ℚ :=
  if x then (if a then 3/4 else 1/4) else (if a then 1/4 else 3/4)
def chooseOne (_x : Bool) (a : Bool) : ℚ := Behavior.indicator a
def chooseZero (_x : Bool) (a : Bool) : ℚ := Behavior.indicator (!a)
def personalized (x a : Bool) : ℚ := if a = !x then 1 else 0
def supportGapLogging (x a : Bool) : ℚ :=
  if x then loggingPolicy x a else if a then 0 else 1

theorem original_policy_values_and_clipping :
    policyValue groupMass loggingPolicy originalMean = 9/20 ∧
    policyValue groupMass chooseOne originalMean = 11/20 ∧
    importanceValue groupMass loggingPolicy chooseOne originalMean = 11/20 ∧
    chooseOne false true / loggingPolicy false true = 4 ∧
    chooseOne true true / loggingPolicy true true = 4/3 ∧
    clippedValue groupMass loggingPolicy chooseOne originalMean 2 = 7/20 ∧
    policyValue groupMass chooseOne originalMean -
      clippedValue groupMass loggingPolicy chooseOne originalMean 2 = 1/5 := by
  norm_num [policyValue, importanceValue, clippedValue, Fintype.sum_bool,
    groupMass, loggingPolicy, chooseOne, originalMean, Behavior.indicator]

theorem original_support_gap_sharp (u : ℚ) (hu : 0 ≤ u) (hu1 : u ≤ 1) :
    policyValue groupMass chooseOne (fillUnsupported supportGapLogging originalMean u) = u/2 + 3/20 ∧
    3/20 ≤ policyValue groupMass chooseOne (fillUnsupported supportGapLogging originalMean u) ∧
    policyValue groupMass chooseOne (fillUnsupported supportGapLogging originalMean u) ≤ 13/20 := by
  have value : policyValue groupMass chooseOne
      (fillUnsupported supportGapLogging originalMean u) = u/2 + 3/20 := by
    norm_num [policyValue, fillUnsupported, supportGapLogging, loggingPolicy, originalMean,
      groupMass, chooseOne, Behavior.indicator, Fintype.sum_bool]
    <;> ring
  rw [value]
  constructor
  · rfl
  · constructor <;> linarith

theorem support_gap_endpoints_observationally_compatible :
    (∀ x a y, bernoulliVisibleLaw groupMass supportGapLogging
      (fillUnsupported supportGapLogging originalMean 0) x a y =
      bernoulliVisibleLaw groupMass supportGapLogging
        (fillUnsupported supportGapLogging originalMean 1) x a y) ∧
    policyValue groupMass chooseOne (fillUnsupported supportGapLogging originalMean 0) = 3/20 ∧
    policyValue groupMass chooseOne (fillUnsupported supportGapLogging originalMean 1) = 13/20 := by
  refine ⟨fun x a y => unsupported_completions_same_visible_law _ _ _ _ _ x a y, ?_, ?_⟩
  · simpa using (original_support_gap_sharp 0 (by norm_num) (by norm_num)).1
  · calc
      _ = (1 : ℚ)/2 + 3/20 := (original_support_gap_sharp 1 (by norm_num) (by norm_num)).1
      _ = 13/20 := by norm_num

theorem heterogeneous_values_change_with_population :
    originalMean false true - originalMean false false = 2/5 ∧
    originalMean true true - originalMean true false = -2/5 ∧
    policyValue groupMass chooseZero originalMean = 11/20 ∧
    policyValue groupMass chooseOne originalMean = 11/20 ∧
    policyValue groupMass personalized originalMean = 3/4 ∧
    policyValue shiftedMass chooseZero originalMean = 16/25 ∧
    policyValue shiftedMass chooseOne originalMean = 2/5 ∧
    policyValue shiftedMass personalized originalMean = 18/25 := by
  norm_num [policyValue, groupMass, shiftedMass, chooseZero, chooseOne, personalized,
    originalMean, Behavior.indicator, Fintype.sum_bool]

-- In the A=1 stratum, one half is recorded with Y=1. The hidden half has
-- Bernoulli mean u. This constructs a full distribution, not just an interval.
def missingJoint (u : ℚ) (recorded y : Bool) : ℚ :=
  (1/2) * if recorded then Behavior.indicator y else if y then u else 1-u

def missingVisibleMass (u : ℚ) (recorded : Bool) (report : Option Bool) : ℚ :=
  ∑ y : Bool, if report = (if recorded then some y else none) then missingJoint u recorded y else 0

def missingPopulationMean (u : ℚ) : ℚ :=
  ∑ r : Bool, ∑ y : Bool, missingJoint u r y * Behavior.indicator y

theorem missing_world_is_probability (u : ℚ) (hu : 0 ≤ u) (hu1 : u ≤ 1) :
    (∑ r : Bool, ∑ y : Bool, missingJoint u r y) = 1 ∧
    (∀ r y, 0 ≤ missingJoint u r y) := by
  constructor
  · norm_num [missingJoint, Behavior.indicator, Fintype.sum_bool]
    <;> ring
  · intro r y
    cases r <;> cases y <;> simp [missingJoint, Behavior.indicator] <;> linarith

theorem missing_outcome_visible_law_independent (u v : ℚ) :
    ∀ r report, missingVisibleMass u r report = missingVisibleMass v r report := by
  intro r report
  fin_cases r <;> fin_cases report <;>
    norm_num [missingVisibleMass, missingJoint, Behavior.indicator, Fintype.sum_bool]
  <;> ring

theorem missing_outcome_interval_sharp (u : ℚ) (hu : 0 ≤ u) (hu1 : u ≤ 1) :
    missingPopulationMean u = (1+u)/2 ∧
    1/2 ≤ missingPopulationMean u ∧ missingPopulationMean u ≤ 1 ∧
    missingPopulationMean 0 = 1/2 ∧ missingPopulationMean 1 = 1 := by
  have value : ∀ v, missingPopulationMean v = (1+v)/2 := by
    intro v
    norm_num [missingPopulationMean, missingJoint, Behavior.indicator, Fintype.sum_bool]
    <;> ring
  refine ⟨value u, ?_, ?_, ?_, ?_⟩
  · rw [value]
    linarith
  · rw [value]
    linarith
  · norm_num [value]
  · norm_num [value]

def firstStageLog (_transition : Bool → Bool) (action : Bool) : Bool × ℚ := (action, 0)
def terminalValue (transition : Bool → Bool) (action : Bool) : ℚ :=
  Behavior.indicator (transition action)

theorem initial_logs_do_not_identify_terminal_value :
    (∀ a, firstStageLog id a = firstStageLog Bool.not a) ∧
    terminalValue id true = 1 ∧ terminalValue Bool.not true = 0 := by
  refine ⟨fun _ => rfl, ?_, ?_⟩ <;> norm_num [terminalValue, Behavior.indicator]

open MeasureTheory ProbabilityTheory
open JurisLean.Candidates.LearningFiniteClass20261027

-- A score is the actual bounded importance-weighted observation for a fixed
-- policy. Its population expectation is a causal value only under the
-- separately stated identification/support/measurement premises above.
theorem bounded_policy_score_uniform {Ω Z H : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Z] {n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (P : Measure Z) [IsProbabilityMeasure P]
    (hn : 0 < n) (policies : Finset H) (nonempty : policies.Nonempty)
    (sample : Fin n → Ω → Z) (sampleMeasurable : ∀ i, Measurable (sample i))
    (independent : iIndepFun sample μ) (law : ∀ i, IdentDistrib (sample i) id μ P)
    (score : H → Z → ℝ) (measurable : ∀ h ∈ policies, Measurable (score h))
    (W : ℝ) (positive : 0 < W)
    (bounded : ∀ h ∈ policies, ∀ z, score h z ∈ Set.Icc (0 : ℝ) W)
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) :
    1 - δ ≤ μ.real {w | ∀ h ∈ policies,
      |empiricalMean (fun i w' => score h (sample i w')) w - ∫ z, score h z ∂P| ≤
        W * finiteRadius n policies.card δ} := by
  have uniform := u01_1_iid_empirical_risk_uniform μ P hn policies nonempty
    sample sampleMeasurable independent law (fun h z => score h z / W)
    (fun h hh => (measurable h hh).div_const W)
    (fun h hh z => ⟨div_nonneg (bounded h hh z).1 positive.le,
      (div_le_one positive).mpr (bounded h hh z).2⟩) δ hδ hδ1
  apply le_trans uniform
  apply measureReal_mono (μ := μ) (h₂ := measure_ne_top μ _)
  intro w hw h hh
  have scaled := hw h hh
  have empirical : empiricalMean (fun i w' => score h (sample i w') / W) w =
      empiricalMean (fun i w' => score h (sample i w')) w / W := by
    simp only [empiricalMean, ← Finset.sum_div]
    ring
  rw [empirical, integral_div, ← sub_div, abs_div, abs_of_pos positive] at scaled
  simpa [mul_comm] using (div_le_iff₀ positive).mp scaled

theorem empirical_policy_winner_regret {H : Type*} (policies : Finset H)
    (value estimate : H → ℝ) (chosen : H) (member : chosen ∈ policies)
    (radius : ℝ) (valid : ∀ h ∈ policies, |estimate h - value h| ≤ radius)
    (winner : ∀ h ∈ policies, estimate h ≤ estimate chosen) :
    ∀ h ∈ policies, value h - value chosen ≤ 2 * radius := by
  intro h hh
  have selected := abs_le.mp (valid chosen member)
  have compared := abs_le.mp (valid h hh)
  have maximizes := winner h hh
  linarith

theorem bounded_policy_winner_probability {Ω Z H : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Z] {n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (P : Measure Z) [IsProbabilityMeasure P]
    (hn : 0 < n) (policies : Finset H) (nonempty : policies.Nonempty)
    (sample : Fin n → Ω → Z) (sampleMeasurable : ∀ i, Measurable (sample i))
    (independent : iIndepFun sample μ) (law : ∀ i, IdentDistrib (sample i) id μ P)
    (score : H → Z → ℝ) (measurable : ∀ h ∈ policies, Measurable (score h))
    (W : ℝ) (positive : 0 < W)
    (bounded : ∀ h ∈ policies, ∀ z, score h z ∈ Set.Icc (0 : ℝ) W)
    (chosen : Ω → H) (member : ∀ w, chosen w ∈ policies)
    (winner : ∀ w h, h ∈ policies →
      empiricalMean (fun i w' => score h (sample i w')) w ≤
        empiricalMean (fun i w' => score (chosen w) (sample i w')) w)
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) :
    1 - δ ≤ μ.real {w | ∀ h ∈ policies,
      (∫ z, score h z ∂P) - (∫ z, score (chosen w) z ∂P) ≤
        2 * (W * finiteRadius n policies.card δ)} := by
  have uniform := bounded_policy_score_uniform μ P hn policies nonempty sample
    sampleMeasurable independent law score measurable W positive bounded δ hδ hδ1
  apply le_trans uniform
  apply measureReal_mono (μ := μ) (h₂ := measure_ne_top μ _)
  intro w hw
  exact empirical_policy_winner_regret policies (fun h => ∫ z, score h z ∂P)
    (fun h => empiricalMean (fun i w' => score h (sample i w')) w)
    (chosen w) (member w) (W * finiteRadius n policies.card δ) hw (winner w)

end JurisLean.Candidates.PolicyEvaluation20261027

