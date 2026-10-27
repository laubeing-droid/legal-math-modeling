import JurisLean.Candidates.Final20261021.Harness
import JurisLean.Candidates.AdaptiveRoundLedger20261027
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Analysis.SpecificLimits.Basic

/-!
Original 02.4: genuine conditional probabilities on one common measure imply
finite union bounds without independence. Countably many steps need a summable
budget. An actual infinite Bernoulli product law supplies the independent
constant-risk counterexample. No number called a confidence score supplies the
conditional premise; changing the learner or history does not renew it.
-/

namespace JurisLean.Candidates.HarnessRisk20261027

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology
open JurisLean.Candidates.Final20261021

noncomputable section

def eventRate {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (population event : Set Ω) : Result ℝ :=
  if 0 < μ.real population then .known (μ.real (population ∩ event) / μ.real population)
  else .unknown .notIdentified

def violationAndBlockingRates {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (accepted admissible unsafe : Set Ω) : Result ℝ × Result ℝ :=
  (eventRate μ accepted unsafe, eventRate μ admissible acceptedᶜ)

theorem reported_population_rate_is_a_probability {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (population event : Set Ω) (rate : ℝ)
    (reported : eventRate μ population event = .known rate) : 0 ≤ rate ∧ rate ≤ 1 := by
  unfold eventRate at reported
  split at reported
  · rename_i positive
    have same := Result.known.inj reported
    rw [← same]
    constructor
    · exact div_nonneg measureReal_nonneg positive.le
    · apply (div_le_iff₀ positive).mpr
      simpa using (measureReal_mono (μ := μ) (Set.inter_subset_left (s := population) (t := event)))
  · cases reported

theorem zero_population_is_not_zero_risk {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (population event : Set Ω) (emptyMass : μ.real population = 0) :
    eventRate μ population event = .unknown .notIdentified := by
  simp [eventRate, emptyMass]

theorem conditional_risk_implies_expected_marginal {Ω : Type*} [m₀ : MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (past : MeasurableSpace Ω) (information : past ≤ m₀)
    (bad : Set Ω) (measurable : @MeasurableSet Ω m₀ bad) (budget : Ω → ℝ)
    (integrable : Integrable budget μ)
    (conditional : ∀ᵐ w ∂μ, (μ[bad.indicator (fun _ => (1 : ℝ)) | past]) w ≤ budget w) :
    μ.real bad ≤ ∫ w, budget w ∂μ := by
  calc
    μ.real bad = ∫ w, bad.indicator (fun _ => (1 : ℝ)) w ∂μ :=
      (integral_indicator_one (μ := μ) measurable).symm
    _ = ∫ w, (μ[bad.indicator (fun _ => (1 : ℝ)) | past]) w ∂μ :=
      (integral_condExp information).symm
    _ ≤ _ := integral_mono_ae integrable_condExp integrable conditional

theorem conditional_risk_implies_constant_marginal {Ω : Type*} [m₀ : MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (past : MeasurableSpace Ω) (information : past ≤ m₀)
    (bad : Set Ω) (measurable : @MeasurableSet Ω m₀ bad) (δ : ℝ)
    (conditional : ∀ᵐ w ∂μ, (μ[bad.indicator (fun _ => (1 : ℝ)) | past]) w ≤ δ) :
    μ.real bad ≤ δ := by
  simpa using conditional_risk_implies_expected_marginal (m₀ := m₀) μ past information bad measurable
    (fun _ => δ) (integrable_const δ) conditional

-- past t is the information before attempt t. Any filtration is a special
-- case: monotonicity is unnecessary for this implication, and independence is
-- not an assumption. Predictable random budgets give expected total spend.
theorem finite_conditional_union_bound {Ω I : Type} [m₀ : MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (attempts : Finset I)
    (past : I → MeasurableSpace Ω) (information : ∀ t, past t ≤ m₀)
    (bad : I → Set Ω) (measurable : ∀ t, MeasurableSet (bad t)) (δ : I → ℝ)
    (conditional : ∀ t ∈ attempts, ∀ᵐ w ∂μ,
      (μ[(bad t).indicator (fun _ => (1 : ℝ)) | past t]) w ≤ δ t) :
    μ.real (⋃ t ∈ attempts, bad t) ≤ ∑ t ∈ attempts, δ t := by
  apply Harness.risk_union_in_declared_measure μ attempts bad δ
  intro t member
  exact conditional_risk_implies_constant_marginal (m₀ := m₀) μ (past t) (information t)
    (bad t) (measurable t) (δ t) (conditional t member)

theorem finite_adaptive_union_bound {Ω I : Type} [m₀ : MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (attempts : Finset I)
    (past : I → MeasurableSpace Ω) (information : ∀ t, past t ≤ m₀)
    (bad : I → Set Ω) (measurable : ∀ t, MeasurableSet (bad t)) (budget : I → Ω → ℝ)
    (integrable : ∀ t, Integrable (budget t) μ)
    (conditional : ∀ t ∈ attempts, ∀ᵐ w ∂μ,
      (μ[(bad t).indicator (fun _ => (1 : ℝ)) | past t]) w ≤ budget t w) :
    μ.real (⋃ t ∈ attempts, bad t) ≤ ∫ w, ∑ t ∈ attempts, budget t w ∂μ := by
  rw [integral_finsetSum _ (fun t _ => integrable t)]
  apply Harness.risk_union_in_declared_measure μ attempts bad
  intro t member
  exact conditional_risk_implies_expected_marginal (m₀ := m₀) μ (past t) (information t)
    (bad t) (measurable t) (budget t) (integrable t) (conditional t member)

theorem countable_summable_risk_budget {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (bad : Nat → Set Ω) (δ : Nat → ℝ)
    (nonnegative : ∀ t, 0 ≤ δ t) (summable : Summable δ)
    (marginal : ∀ t, μ.real (bad t) ≤ δ t) :
    μ.real (⋃ t, bad t) ≤ ∑' t, δ t := by
  apply ENNReal.toReal_le_of_le_ofReal (tsum_nonneg nonnegative)
  calc
    μ (⋃ t, bad t) ≤ ∑' t, μ (bad t) := measure_iUnion_le bad
    _ ≤ ∑' t, ENNReal.ofReal (δ t) := ENNReal.tsum_le_tsum fun t =>
      (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top μ (bad t)) (nonnegative t)).mpr (marginal t)
    _ = ENNReal.ofReal (∑' t, δ t) := (ENNReal.ofReal_tsum_of_nonneg nonnegative summable).symm

theorem countable_conditional_risk_budget {Ω : Type*} [m₀ : MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (past : Nat → MeasurableSpace Ω)
    (information : ∀ t, past t ≤ m₀) (bad : Nat → Set Ω)
    (measurable : ∀ t, MeasurableSet (bad t)) (δ : Nat → ℝ)
    (nonnegative : ∀ t, 0 ≤ δ t) (summable : Summable δ)
    (conditional : ∀ t, ∀ᵐ w ∂μ,
      (μ[(bad t).indicator (fun _ => (1 : ℝ)) | past t]) w ≤ δ t) :
    μ.real (⋃ t, bad t) ≤ ∑' t, δ t := by
  apply countable_summable_risk_budget μ bad δ nonnegative summable
  exact fun t => conditional_risk_implies_constant_marginal (m₀ := m₀) μ (past t) (information t)
    (bad t) (measurable t) (δ t) (conditional t)

-- A concrete probability measure, not an assumed sequence of risk values.
local instance : MeasurableSpace Bool := ⊤

def bernoulliPaths (p : ℝ≥0) (hp : p ≤ 1) : Measure (Nat → Bool) :=
  Measure.infinitePi (fun _ : Nat => (PMF.bernoulli p hp).toMeasure)

instance bernoulli_paths_probability (p : ℝ≥0) (hp : p ≤ 1) :
    IsProbabilityMeasure (bernoulliPaths p hp) := by
  unfold bernoulliPaths
  infer_instance

theorem bernoulli_coordinates_are_independent (p : ℝ≥0) (hp : p ≤ 1) :
    iIndepFun (fun (t : Nat) (path : Nat → Bool) => path t) (bernoulliPaths p hp) := by
  exact iIndepFun_infinitePi (X := fun _ (b : Bool) => b) (fun _ => measurable_id)

theorem bernoulli_cylinder_probability (p : ℝ≥0) (hp : p ≤ 1) (times : Finset Nat) (b : Bool) :
    bernoulliPaths p hp (Set.pi (times : Set Nat) (fun _ => ({b} : Set Bool))) =
      (if b then (p : ℝ≥0∞) else ((1 - p : ℝ≥0) : ℝ≥0∞)) ^ times.card := by
  have singleton : (PMF.bernoulli p hp).toMeasure ({b} : Set Bool) =
      (if b then (p : ℝ≥0∞) else ((1 - p : ℝ≥0) : ℝ≥0∞)) := by
    rw [(PMF.bernoulli p hp).toMeasure_apply_singleton b (by trivial), PMF.bernoulli_apply]
    cases b <;> rfl
  unfold bernoulliPaths
  rw [Measure.infinitePi_pi _ (fun _ _ => (show MeasurableSet ({b} : Set Bool) from by trivial))]
  simp [singleton]

def failureAt (t : Nat) : Set (Nat → Bool) := {path | path t = true}

theorem bernoulli_one_attempt_risk (p : ℝ≥0) (hp : p ≤ 1) (t : Nat) :
    (bernoulliPaths p hp).real (failureAt t) = (p : ℝ) := by
  have same : failureAt t = Set.pi ({t} : Set Nat) (fun _ => ({true} : Set Bool)) := by
    ext path
    simp [failureAt, Set.mem_pi]
  rw [Measure.real, same]
  have mass := bernoulli_cylinder_probability p hp {t} true
  simpa using congrArg ENNReal.toReal mass

theorem no_failure_is_the_false_cylinder (T : Nat) :
    (⋃ t ∈ Finset.range T, failureAt t)ᶜ =
      Set.pi (Finset.range T : Set Nat) (fun _ => ({false} : Set Bool)) := by
  ext path
  simp [failureAt, Set.mem_pi, Bool.not_eq_true]

theorem independent_constant_risk_accumulates (p : ℝ≥0) (hp : p ≤ 1) (T : Nat) :
    (bernoulliPaths p hp).real (⋃ t ∈ Finset.range T, failureAt t) =
      1 - (1 - (p : ℝ)) ^ T := by
  have cylinder := bernoulli_cylinder_probability p hp (Finset.range T) false
  have safeMass : (bernoulliPaths p hp).real (⋃ t ∈ Finset.range T, failureAt t)ᶜ =
      (1 - (p : ℝ)) ^ T := by
    rw [no_failure_is_the_false_cylinder, Measure.real, cylinder]
    simp [ENNReal.toReal_pow, NNReal.coe_sub hp]
  have measurable : MeasurableSet (⋃ t ∈ Finset.range T, failureAt t) := by
    apply MeasurableSet.iUnion
    intro t
    apply MeasurableSet.iUnion
    intro _
    exact (measurable_pi_apply t) (show MeasurableSet ({true} : Set Bool) from by trivial)
  have complement := measureReal_add_measureReal_compl (μ := bernoulliPaths p hp) measurable
  rw [safeMass, probReal_univ] at complement
  linarith

theorem positive_constant_risk_has_no_fixed_subunit_horizon_limit
    (p : ℝ≥0) (hp : p ≤ 1) (positive : 0 < p) :
    Tendsto (fun T => (bernoulliPaths p hp).real (⋃ t ∈ Finset.range T, failureAt t))
      atTop (𝓝 1) := by
  have bounded : (p : ℝ) ≤ 1 := by exact_mod_cast hp
  have strictlyPositive : (0 : ℝ) < (p : ℝ) := by exact_mod_cast positive
  have vanish : Tendsto (fun T : Nat => (1 - (p : ℝ)) ^ T) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by linarith) (by linarith)
  simpa only [independent_constant_risk_accumulates, sub_zero] using
    (tendsto_const_nhds.sub vanish : Tendsto (fun T => (1 : ℝ) - (1 - (p : ℝ)) ^ T) atTop (𝓝 (1 - 0)))

end

-- The finite executable check enumerates every binary path with its product
-- mass. It is a reproducible rational projection of the constructed law, not
-- a replacement for the measure-theoretic theorem above.
def finitePaths (δ : ℚ) : Nat → List (List Bool × ℚ)
  | 0 => [([], 1)]
  | T + 1 => (finitePaths δ T).flatMap fun (path, mass) =>
      [(false :: path, (1 - δ) * mass), (true :: path, δ * mass)]

def enumeratedFailureMass (δ : ℚ) (T : Nat) : ℚ :=
  ((finitePaths δ T).filter fun row => row.1.any id).map Prod.snd |>.sum

-- Distinct attempts spend twice even if their per-attempt number is identical.
-- The existing AdaptiveRoundLedger retains charges across replays and learner
-- changes; its actual finite action fold is reused, never reset per call.
theorem two_attempts_are_not_one_budget (δ : ℚ) (positive : 0 < δ) : δ < δ + δ := by linarith

end JurisLean.Candidates.HarnessRisk20261027
