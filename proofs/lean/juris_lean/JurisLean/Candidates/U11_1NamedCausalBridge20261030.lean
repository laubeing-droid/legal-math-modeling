/-
CI_NOT_RUN.

Original 11.3 L119–121: fixed J,t; finite X; binary A; real-valued,
integrable potential outcomes. No finite Ω/U/Y or rational-probability
assumption is introduced.

A fixed J,t is represented by the one probability measure μ and the one
response function below. Observational fit does not establish E_exch.

I_nointerf permits own-action noninterference, or a specified binary
exposure mapping whose response sufficiency and alignment with A and the
two target interventions are stated explicitly.
-/

import Mathlib.Probability.ConditionalProbability
import Mathlib.Probability.Independence.Integration
import Mathlib.MeasureTheory.Integral.Bochner.Set

open scoped BigOperators
open MeasureTheory ProbabilityTheory

namespace JurisLean.Candidates.U11_1NamedCausalBridge20261030

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Same intervention version and the actual observed response are distinct
    clauses of consistency. Neither clause asserts exchangeability. -/
def C_cons
    {V ι : Type*}
    (μ : Measure Ω)
    (response : V → Ω → (ι → Bool) → ℝ)
    (fixedVersion : V) (actualVersion : Ω → V)
    (allocation : Ω → ι → Bool) (Y : Ω → ℝ) : Prop :=
  (∀ᵐ ω ∂μ, actualVersion ω = fixedVersion) ∧
  (∀ᵐ ω ∂μ,
    Y ω = response (actualVersion ω) ω (allocation ω))

/-- For ownExposure i this is noninterference for unit i. For a specified
    binary exposure it states response sufficiency of that exposure;
    merely providing an exposure map does not satisfy this condition. -/
def I_nointerf
    {V ι : Type*}
    (μ : Measure Ω)
    (response : V → Ω → (ι → Bool) → ℝ)
    (fixedVersion : V) (exposure : (ι → Bool) → Bool) : Prop :=
  ∀ᵐ ω ∂μ, ∀ g h : ι → Bool,
    exposure g = exposure h →
      response fixedVersion ω g = response fixedVersion ω h

def ownExposure {ι : Type*} (i : ι) (g : ι → Bool) : Bool := g i

def ownIntervention {ι : Type*} (a : Bool) : ι → Bool := fun _ => a

def potentialOutcome
    {V ι : Type*}
    (response : V → Ω → (ι → Bool) → ℝ)
    (fixedVersion : V) (intervention : Bool → ι → Bool)
    (a : Bool) (ω : Ω) : ℝ :=
  response fixedVersion ω (intervention a)

/-- Blocks the missing semantic entrance in L119: C_cons, the fixed version,
    exposure sufficiency, and actual/target exposure alignment really imply
    Y = Y(A), rather than assuming that equality as a modelling badge. -/
theorem consistency_from_version_and_exposure
    {V ι : Type*}
    (μ : Measure Ω)
    (response : V → Ω → (ι → Bool) → ℝ)
    (fixedVersion : V) (actualVersion : Ω → V)
    (allocation : Ω → ι → Bool) (A : Ω → Bool) (Y : Ω → ℝ)
    (exposure : (ι → Bool) → Bool)
    (intervention : Bool → ι → Bool)
    (targetAligned : ∀ a, exposure (intervention a) = a)
    (observedAligned : ∀ᵐ ω ∂μ, exposure (allocation ω) = A ω)
    (consistent :
      C_cons μ response fixedVersion actualVersion allocation Y)
    (noInterference :
      I_nointerf μ response fixedVersion exposure) :
    Y =ᵐ[μ] fun ω =>
      potentialOutcome response fixedVersion intervention (A ω) ω := by
  filter_upwards
      [consistent.1, consistent.2, noInterference, observedAligned]
      with ω versionEq observedEq responseEq actionEq
  change Y ω = response fixedVersion ω (intervention (A ω))
  rw [observedEq, versionEq]
  exact responseEq _ _ (actionEq.trans (targetAligned (A ω)).symm)

def E_exch
    {S : Type*}
    (μ : Measure Ω) (X : Ω → S) (A : Ω → Bool)
    (potential : Bool → Ω → ℝ) : Prop :=
  ∀ x, μ {ω | X ω = x} ≠ 0 →
    IndepFun
      (fun ω => (potential false ω, potential true ω))
      A
      (ProbabilityTheory.cond μ {ω | X ω = x})

def P_pos
    {S : Type*}
    (μ : Measure Ω) (X : Ω → S) (A : Ω → Bool) : Prop :=
  ∀ x, μ {ω | X ω = x} ≠ 0 → ∀ a : Bool,
    0 < (ProbabilityTheory.cond μ {ω | X ω = x})
      {ω | A ω = a}

/-- Interpreted as an observed conditional mean only when its conditioning
    cell has positive probability. Zero-mass X strata are later multiplied
    by zero and require no positivity assumption. -/
noncomputable def observedCellMean
    {S : Type*}
    (μ : Measure Ω) (X : Ω → S) (A : Ω → Bool)
    (Y : Ω → ℝ) (x : S) (a : Bool) : ℝ :=
  ∫ ω, Y ω ∂ProbabilityTheory.cond μ
    ({ω | X ω = x} ∩ {ω | A ω = a})

/-- Normalization connection needed for the conditional expectations in L121;
    this is the existing cond definition plus integral_smul_measure. -/
private theorem integral_cond_eq
    (μ : Measure Ω) (s : Set Ω) (f : Ω → ℝ) :
    (∫ ω, f ω ∂ProbabilityTheory.cond μ s) =
      (μ.real s)⁻¹ * ∫ ω in s, f ω ∂μ := by
  simp only [ProbabilityTheory.cond, integral_smul_measure,
    ENNReal.toReal_inv, smul_eq_mul, measureReal_def]

/-- Integrability of a potential outcome survives conditioning on a
    nonzero stratum; this supplies the meaning of the conditional means. -/
private theorem integrable_cond
    (μ : Measure Ω) (s : Set Ω) (f : Ω → ℝ)
    (integrable : Integrable f μ) (nonzero : μ s ≠ 0) :
    Integrable f (ProbabilityTheory.cond μ s) := by
  change Integrable f ((μ s)⁻¹ • μ.restrict s)
  exact integrable.restrict.smul_measure (ENNReal.inv_ne_top.mpr nonzero)

/-- The actual observed outcome is integrable as a consequence of binary
    consistency and integrable potential outcomes, not an extra Y-bound. -/
private theorem observed_integrable
    (μ : Measure Ω) (A : Ω → Bool) (measurableA : Measurable A)
    (potential : Bool → Ω → ℝ)
    (potentialIntegrable : ∀ a, Integrable (potential a) μ)
    (Y : Ω → ℝ)
    (consistent : Y =ᵐ[μ] fun ω => potential (A ω) ω) :
    Integrable Y μ := by
  have ht : MeasurableSet {ω | A ω = true} :=
    (measurableSet_singleton true).preimage measurableA
  have hf : MeasurableSet {ω | A ω = false} :=
    (measurableSet_singleton false).preimage measurableA
  have integrableSum :=
    ((potentialIntegrable true).indicator ht).add
      ((potentialIntegrable false).indicator hf)
  apply integrableSum.congr
  filter_upwards [consistent] with ω hω
  cases action : A ω <;>
    simpa [Set.indicator, action] using hω.symm

/-- Multiplying the normalized stratum expectation by its actual mass
    recovers the restricted integral, including the zero-mass case. -/
private theorem weighted_cond_integral
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (s : Set Ω) (f : Ω → ℝ) :
    μ.real s * (∫ ω, f ω ∂ProbabilityTheory.cond μ s) =
      ∫ ω in s, f ω ∂μ := by
  rw [integral_cond_eq]
  by_cases zero : μ s = 0
  · have restrictedZero : μ.restrict s = 0 :=
      Measure.restrict_eq_zero.mpr zero
    simp [restrictedZero, measureReal_def, zero]
  · have realNonzero : μ.real s ≠ 0 :=
      ENNReal.toReal_ne_zero.mpr ⟨zero, measure_ne_top μ s⟩
    field_simp [realNonzero]

/-- Finite X, rather than finite Ω or finite Y, is exactly what permits
    the finite total-expectation decomposition used in L121. -/
private theorem finite_stratified_integral
    {S : Type*} [Fintype S]
    [MeasurableSpace S] [MeasurableSingletonClass S]
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (X : Ω → S) (measurableX : Measurable X)
    (f : Ω → ℝ) (integrable : Integrable f μ) :
    (∫ ω, f ω ∂μ) =
      ∑ x, μ.real {ω | X ω = x} *
        ∫ ω, f ω ∂ProbabilityTheory.cond μ {ω | X ω = x} := by
  classical
  have measurableStrata : ∀ x, MeasurableSet {ω | X ω = x} :=
    fun x => (measurableSet_singleton x).preimage measurableX
  have disjointStrata :
      Pairwise (fun x y : S =>
        Disjoint {ω | X ω = x} {ω | X ω = y}) := by
    intro x y different
    rw [Set.disjoint_left]
    intro ω hx hy
    exact different (hx.symm.trans hy)
  have unionStrata :
      (⋃ x : S, {ω | X ω = x}) = Set.univ := by
    ext ω
    simp
  have partition := integral_iUnion_fintype measurableStrata disjointStrata
    (fun _ => integrable.integrableOn)
  rw [unionStrata, setIntegral_univ] at partition
  calc
    (∫ ω, f ω ∂μ) = ∑ x, ∫ ω in {ω | X ω = x}, f ω ∂μ :=
      partition
    _ = _ := by
      apply Finset.sum_congr rfl
      intro x _
      exact (weighted_cond_integral μ {ω | X ω = x} f).symm

/-- Blocks the statistical identification gap in L119–121.
    Exchangeability is joint independence of the two actual potential
    outcomes and A under the actual X-stratum law. Consistency replaces Y
    only inside the corresponding observed cell; positivity cancels its
    normalization. No equality of observed/potential means is assumed. -/
theorem observed_cell_mean_eq_potential
    {S : Type*} [Fintype S]
    [MeasurableSpace S] [MeasurableSingletonClass S]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → S) (measurableX : Measurable X)
    (A : Ω → Bool) (measurableA : Measurable A)
    (potential : Bool → Ω → ℝ)
    (potentialIntegrable : ∀ a, Integrable (potential a) μ)
    (Y : Ω → ℝ)
    (consistent : Y =ᵐ[μ] fun ω => potential (A ω) ω)
    (exchangeable : E_exch μ X A potential)
    (positive : P_pos μ X A)
    (x : S) (populated : μ {ω | X ω = x} ≠ 0) (a : Bool) :
    Integrable Y
        (ProbabilityTheory.cond μ
          ({ω | X ω = x} ∩ {ω | A ω = a})) ∧
      observedCellMean μ X A Y x a =
        ∫ ω, potential a ω ∂ProbabilityTheory.cond μ {ω | X ω = x} := by
  classical
  let C : Set Ω := {ω | X ω = x}
  let D : Set Ω := {ω | A ω = a}
  let ν : Measure Ω := ProbabilityTheory.cond μ C
  have measurableC : MeasurableSet C :=
    (measurableSet_singleton x).preimage measurableX
  have measurableD : MeasurableSet D :=
    (measurableSet_singleton a).preimage measurableA
  haveI : IsProbabilityMeasure ν :=
    ProbabilityTheory.cond_isProbabilityMeasure populated
  have actionNonzero : ν D ≠ 0 :=
    ne_of_gt (positive x populated a)
  have jointNonzero : μ (C ∩ D) ≠ 0 := by
    intro zero
    apply actionNonzero
    change (ProbabilityTheory.cond μ C) D = 0
    rw [ProbabilityTheory.cond_apply measurableC μ D, zero, mul_zero]
  have observedIntegrable :=
    observed_integrable μ A measurableA potential potentialIntegrable Y consistent
  refine ⟨integrable_cond μ (C ∩ D) Y observedIntegrable jointNonzero, ?_⟩
  have potentialIntegrableν : ∀ b, Integrable (potential b) ν :=
    fun b => integrable_cond μ C (potential b) (potentialIntegrable b) populated
  let flag : Bool → ℝ := fun b => if b = a then 1 else 0
  have measurableFlag : Measurable flag := measurable_of_finite _
  have independent :
      IndepFun (potential a) (fun ω => flag (A ω)) ν := by
    have independentPair := exchangeable x populated
    cases a with
    | false =>
        simpa [Function.comp_def] using
          independentPair.comp measurable_fst measurableFlag
    | true =>
        simpa [Function.comp_def] using
          independentPair.comp measurable_snd measurableFlag
  have factorized :=
    independent.integral_fun_mul_eq_mul_integral
      (potentialIntegrableν a).aestronglyMeasurable
      (measurableFlag.comp measurableA).aestronglyMeasurable
  have flagIntegral : (∫ ω, flag (A ω) ∂ν) = ν.real D := by
    simpa [flag, D, Set.indicator] using
      (integral_indicator_one (μ := ν) measurableD)
  have flagProduct :
      (fun ω => potential a ω * flag (A ω)) =
        D.indicator (potential a) := by
    funext ω
    by_cases action : A ω = a <;>
      simp [flag, D, Set.indicator, action]
  have restrictedFactor :
      (∫ ω in D, potential a ω ∂ν) =
        (∫ ω, potential a ω ∂ν) * ν.real D := by
    rw [← integral_indicator measurableD, ← flagProduct]
    rw [factorized, flagIntegral]
  have observedRestricted :
      (∫ ω in C ∩ D, Y ω ∂μ) =
        ∫ ω in C ∩ D, potential a ω ∂μ := by
    apply setIntegral_congr_ae (measurableC.inter measurableD)
    filter_upwards [consistent] with ω hω
    intro belongs
    have actionEq : A ω = a := belongs.2
    simpa only [actionEq] using hω
  calc
    observedCellMean μ X A Y x a =
        ∫ ω, potential a ω ∂ProbabilityTheory.cond μ (C ∩ D) := by
      change (∫ ω, Y ω ∂ProbabilityTheory.cond μ (C ∩ D)) = _
      rw [integral_cond_eq, integral_cond_eq, observedRestricted]
    _ = ∫ ω, potential a ω ∂ProbabilityTheory.cond ν D := by
      change (∫ ω, potential a ω ∂ProbabilityTheory.cond μ (C ∩ D)) =
        ∫ ω, potential a ω
          ∂ProbabilityTheory.cond (ProbabilityTheory.cond μ C) D
      rw [ProbabilityTheory.cond_cond_eq_cond_inter measurableC measurableD μ]
    _ = ∫ ω, potential a ω ∂ν := by
      rw [integral_cond_eq, restrictedFactor]
      have realNonzero : ν.real D ≠ 0 :=
        ENNReal.toReal_ne_zero.mpr
          ⟨actionNonzero, measure_ne_top ν D⟩
      field_simp [realNonzero] <;> ring

/-- Blocks L121 itself: the named semantic and statistical conditions imply
    the observed g formula on the original population. The actual Y is also
    proved integrable. Zero-mass X strata require neither exchangeability
    nor treatment positivity. -/
theorem finite_g_formula_from_conditions
    {S V ι : Type*} [Fintype S]
    [MeasurableSpace S] [MeasurableSingletonClass S]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → S) (measurableX : Measurable X)
    (A : Ω → Bool) (measurableA : Measurable A)
    (Y : Ω → ℝ)
    (response : V → Ω → (ι → Bool) → ℝ)
    (fixedVersion : V) (actualVersion : Ω → V)
    (allocation : Ω → ι → Bool)
    (exposure : (ι → Bool) → Bool)
    (intervention : Bool → ι → Bool)
    (targetAligned : ∀ a, exposure (intervention a) = a)
    (observedAligned : ∀ᵐ ω ∂μ, exposure (allocation ω) = A ω)
    (consistent :
      C_cons μ response fixedVersion actualVersion allocation Y)
    (noInterference :
      I_nointerf μ response fixedVersion exposure)
    (potentialIntegrable :
      ∀ a, Integrable
        (potentialOutcome response fixedVersion intervention a) μ)
    (exchangeable :
      E_exch μ X A (potentialOutcome response fixedVersion intervention))
    (positive : P_pos μ X A) :
    Integrable Y μ ∧
      (∫ ω,
        potentialOutcome response fixedVersion intervention true ω -
          potentialOutcome response fixedVersion intervention false ω ∂μ) =
        ∑ x,
          (observedCellMean μ X A Y x true -
            observedCellMean μ X A Y x false) *
              μ.real {ω | X ω = x} := by
  have actualConsistency :=
    consistency_from_version_and_exposure μ response fixedVersion
      actualVersion allocation A Y exposure intervention
      targetAligned observedAligned consistent noInterference
  refine ⟨observed_integrable μ A measurableA
    (potentialOutcome response fixedVersion intervention)
    potentialIntegrable Y actualConsistency, ?_⟩
  calc
    _ = ∑ x, μ.real {ω | X ω = x} *
        ∫ ω,
          potentialOutcome response fixedVersion intervention true ω -
            potentialOutcome response fixedVersion intervention false ω
          ∂ProbabilityTheory.cond μ {ω | X ω = x} :=
      finite_stratified_integral μ X measurableX _
        ((potentialIntegrable true).sub (potentialIntegrable false))
    _ = _ := by
      apply Finset.sum_congr rfl
      intro x _
      by_cases zero : μ {ω | X ω = x} = 0
      · simp [measureReal_def, zero]
      · have meanTrue :=
          (observed_cell_mean_eq_potential μ X measurableX A measurableA
            (potentialOutcome response fixedVersion intervention)
            potentialIntegrable Y actualConsistency exchangeable positive
            x zero true).2
        have meanFalse :=
          (observed_cell_mean_eq_potential μ X measurableX A measurableA
            (potentialOutcome response fixedVersion intervention)
            potentialIntegrable Y actualConsistency exchangeable positive
            x zero false).2
        rw [meanTrue, meanFalse,
          integral_sub
            (integrable_cond μ {ω | X ω = x}
              (potentialOutcome response fixedVersion intervention true)
              (potentialIntegrable true) zero)
            (integrable_cond μ {ω | X ω = x}
              (potentialOutcome response fixedVersion intervention false)
              (potentialIntegrable false) zero)]
        ring

end JurisLean.Candidates.U11_1NamedCausalBridge20261030