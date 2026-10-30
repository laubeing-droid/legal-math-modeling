/-
CI_NOT_RUN.

Blocker: master U12.1 and original 12.3 L119 require actual consistency,
exchangeability and target support to identify the actual logging score with
the frozen intervention-policy value. A constructed Bernoulli logging law
does not by itself supply that causal or measurement interpretation.

The sample and covariate spaces below are arbitrary measurable spaces.
Only the action set is finite. Potential outcomes are real and integrable.
The actual conditional law is Mathlib's condDistrib of the actual variables
under P. Its standard-Borel result space is the finite potential vector and
the action, not the original sample or covariate space. No uniform positive
lower bound on logging probabilities is assumed.
-/

import Mathlib.Probability.Kernel.CondDistrib
import Mathlib.Probability.Independence.Integration
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import JurisLean.Candidates.MeasuredPolicy20261027

open scoped BigOperators
open MeasureTheory ProbabilityTheory

namespace JurisLean.Candidates.U12_1CausalPolicyBridge20261030

abbrev JointOutcome (Act : Type*) := (Act → ℝ) × Act

section Generic

variable {Ω XSpace Act : Type*}
  [MeasurableSpace Ω] [MeasurableSpace XSpace]
  [Fintype Act] [MeasurableSpace Act] [MeasurableSingletonClass Act]

def jointObservation (actualA : Ω → Act) (potential : Act → Ω → ℝ)
    (ω : Ω) : JointOutcome Act :=
  (fun a => potential a ω, actualA ω)

/-- The actual action on a probability space supplies nonemptiness internally;
    it is not a new policy-support or causal assumption. -/
private theorem actual_action_nonempty (P : Measure Ω) [IsProbabilityMeasure P]
    (actualA : Ω → Act) : Nonempty Act := by
  classical
  letI : Nonempty Ω := nonempty_of_isProbabilityMeasure P
  exact ⟨actualA (Classical.ofNonempty : Ω)⟩

noncomputable def actualConditional
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → XSpace) (actualA : Ω → Act) (potential : Act → Ω → ℝ) :
    Kernel XSpace (JointOutcome Act) := by
  classical
  letI : Nonempty Act := actual_action_nonempty P actualA
  exact condDistrib (jointObservation actualA potential) X P

instance actualConditional_markov
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → XSpace) (actualA : Ω → Act) (potential : Act → Ω → ℝ) :
    IsMarkovKernel (actualConditional P X actualA potential) := by
  classical
  unfold actualConditional
  infer_instance

noncomputable def loggingMass (K : Kernel XSpace (JointOutcome Act))
    (x : XSpace) (a : Act) : ℝ :=
  (K x).real {z | z.2 = a}

noncomputable def causalPolicyValue
    (P : Measure Ω) (X : Ω → XSpace) (π : XSpace → Act → ℝ)
    (potential : Act → Ω → ℝ) : ℝ :=
  ∫ ω, ∑ a, π (X ω) a * potential a ω ∂P

noncomputable def actualLoggingScore
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → XSpace) (actualA : Ω → Act) (potential : Act → Ω → ℝ)
    (π : XSpace → Act → ℝ) (Y : Ω → ℝ) (ω : Ω) : ℝ :=
  π (X ω) (actualA ω) /
      loggingMass (actualConditional P X actualA potential) (X ω) (actualA ω) * Y ω

private theorem loggingMass_nonnegative
    (K : Kernel XSpace (JointOutcome Act)) (x : XSpace) (a : Act) :
    0 ≤ loggingMass K x a :=
  ENNReal.toReal_nonneg

private theorem loggingMass_measurable
    (K : Kernel XSpace (JointOutcome Act)) (a : Act) :
    Measurable (fun x => loggingMass K x a) := by
  simpa only [loggingMass, measureReal_def] using
    (Kernel.measurable_coe K
      ((measurableSet_singleton a).preimage measurable_snd)).ennreal_toReal

private theorem probability_row_le_one
    (p : Act → ℝ) (nonnegative : ∀ a, 0 ≤ p a)
    (normalized : ∑ a, p a = 1) (a : Act) : p a ≤ 1 := by
  have h := Finset.single_le_sum
    (fun b (_ : b ∈ (Finset.univ : Finset Act)) => nonnegative b)
    (Finset.mem_univ a)
  exact h.trans_eq normalized

private noncomputable def fiberSum
    (ν : Measure (JointOutcome Act)) (p : Act → ℝ)
    (g : Act → (Act → ℝ) → ℝ) (z : JointOutcome Act) : ℝ := by
  classical
  exact ∑ a, p a / ν.real {w | w.2 = a} * (if z.2 = a then g a z.1 else 0)

private theorem fiberSum_apply
    (ν : Measure (JointOutcome Act)) (p : Act → ℝ)
    (g : Act → (Act → ℝ) → ℝ) (z : JointOutcome Act) :
    fiberSum ν p g z = p z.2 / ν.real {w | w.2 = z.2} * g z.2 z.1 := by
  classical
  simp [fiberSum, mul_ite, eq_comm]

/-- Conditional exchangeability is used as actual independence of random
    variables, not as the desired conditional-moment identity. -/
private theorem independent_action_indicator_integral
    (ν : Measure (JointOutcome Act)) [IsProbabilityMeasure ν]
    (independent : IndepFun (fun z : JointOutcome Act => z.1) (fun z => z.2) ν)
    (g : (Act → ℝ) → ℝ) (measurableG : Measurable g) (a : Act) :
    (∫ z in {z : JointOutcome Act | z.2 = a}, g z.1 ∂ν) =
      (∫ z, g z.1 ∂ν) * ν.real {z | z.2 = a} := by
  classical
  let flag : Act → ℝ := fun b => if b = a then 1 else 0
  have measurableFlag : Measurable flag := measurable_of_finite _
  have measurableAction : MeasurableSet {z : JointOutcome Act | z.2 = a} :=
    (measurableSet_singleton a).preimage measurable_snd
  have factorized := independent.integral_fun_comp_mul_comp
    (f := g) (g := flag)
    measurable_fst.aemeasurable measurable_snd.aemeasurable
    measurableG.aestronglyMeasurable measurableFlag.aestronglyMeasurable
  have flagIntegral : (∫ z : JointOutcome Act, flag z.2 ∂ν) =
      ν.real {z | z.2 = a} := by
    simpa [flag, Set.indicator] using
      (integral_indicator_one (μ := ν) measurableAction)
  rw [← integral_indicator measurableAction]
  calc
    (∫ z : JointOutcome Act,
        ({z : JointOutcome Act | z.2 = a}.indicator (fun z => g z.1)) z ∂ν) =
        ∫ z : JointOutcome Act, g z.1 * flag z.2 ∂ν := by
      apply integral_congr_ae
      filter_upwards with z
      by_cases action : z.2 = a <;> simp [Set.indicator, flag, action]
    _ = (∫ z : JointOutcome Act, g z.1 ∂ν) *
        (∫ z : JointOutcome Act, flag z.2 ∂ν) := factorized
    _ = _ := by rw [flagIntegral]

/-- The finite-action cancellation occurs inside an actual conditional law.
    This local real-valued connection does not replace the existing rational
    finite-policy IPW theorem or assume any global bound on inverse weights. -/
private theorem fiber_moment
    (ν : Measure (JointOutcome Act)) [IsProbabilityMeasure ν]
    (independent : IndepFun (fun z : JointOutcome Act => z.1) (fun z => z.2) ν)
    (p : Act → ℝ) (g : Act → (Act → ℝ) → ℝ)
    (measurableG : ∀ a, Measurable (g a))
    (integrableG : ∀ a, Integrable (fun z : JointOutcome Act => g a z.1) ν)
    (support : ∀ a, p a ≠ 0 → 0 < ν.real {z : JointOutcome Act | z.2 = a}) :
    Integrable (fiberSum ν p g) ν ∧
      (∫ z, fiberSum ν p g z ∂ν) =
        ∑ a, p a * ∫ z : JointOutcome Act, g a z.1 ∂ν := by
  classical
  have term (a : Act) : Integrable
      (fun z : JointOutcome Act => p a / ν.real {w | w.2 = a} *
        (if z.2 = a then g a z.1 else 0)) ν := by
    have hi := (integrableG a).indicator
      ((measurableSet_singleton a).preimage measurable_snd)
    simpa [Set.indicator] using hi.const_mul (p a / ν.real {w | w.2 = a})
  refine ⟨integrable_finsetSum Finset.univ (fun a _ => term a), ?_⟩
  unfold fiberSum
  rw [integral_finsetSum Finset.univ (fun a _ => term a)]
  apply Finset.sum_congr rfl
  intro a _
  rw [integral_const_mul]
  have actionIntegral :
      (∫ z : JointOutcome Act, (if z.2 = a then g a z.1 else 0) ∂ν) =
        (∫ z : JointOutcome Act, g a z.1 ∂ν) * ν.real {z | z.2 = a} := by
    simpa [Set.indicator] using
      (integral_indicator
        ((measurableSet_singleton a).preimage measurable_snd)).trans
        (independent_action_indicator_integral ν independent (g a) (measurableG a) a)
  rw [actionIntegral]
  by_cases zero : p a = 0
  · simp [zero]
  · field_simp [ne_of_gt (support a zero)] <;> ring

/-- The absolute-moment cancellation proves score integrability rather than
    taking it as a premise. Finitely many potential L1 norms dominate it. -/
private theorem fiber_ipw_bound
    (ν : Measure (JointOutcome Act)) [IsProbabilityMeasure ν]
    (independent : IndepFun (fun z : JointOutcome Act => z.1) (fun z => z.2) ν)
    (p : Act → ℝ) (nonnegative : ∀ a, 0 ≤ p a) (normalized : ∑ a, p a = 1)
    (potentialIntegrable : ∀ a, Integrable (fun z : JointOutcome Act => z.1 a) ν)
    (support : ∀ a, p a ≠ 0 → 0 < ν.real {z : JointOutcome Act | z.2 = a}) :
    Integrable (fiberSum ν p (fun a v => v a)) ν ∧
      (∫ z, fiberSum ν p (fun a v => v a) z ∂ν) =
        (∑ a, p a * ∫ z : JointOutcome Act, z.1 a ∂ν) ∧
      (∫ z, ‖fiberSum ν p (fun a v => v a) z‖ ∂ν) ≤
        ∑ a, ∫ z : JointOutcome Act, ‖z.1 a‖ ∂ν := by
  have moment := fiber_moment ν independent p (fun a v => v a)
    (fun a => measurable_pi_apply a) potentialIntegrable support
  have absoluteMoment := fiber_moment ν independent p (fun a v => ‖v a‖)
    (fun a => (measurable_pi_apply a).norm)
    (fun a => (potentialIntegrable a).norm) support
  refine ⟨moment.1, moment.2, ?_⟩
  have normIdentity :
      (fun z => ‖fiberSum ν p (fun a v => v a) z‖) =
        fiberSum ν p (fun a v => ‖v a‖) := by
    funext z
    rw [fiberSum_apply, fiberSum_apply]
    rw [norm_mul, Real.norm_eq_abs,
      abs_of_nonneg (div_nonneg (nonnegative z.2) ENNReal.toReal_nonneg)]
  rw [normIdentity, absoluteMoment.2]
  apply Finset.sum_le_sum
  intro a _
  have positiveMean : 0 ≤ ∫ z : JointOutcome Act, ‖z.1 a‖ ∂ν :=
    integral_nonneg (fun _ => norm_nonneg _)
  have bound := probability_row_le_one p nonnegative normalized a
  nlinarith

private noncomputable def jointWeight
    (K : Kernel XSpace (JointOutcome Act)) (π : XSpace → Act → ℝ)
    (q : XSpace × JointOutcome Act) : ℝ :=
  fiberSum (K q.1) (π q.1) (fun a v => v a) q.2

private def jointPolicyReturn (π : XSpace → Act → ℝ)
    (q : XSpace × JointOutcome Act) : ℝ :=
  ∑ a, π q.1 a * q.2.1 a

private theorem jointWeight_measurable
    (K : Kernel XSpace (JointOutcome Act)) (π : XSpace → Act → ℝ)
    (measurablePolicy : ∀ a, Measurable (fun x => π x a)) :
    Measurable (jointWeight K π) := by
  classical
  change Measurable (fun q : XSpace × JointOutcome Act =>
    ∑ a, π q.1 a / loggingMass K q.1 a *
      (if q.2.2 = a then q.2.1 a else 0))
  apply Finset.measurable_sum
  intro a _
  have actionSet : MeasurableSet {q : XSpace × JointOutcome Act | q.2.2 = a} :=
    (measurableSet_singleton a).preimage (measurable_snd.comp measurable_snd)
  have coordinate : Measurable (fun q : XSpace × JointOutcome Act => q.2.1 a) :=
    (measurable_pi_apply a).comp (measurable_fst.comp measurable_snd)
  exact (((measurablePolicy a).comp measurable_fst).div
    ((loggingMass_measurable K a).comp measurable_fst)).mul
      (Measurable.ite actionSet coordinate measurable_const)

private theorem jointPolicyReturn_measurable
    (π : XSpace → Act → ℝ)
    (measurablePolicy : ∀ a, Measurable (fun x => π x a)) :
    Measurable (jointPolicyReturn π) := by
  classical
  unfold jointPolicyReturn
  apply Finset.measurable_sum
  intro a _
  exact ((measurablePolicy a).comp measurable_fst).mul
    ((measurable_pi_apply a).comp (measurable_fst.comp measurable_snd))

private theorem policy_return_integrable
    (P : Measure Ω) (X : Ω → XSpace) (measurableX : Measurable X)
    (π : XSpace → Act → ℝ)
    (measurablePolicy : ∀ a, Measurable (fun x => π x a))
    (nonnegative : ∀ x a, 0 ≤ π x a) (normalized : ∀ x, ∑ a, π x a = 1)
    (potential : Act → Ω → ℝ) (potentialIntegrable : ∀ a, Integrable (potential a) P) :
    Integrable (fun ω => ∑ a, π (X ω) a * potential a ω) P := by
  apply integrable_finsetSum Finset.univ
  intro a _
  apply (potentialIntegrable a).bdd_mul
    ((measurablePolicy a).comp measurableX).aestronglyMeasurable (c := 1)
  filter_upwards with ω
  rw [Real.norm_eq_abs, abs_of_nonneg (nonnegative (X ω) a)]
  exact probability_row_le_one (π (X ω)) (nonnegative (X ω)) (normalized (X ω)) a

/-- Master U12.1 / original 12.3 L119: consistency, actual conditional
    exchangeability and target support identify the actual logging score.
    No finite-X, rational-outcome, bounded-Y or uniform-positivity premise
    appears. P and the potential/actual variables define K themselves. -/
theorem finite_action_causal_ipw
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → XSpace) (measurableX : Measurable X)
    (actualA : Ω → Act) (measurableA : Measurable actualA)
    (potential : Act → Ω → ℝ)
    (measurablePotential : ∀ a, Measurable (potential a))
    (potentialIntegrable : ∀ a, Integrable (potential a) P)
    (Y : Ω → ℝ) (consistent : Y =ᵐ[P] fun ω => potential (actualA ω) ω)
    (π : XSpace → Act → ℝ)
    (measurablePolicy : ∀ a, Measurable (fun x => π x a))
    (nonnegative : ∀ x a, 0 ≤ π x a) (normalized : ∀ x, ∑ a, π x a = 1)
    (exchangeable : ∀ᵐ x ∂P.map X,
      IndepFun (fun z : JointOutcome Act => z.1) (fun z => z.2)
        (actualConditional P X actualA potential x))
    (targetSupported : ∀ᵐ x ∂P.map X, ∀ a, π x a ≠ 0 →
      0 < loggingMass (actualConditional P X actualA potential) x a) :
    Integrable (actualLoggingScore P X actualA potential π Y) P ∧
      Integrable (fun ω => ∑ a, π (X ω) a * potential a ω) P ∧
      (∫ ω, actualLoggingScore P X actualA potential π Y ω ∂P) =
        causalPolicyValue P X π potential := by
  classical
  letI : Nonempty Act := actual_action_nonempty P actualA
  let T : Ω → JointOutcome Act := jointObservation actualA potential
  let K : Kernel XSpace (JointOutcome Act) := actualConditional P X actualA potential
  let L : Measure (XSpace × JointOutcome Act) := P.map (fun ω => (X ω, T ω))
  let F : XSpace × JointOutcome Act → ℝ := jointWeight K π
  let G : XSpace × JointOutcome Act → ℝ := jointPolicyReturn π
  have measurableT : Measurable T :=
    Measurable.prod (measurable_pi_lambda _ measurablePotential) measurableA
  have measurableXT : Measurable (fun ω => (X ω, T ω)) :=
    Measurable.prod measurableX measurableT
  have measurableF : Measurable F := jointWeight_measurable K π measurablePolicy
  have measurableG : Measurable G := jointPolicyReturn_measurable π measurablePolicy
  have coordinateJoint (a : Act) : Integrable
      (fun q : XSpace × JointOutcome Act => q.2.1 a) L := by
    have hm : Measurable (fun q : XSpace × JointOutcome Act => q.2.1 a) :=
      (measurable_pi_apply a).comp (measurable_fst.comp measurable_snd)
    apply (integrable_map_measure hm.aestronglyMeasurable measurableXT.aemeasurable).2
    simpa only [T, jointObservation] using potentialIntegrable a
  have coordinatesAE : ∀ᵐ x ∂P.map X, ∀ a,
      Integrable (fun z : JointOutcome Act => z.1 a) (K x) := by
    apply ae_all_iff.mpr
    intro a
    simpa only [K, actualConditional, T] using
      (MeasureTheory.Integrable.condDistrib_ae_map
        (μ := P) (X := X) (Y := T)
        measurableT.aemeasurable (coordinateJoint a))
  have coordinateNormIntegral (a : Act) : Integrable
      (fun x => ∫ z : JointOutcome Act, ‖z.1 a‖ ∂K x) (P.map X) := by
    simpa only [K, actualConditional, T] using
      (MeasureTheory.Integrable.integral_norm_condDistrib_map
        (μ := P) (X := X) (Y := T)
        measurableT.aemeasurable (coordinateJoint a))
  have dominatingIntegral : Integrable
      (fun x => ∑ a, ∫ z : JointOutcome Act, ‖z.1 a‖ ∂K x) (P.map X) :=
    integrable_finsetSum Finset.univ (fun a _ => coordinateNormIntegral a)
  have fiberIntegrable : ∀ᵐ x ∂P.map X, Integrable (fun z => F (x, z)) (K x) := by
    filter_upwards [coordinatesAE, exchangeable, targetSupported] with x hx hi hs
    exact (fiber_ipw_bound (K x) hi (π x) (nonnegative x) (normalized x) hx hs).1
  have normIntegralMeasurable : AEStronglyMeasurable
      (fun x => ∫ z, ‖F (x, z)‖ ∂K x) (P.map X) := by
    simpa only [K, actualConditional, T] using
      (MeasureTheory.AEStronglyMeasurable.integral_condDistrib_map
        (μ := P) (X := X) (Y := T) (f := fun q => ‖F q‖)
        measurableT.aemeasurable measurableF.aestronglyMeasurable.norm)
  have normIntegralIntegrable : Integrable
      (fun x => ∫ z, ‖F (x, z)‖ ∂K x) (P.map X) := by
    apply dominatingIntegral.mono' normIntegralMeasurable
    filter_upwards [coordinatesAE, exchangeable, targetSupported] with x hx hi hs
    have nonnegativeIntegral : 0 ≤ ∫ z, ‖F (x, z)‖ ∂K x :=
      integral_nonneg (fun _ => norm_nonneg _)
    rw [Real.norm_eq_abs, abs_of_nonneg nonnegativeIntegral]
    exact (fiber_ipw_bound (K x) hi (π x) (nonnegative x) (normalized x) hx hs).2.2
  have integrableF : Integrable F L := by
    apply (MeasureTheory.AEStronglyMeasurable.ae_integrable_condDistrib_map_iff
      (μ := P) (X := X) (Y := T) (f := F)
      measurableT.aemeasurable measurableF.aestronglyMeasurable).mp
    constructor
    · simpa only [K, actualConditional, T] using fiberIntegrable
    · simpa only [K, actualConditional, T] using normIntegralIntegrable
  have actualFIntegrable : Integrable (fun ω => F (X ω, T ω)) P :=
    (integrable_map_measure measurableF.aestronglyMeasurable
      measurableXT.aemeasurable).1 integrableF
  have policyIntegrable := policy_return_integrable P X measurableX π
    measurablePolicy nonnegative normalized potential potentialIntegrable
  have integrableG : Integrable G L := by
    apply (integrable_map_measure measurableG.aestronglyMeasurable
      measurableXT.aemeasurable).2
    simpa only [G, jointPolicyReturn, T, jointObservation] using policyIntegrable
  have disintegration : (P.map X) ⊗ₘ K = L := by
    simpa only [K, L, actualConditional, T] using
      (compProd_map_condDistrib (μ := P) (X := X) (Y := T)
        measurableT.aemeasurable)
  have integrableFComp : Integrable F ((P.map X) ⊗ₘ K) := by
    rw [disintegration]
    exact integrableF
  have integrableGComp : Integrable G ((P.map X) ⊗ₘ K) := by
    rw [disintegration]
    exact integrableG
  have conditionalMeans : ∀ᵐ x ∂P.map X,
      (∫ z, F (x, z) ∂K x) = ∫ z, G (x, z) ∂K x := by
    filter_upwards [coordinatesAE, exchangeable, targetSupported] with x hx hi hs
    have moment := (fiber_moment (K x) hi (π x) (fun a v => v a)
      (fun a => measurable_pi_apply a) hx hs).2
    change (∫ z, fiberSum (K x) (π x) (fun a v => v a) z ∂K x) =
      ∫ z : JointOutcome Act, ∑ a, π x a * z.1 a ∂K x
    rw [moment, integral_finsetSum Finset.univ
      (fun a _ => (hx a).const_mul (π x a))]
    simp only [integral_const_mul]
  have scoreReadsActual : actualLoggingScore P X actualA potential π Y =ᵐ[P]
      fun ω => F (X ω, T ω) := by
    filter_upwards [consistent] with ω hω
    change π (X ω) (actualA ω) / loggingMass K (X ω) (actualA ω) * Y ω =
      fiberSum (K (X ω)) (π (X ω)) (fun a v => v a) (T ω)
    rw [hω, fiberSum_apply]
    rfl
  refine ⟨actualFIntegrable.congr scoreReadsActual.symm, policyIntegrable, ?_⟩
  calc
    (∫ ω, actualLoggingScore P X actualA potential π Y ω ∂P) =
        ∫ ω, F (X ω, T ω) ∂P := integral_congr_ae scoreReadsActual
    _ = ∫ q, F q ∂L :=
      (integral_map measurableXT.aemeasurable measurableF.aestronglyMeasurable).symm
    _ = ∫ x, ∫ z, F (x, z) ∂K x ∂P.map X := by
      rw [← disintegration]
      exact Measure.integral_compProd integrableFComp
    _ = ∫ x, ∫ z, G (x, z) ∂K x ∂P.map X := integral_congr_ae conditionalMeans
    _ = ∫ q, G q ∂L := by
      rw [← disintegration]
      exact (Measure.integral_compProd integrableGComp).symm
    _ = ∫ ω, G (X ω, T ω) ∂P :=
      integral_map measurableXT.aemeasurable measurableG.aestronglyMeasurable
    _ = causalPolicyValue P X π potential := rfl

end Generic

open JurisLean.Candidates.Final20261021
open JurisLean.Candidates.BusinessMeasurement20261027
open JurisLean.Candidates.MeasuredPolicy20261027
open JurisLean.Candidates.PolicyEvaluation20261027

section MeasuredInstance

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The original finite conditional-mean table is an input about potential
    outcomes. This connection uses total conditional expectation; it neither
    assumes an observed/potential-mean equality nor recomputes the old numeric
    policy values. The finite covariate restriction occurs only in this
    existing PolicyDatum instance, not in finite_action_causal_ipw. -/
private theorem finite_value_from_potential_means {m : Nat}
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → Fin m) (measurableX : Measurable X)
    (potential : Bool → Ω → ℝ)
    (potentialIntegrable : ∀ a, Integrable (potential a) P)
    (table : List ℚ)
    (tableBounds : ∀ x : Fin m,
      0 ≤ table.getD x.val 0 ∧ table.getD x.val 0 ≤ 1)
    (mass : Fin m → ℚ)
    (massMatches : ∀ x, P.real {ω | X ω = x} = (mass x : ℝ))
    (outcome : Fin m → Bool → ℚ)
    (potentialMeans : ∀ a,
      P[potential a | MeasurableSpace.comap X (inferInstance : MeasurableSpace (Fin m))]
        =ᵐ[P] fun ω => (outcome (X ω) a : ℝ)) :
    causalPolicyValue P X (fun x a => (policyProbability table x a : ℝ)) potential =
      (policyValue mass (policyProbability table) outcome : ℝ) := by
  classical
  let π : Fin m → Bool → ℝ := fun x a => (policyProbability table x a : ℝ)
  let σ : MeasurableSpace Ω := MeasurableSpace.comap X inferInstance
  have measurablePolicy (a : Bool) : Measurable (fun x => π x a) :=
    measurable_of_finite _
  have nonnegative (x : Fin m) (a : Bool) : 0 ≤ π x a := by
    cases a with
    | false =>
        change (0 : ℝ) ≤ ((1 - table.getD x.val 0 : ℚ) : ℝ)
        exact_mod_cast sub_nonneg.mpr (tableBounds x).2
    | true =>
        change (0 : ℝ) ≤ (table.getD x.val 0 : ℝ)
        exact_mod_cast (tableBounds x).1
  have normalized (x : Fin m) : ∑ a : Bool, π x a = 1 := by
    simp [π, policyProbability, Fintype.sum_bool]
  have productIntegrable (a : Bool) :
      Integrable (fun ω => π (X ω) a * potential a ω) P := by
    apply (potentialIntegrable a).bdd_mul
      ((measurablePolicy a).comp measurableX).aestronglyMeasurable (c := 1)
    filter_upwards with ω
    rw [Real.norm_eq_abs, abs_of_nonneg (nonnegative (X ω) a)]
    exact probability_row_le_one (π (X ω)) (nonnegative (X ω)) (normalized (X ω)) a
  have replacePotential (a : Bool) :
      (∫ ω, π (X ω) a * potential a ω ∂P) =
        ∫ ω, π (X ω) a * (outcome (X ω) a : ℝ) ∂P := by
    have measurableAtX : StronglyMeasurable[σ] (fun ω => π (X ω) a) :=
      (measurablePolicy a).stronglyMeasurable.comp_measurable
        (Measurable.of_comap_le le_rfl)
    have pullout := condExp_mul_of_stronglyMeasurable_left
      (μ := P) (m := σ) measurableAtX (productIntegrable a) (potentialIntegrable a)
    calc
      (∫ ω, π (X ω) a * potential a ω ∂P) =
          ∫ ω, P[(fun ω => π (X ω) a * potential a ω) | σ] ω ∂P :=
        (integral_condExp (μ := P)
          (f := fun ω => π (X ω) a * potential a ω) measurableX.comap_le).symm
      _ = ∫ ω, π (X ω) a * P[potential a | σ] ω ∂P :=
        integral_congr_ae pullout
      _ = _ := by
        apply integral_congr_ae
        filter_upwards [potentialMeans a] with ω hω
        rw [hω]
  have finiteIntegral (a : Bool) :
      (∫ ω, π (X ω) a * (outcome (X ω) a : ℝ) ∂P) =
        ∑ x, (mass x : ℝ) * π x a * (outcome x a : ℝ) := by
    let f : Fin m → ℝ := fun x => π x a * (outcome x a : ℝ)
    have measurableF : Measurable f := measurable_of_finite _
    calc
      (∫ ω, π (X ω) a * (outcome (X ω) a : ℝ) ∂P) =
          ∫ x, f x ∂P.map X :=
        (integral_map measurableX.aemeasurable measurableF.aestronglyMeasurable).symm
      _ = ∑ x, (P.map X).real {x} * f x := by
        simpa only [smul_eq_mul] using
          (integral_fintype (μ := P.map X) (f := f) Integrable.of_finite)
      _ = _ := by
        apply Finset.sum_congr rfl
        intro x _
        have actualMass : (P.map X).real {x} = (mass x : ℝ) := by
          change (P.map X {x}).toReal = (mass x : ℝ)
          rw [Measure.map_apply measurableX (measurableSet_singleton x)]
          exact massMatches x
        rw [actualMass]
        dsimp [f]
        ring
  calc
    causalPolicyValue P X (fun x a => (policyProbability table x a : ℝ)) potential =
        ∑ a : Bool, ∫ ω, π (X ω) a * potential a ω ∂P :=
      integral_finsetSum Finset.univ (fun a _ => productIntegrable a)
    _ = ∑ a : Bool, ∑ x, (mass x : ℝ) * π x a * (outcome x a : ℝ) := by
      apply Finset.sum_congr rfl
      intro a _
      rw [replacePotential a, finiteIntegral a]
    _ = (policyValue mass (policyProbability table) outcome : ℝ) := by
      rw [Finset.sum_comm]
      simp only [policyValue, Rat.cast_sum, Rat.cast_mul, Finset.mul_sum, π, mul_assoc]

/-- Master U12.1 / original 12.3 L119, actual binary measurement instance.
    The existing consumeMeasurement success theorem supplies the actual
    returned measurement and treatment. Measurement validity, causal
    consistency/exchangeability, and equality of the supplied logging table
    to the actual conditional-action law are separate, explicit premises.
    SourceRef membership or a successful field comparison proves none of them.
    Given potential means and the actual X mass then connect this causal value
    to the existing finite policyValue, whose numeric/sharp-bound results are
    reused unchanged. No constructed full-datum law is assumed. -/
theorem actual_measured_policy_causal_value {m : Nat}
    (P : Measure Ω) [IsProbabilityMeasure P]
    (rows : Ω → PolicyObservation m)
    (measurableDatum : Measurable (fun ω => observationDatum (rows ω)))
    (env : PolicyEnvironment) (measurement : Ω → MeasurementResult)
    (treatment : Ω → TreatmentRecord m) (catalog : List (TreatmentRecord m))
    (accepted : ∀ᵐ ω ∂P,
      consumeMeasurement env (measurement ω) (treatment ω) catalog = .known (rows ω))
    (Y : Ω → ℝ)
    (measurementValid : ∀ᵐ ω ∂P, (Behavior.indicator (rows ω).measured.label : ℝ) = Y ω)
    (potential : Bool → Ω → ℝ)
    (measurablePotential : ∀ a, Measurable (potential a))
    (potentialIntegrable : ∀ a, Integrable (potential a) P)
    (consistent : Y =ᵐ[P] fun ω => potential (rows ω).treatment.action ω)
    (logging table : List ℚ)
    (tableBounds : ∀ x : Fin m,
      0 ≤ table.getD x.val 0 ∧ table.getD x.val 0 ≤ 1)
    (coverage : ∀ (x : Fin m) (a : Bool),
      policyProbability table x a ≠ 0 → policyProbability logging x a ≠ 0)
    (loggingMatches : ∀ᵐ x ∂P.map (fun ω => (rows ω).treatment.feature), ∀ a : Bool,
      loggingMass
        (actualConditional P (fun ω => (rows ω).treatment.feature)
          (fun ω => (rows ω).treatment.action) potential) x a =
        (policyProbability logging x a : ℝ))
    (exchangeable : ∀ᵐ x ∂P.map (fun ω => (rows ω).treatment.feature),
      IndepFun (fun z : JointOutcome Bool => z.1) (fun z => z.2)
        (actualConditional P (fun ω => (rows ω).treatment.feature)
          (fun ω => (rows ω).treatment.action) potential x))
    (mass : Fin m → ℚ)
    (massMatches : ∀ x,
      P.real {ω | (rows ω).treatment.feature = x} = (mass x : ℝ))
    (outcome : Fin m → Bool → ℚ)
    (potentialMeans : ∀ a,
      P[potential a | MeasurableSpace.comap (fun ω => (rows ω).treatment.feature)
        (inferInstance : MeasurableSpace (Fin m))] =ᵐ[P]
          fun ω => (outcome (rows ω).treatment.feature a : ℝ)) :
    (∀ᵐ ω ∂P,
      measurement ω = .measured (rows ω).measured ∧
        (rows ω).treatment = treatment ω ∧
        treatmentMatches env (rows ω).measured (treatment ω) catalog = true) ∧
      Integrable (fun ω => (policyScore logging table (observationDatum (rows ω)) : ℝ)) P ∧
      (∫ ω, (policyScore logging table (observationDatum (rows ω)) : ℝ) ∂P) =
        causalPolicyValue P (fun ω => (rows ω).treatment.feature)
          (fun x a => (policyProbability table x a : ℝ)) potential ∧
      causalPolicyValue P (fun ω => (rows ω).treatment.feature)
          (fun x a => (policyProbability table x a : ℝ)) potential =
        (policyValue mass (policyProbability table) outcome : ℝ) := by
  classical
  let X : Ω → Fin m := fun ω => (rows ω).treatment.feature
  let actualA : Ω → Bool := fun ω => (rows ω).treatment.action
  let K : Kernel (Fin m) (JointOutcome Bool) := actualConditional P X actualA potential
  let π : Fin m → Bool → ℝ := fun x a => (policyProbability table x a : ℝ)
  have measurableX : Measurable X :=
    (measurable_of_finite (fun z : PolicyDatum m => z.1)).comp measurableDatum
  have measurableA : Measurable actualA :=
    (measurable_of_finite (fun z : PolicyDatum m => z.2.1)).comp measurableDatum
  have measurablePolicy (a : Bool) : Measurable (fun x => π x a) :=
    measurable_of_finite _
  have nonnegative (x : Fin m) (a : Bool) : 0 ≤ π x a := by
    cases a with
    | false =>
        change (0 : ℝ) ≤ ((1 - table.getD x.val 0 : ℚ) : ℝ)
        exact_mod_cast sub_nonneg.mpr (tableBounds x).2
    | true =>
        change (0 : ℝ) ≤ (table.getD x.val 0 : ℝ)
        exact_mod_cast (tableBounds x).1
  have normalized (x : Fin m) : ∑ a : Bool, π x a = 1 := by
    simp [π, policyProbability, Fintype.sum_bool]
  have targetSupported : ∀ᵐ x ∂P.map X, ∀ a : Bool,
      π x a ≠ 0 → 0 < loggingMass K x a := by
    filter_upwards [loggingMatches] with x hx
    intro a targetNonzero
    have targetRationalNonzero : policyProbability table x a ≠ 0 := by
      intro zero
      apply targetNonzero
      simp [π, zero]
    have loggingRationalNonzero := coverage x a targetRationalNonzero
    have loggingRealNonzero : (policyProbability logging x a : ℝ) ≠ 0 := by
      exact_mod_cast loggingRationalNonzero
    have actualNonzero : loggingMass K x a ≠ 0 := by
      rw [hx a]
      exact loggingRealNonzero
    exact lt_of_le_of_ne (loggingMass_nonnegative K x a) (Ne.symm actualNonzero)
  have causal := finite_action_causal_ipw P X measurableX actualA measurableA
    potential measurablePotential potentialIntegrable Y consistent π
    measurablePolicy nonnegative normalized exchangeable targetSupported
  have loggerAtActual : ∀ᵐ ω ∂P, ∀ a : Bool,
      loggingMass K (X ω) a = (policyProbability logging (X ω) a : ℝ) :=
    ae_of_ae_map measurableX.aemeasurable loggingMatches
  have scoreEquality :
      (fun ω => (policyScore logging table (observationDatum (rows ω)) : ℝ)) =ᵐ[P]
        actualLoggingScore P X actualA potential π Y := by
    filter_upwards [loggerAtActual, measurementValid] with ω hlog hmeasurement
    simp only [policyScore, Rat.cast_mul, Rat.cast_div]
    change (policyProbability table (X ω) (actualA ω) : ℝ) /
        (policyProbability logging (X ω) (actualA ω) : ℝ) *
          (Behavior.indicator (rows ω).measured.label : ℝ) =
      π (X ω) (actualA ω) / loggingMass K (X ω) (actualA ω) * Y ω
    rw [← hlog (actualA ω), hmeasurement]
    rfl
  refine ⟨?_, causal.1.congr scoreEquality.symm, ?_, ?_⟩
  · filter_upwards [accepted] with ω hω
    exact measured_policy_row_preserves_actual_output env (measurement ω)
      (treatment ω) catalog (rows ω) hω
  · rw [integral_congr_ae scoreEquality]
    exact causal.2.2
  · exact finite_value_from_potential_means P X measurableX potential
      potentialIntegrable table tableBounds mass massMatches outcome potentialMeans

end MeasuredInstance

end JurisLean.Candidates.U12_1CausalPolicyBridge20261030
