import JurisLean.Candidates.ExactProbability20261027
import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Probability.Kernel.Defs
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Probability.ConditionalProbability
import Mathlib.Tactic

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace JurisLean.Candidates.BetaFutureSampling20261031

noncomputable section

local instance : MeasurableSpace Bool := ⊤

private def coinParameter (θ : ℝ) : ℝ≥0 :=
  min θ.toNNReal 1

private theorem coinParameter_le_one (θ : ℝ) :
    coinParameter θ ≤ 1 :=
  min_le_right _ _

@[fun_prop]
private theorem measurable_coinParameter : Measurable coinParameter := by
  unfold coinParameter
  fun_prop

private def coinMeasure (θ : ℝ) : Measure Bool :=
  (PMF.bernoulli (coinParameter θ) (coinParameter_le_one θ)).toMeasure

private instance coin_probability (θ : ℝ) :
    IsProbabilityMeasure (coinMeasure θ) := by
  unfold coinMeasure
  infer_instance

private def coinMass (θ : ℝ) (b : Bool) : ℝ≥0∞ :=
  if b then (coinParameter θ : ℝ≥0∞)
  else ((1 - coinParameter θ : ℝ≥0) : ℝ≥0∞)

@[fun_prop]
private theorem measurable_coinMass (b : Bool) :
    Measurable (fun θ => coinMass θ b) := by
  cases b <;> unfold coinMass <;> simp only [Bool.false_eq_true, if_false, if_true]
  all_goals fun_prop

private theorem coinMeasure_singleton (θ : ℝ) (b : Bool) :
    coinMeasure θ {b} = coinMass θ b := by
  unfold coinMeasure
  rw [(PMF.bernoulli (coinParameter θ) (coinParameter_le_one θ)).
    toMeasure_apply_singleton b (by trivial), PMF.bernoulli_apply]
  cases b <;> rfl

private def pairAtom (θ : ℝ) (z : Bool × Bool) : ℝ≥0∞ :=
  (1 / 2 : ℝ≥0∞) * (if z.1 = z.2 then coinMass θ z.1 else 0) +
    (1 / 2 : ℝ≥0∞) * coinMass θ z.1 * coinMass θ z.2

@[fun_prop]
private theorem measurable_pairAtom (z : Bool × Bool) :
    Measurable (fun θ => pairAtom θ z) := by
  by_cases h : z.1 = z.2 <;> simp only [pairAtom, h, if_true, if_false]
  all_goals fun_prop

/-- The parameter-dependent pair kernel, expressed by its four actual atoms. -/
def halfCopyKernel : Kernel ℝ (Bool × Bool) where
  toFun θ := Measure.sum fun z : Bool × Bool =>
    pairAtom θ z • Measure.dirac z
  measurable' := by
    apply Measure.measurable_of_measurable_coe
    intro s hs
    simp_rw [Measure.sum_apply _ hs, Measure.smul_apply, smul_eq_mul]
    exact Measurable.tsum
      (fun z => (measurable_pairAtom z).mul measurable_const)

private theorem halfCopyKernel_singleton (θ : ℝ) (z : Bool × Bool) :
    halfCopyKernel θ {z} = pairAtom θ z := by
  change (Measure.sum fun w : Bool × Bool =>
    pairAtom θ w • Measure.dirac w) {z} = pairAtom θ z
  exact Measure.sum_smul_dirac_singleton

private theorem half_copy_generation (θ : ℝ) :
    halfCopyKernel θ =
      (1 / 2 : ℝ≥0∞) •
        ((coinMeasure θ).map (fun b : Bool => (b, b))) +
      (1 / 2 : ℝ≥0∞) •
        ((coinMeasure θ).prod (coinMeasure θ)) := by
  apply Measure.ext_of_singleton
  rintro ⟨a, b⟩
  have hcopy :
      (coinMeasure θ).map (fun c : Bool => (c, c)) {(a, b)} =
        if a = b then coinMass θ a else 0 := by
    rw [Measure.map_apply (measurable_id.prodMk measurable_id)
      (measurableSet_singleton _)]
    by_cases hab : a = b
    · subst b
      have he :
          (fun c : Bool => (c, c)) ⁻¹' {(a, a)} = {a} := by
        ext c
        simp
      rw [he, coinMeasure_singleton]
      simp
    · have he :
          (fun c : Bool => (c, c)) ⁻¹' {(a, b)} = ∅ := by
        ext c
        simp only [Set.mem_preimage, Set.mem_singleton_iff,
          Prod.mk.injEq, Set.mem_empty_iff_false]
        aesop
      rw [he]
      simp [hab]
  have hprod :
      (coinMeasure θ).prod (coinMeasure θ) {(a, b)} =
        coinMass θ a * coinMass θ b := by
    rw [← Set.singleton_prod_singleton, Measure.prod_prod,
      coinMeasure_singleton, coinMeasure_singleton]
  rw [halfCopyKernel_singleton]
  simp only [Measure.add_apply, Measure.smul_apply, smul_eq_mul, hcopy, hprod]
  rfl

instance halfCopyKernel_markov : IsMarkovKernel halfCopyKernel where
  isProbabilityMeasure θ := by
    refine ⟨?_⟩
    rw [half_copy_generation θ]
    norm_num [Measure.add_apply, Measure.smul_apply, smul_eq_mul,
      Measure.map_apply (measurable_id.prodMk measurable_id)]

/-- The finite-atom kernel is exactly the copy/independent mixture,
not a distribution defined by the final integrated constants. -/
theorem half_copy_kernel_realizes_generation (θ : ℝ) :
    halfCopyKernel θ =
      (1 / 2 : ℝ≥0∞) •
        ((coinMeasure θ).map (fun b : Bool => (b, b))) +
      (1 / 2 : ℝ≥0∞) •
        ((coinMeasure θ).prod (coinMeasure θ)) ∧
    ∀ a b : Bool,
      halfCopyKernel θ {(a, b)} =
        (1 / 2 : ℝ≥0∞) * (if a = b then coinMass θ a else 0) +
          (1 / 2 : ℝ≥0∞) * coinMass θ a * coinMass θ b := by
  refine ⟨half_copy_generation θ, ?_⟩
  intro a b
  exact halfCopyKernel_singleton θ (a, b)

open JurisLean.Candidates.ExactProbability20261027
open JurisLean.FullMath.Probability

/-- The actual future distribution is posterior measure bound to the
declared post-data future channel. -/
theorem beta_future_success_of_channel
    (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) (s f : ℕ)
    (next : Kernel ℝ Bool) [IsMarkovKernel next]
    (channel : ∀ᵐ θ ∂(volume.withDensity (normalizedBetaLikelihood α β s f)),
      next θ {true} = ENNReal.ofReal θ) :
    ((volume.withDensity (normalizedBetaLikelihood α β s f)).bind next) {true} =
      ENNReal.ofReal ((α + s) / ((α + s) + (β + f))) := by
  have hd : Measurable (normalizedBetaLikelihood α β s f) := by
    have heq :
        normalizedBetaLikelihood α β s f =
          betaPDF (α + s) (β + f) := by
      funext θ
      exact positive_real_beta_posterior_density α β hα hβ s f θ
    rw [heq]
    exact (measurable_betaPDFReal (α + s) (β + f)).ennreal_ofReal
  rw [Measure.bind_apply (measurableSet_singleton true) next.aemeasurable]
  calc
    (∫⁻ θ, next θ {true}
        ∂(volume.withDensity (normalizedBetaLikelihood α β s f))) =
        ∫⁻ θ, ENNReal.ofReal θ
          ∂(volume.withDensity (normalizedBetaLikelihood α β s f)) :=
      lintegral_congr_ae channel
    _ = ENNReal.ofReal ((α + s) / ((α + s) + (β + f))) := by
      rw [lintegral_withDensity_eq_lintegral_mul volume hd
        measurable_id.ennreal_ofReal]
      simpa only [Pi.mul_apply, mul_comm] using
        positive_real_beta_predictive_mean α β hα hβ s f

private instance beta11_probability :
    IsProbabilityMeasure (betaMeasure 1 1) :=
  isProbabilityMeasureBeta (by norm_num) (by norm_num)

private theorem beta11_support :
    ∀ᵐ θ ∂betaMeasure 1 1, 0 < θ ∧ θ < 1 := by
  rw [betaMeasure,
    ae_withDensity_iff (measurable_betaPDFReal 1 1).ennreal_ofReal]
  exact Filter.Eventually.of_forall fun θ hθ => by
    by_contra hout
    exact hθ (by simp [betaPDF, betaPDFReal, hout])

private theorem coinMass_on_unit (θ : ℝ) (h0 : 0 ≤ θ) (h1 : θ ≤ 1)
    (b : Bool) :
    coinMass θ b = ENNReal.ofReal (if b then θ else 1 - θ) := by
  have hp : θ.toNNReal ≤ (1 : ℝ≥0) := by
    change (θ.toNNReal : ℝ) ≤ (1 : ℝ)
    rw [Real.coe_toNNReal θ h0]
    exact h1
  cases b
  · change (((1 - min θ.toNNReal 1 : ℝ≥0) : ℝ≥0∞)) =
      ENNReal.ofReal (1 - θ)
    rw [min_eq_left hp]
    change (((1 - θ.toNNReal : ℝ≥0) : ℝ≥0∞)) =
      ((1 - θ).toNNReal : ℝ≥0∞)
    congr 1
    apply NNReal.coe_injective
    rw [NNReal.coe_sub hp, NNReal.coe_one, Real.coe_toNNReal θ h0,
      Real.coe_toNNReal (1 - θ) (sub_nonneg.mpr h1)]
  · change ((min θ.toNNReal 1 : ℝ≥0) : ℝ≥0∞) = ENNReal.ofReal θ
    rw [min_eq_left hp]
    rfl

private theorem beta11_likelihood_integral (s f : ℕ) :
    (∫⁻ θ, ENNReal.ofReal (bernoulliLikelihood s f θ)
      ∂betaMeasure 1 1) = ENNReal.ofReal (betaEvidence 1 1 s f) := by
  rw [betaMeasure, lintegral_withDensity_eq_lintegral_mul volume
    (measurable_betaPDFReal 1 1).ennreal_ofReal
    (by unfold bernoulliLikelihood; fun_prop)]
  exact beta_likelihood_normalization_integral 1 1
    (by norm_num) (by norm_num) s f

private theorem beta11_evidence (s f : ℕ) :
    betaEvidence 1 1 s f =
      rising 1 s * rising 1 f / rising 2 (s + f) := by
  have h :=
    JurisLean.Candidates.Final20261021.Probability.u04_1_real_gamma_weight_ratio
      1 1 (by norm_num) (by norm_num) s f
  simpa only [betaEvidence, beta, Nat.cast_add,
    show (1 : ℝ) + 1 = 2 by norm_num,
    add_assoc, add_comm, add_left_comm] using h

private theorem beta11_coin_integral (b : Bool) :
    (∫⁻ θ, coinMass θ b ∂betaMeasure 1 1) = (1 / 2 : ℝ≥0∞) := by
  calc
    (∫⁻ θ, coinMass θ b ∂betaMeasure 1 1) =
        ∫⁻ θ, ENNReal.ofReal
          (bernoulliLikelihood (if b then 1 else 0) (if b then 0 else 1) θ)
          ∂betaMeasure 1 1 := by
      apply lintegral_congr_ae
      filter_upwards [beta11_support] with θ hθ
      rw [coinMass_on_unit θ hθ.1.le hθ.2.le b]
      cases b <;> simp [bernoulliLikelihood]
    _ = (1 / 2 : ℝ≥0∞) := by
      rw [beta11_likelihood_integral, beta11_evidence]
      cases b <;> norm_num [rising]

private theorem beta11_coin_product_integral (a b : Bool) :
    (∫⁻ θ, coinMass θ a * coinMass θ b ∂betaMeasure 1 1) =
      if a = b then (1 / 3 : ℝ≥0∞) else 1 / 6 := by
  calc
    (∫⁻ θ, coinMass θ a * coinMass θ b ∂betaMeasure 1 1) =
        ∫⁻ θ, ENNReal.ofReal
          (bernoulliLikelihood
            ((if a then 1 else 0) + (if b then 1 else 0))
            ((if a then 0 else 1) + (if b then 0 else 1)) θ)
          ∂betaMeasure 1 1 := by
      apply lintegral_congr_ae
      filter_upwards [beta11_support] with θ hθ
      have hn : 0 ≤ (if a then θ else 1 - θ) := by
        cases a <;> simp only [Bool.false_eq_true, if_false, if_true]
        all_goals linarith [hθ.1, hθ.2]
      rw [coinMass_on_unit θ hθ.1.le hθ.2.le a,
        coinMass_on_unit θ hθ.1.le hθ.2.le b,
        ← ENNReal.ofReal_mul hn]
      congr 1
      cases a <;> cases b <;> norm_num [bernoulliLikelihood] <;> ring
    _ = if a = b then (1 / 3 : ℝ≥0∞) else 1 / 6 := by
      rw [beta11_likelihood_integral, beta11_evidence]
      cases a <;> cases b <;> norm_num [rising]

private theorem beta11_pairAtom_integral (a b : Bool) :
    (∫⁻ θ, pairAtom θ (a, b) ∂betaMeasure 1 1) =
      if a = b then (5 / 12 : ℝ≥0∞) else 1 / 12 := by
  have hfirst :
      (∫⁻ θ, (if a = b then coinMass θ a else 0) ∂betaMeasure 1 1) =
        if a = b then (1 / 2 : ℝ≥0∞) else 0 := by
    by_cases hab : a = b <;> simp [hab, beta11_coin_integral]
  calc
    (∫⁻ θ, pairAtom θ (a, b) ∂betaMeasure 1 1) =
        (1 / 2 : ℝ≥0∞) *
          (∫⁻ θ, (if a = b then coinMass θ a else 0) ∂betaMeasure 1 1) +
        (1 / 2 : ℝ≥0∞) *
          (∫⁻ θ, coinMass θ a * coinMass θ b ∂betaMeasure 1 1) := by
      simp only [pairAtom]
      simp_rw [mul_assoc]
      rw [lintegral_add_left
        (by by_cases hab : a = b <;> simp only [hab, if_true, if_false]
            <;> fun_prop),
        lintegral_const_mul' _ _ (by norm_num),
        lintegral_const_mul' _ _ (by norm_num)]
    _ = if a = b then (5 / 12 : ℝ≥0∞) else 1 / 12 := by
      rw [hfirst, beta11_coin_product_integral]
      by_cases hab : a = b <;> norm_num [hab]

/-- Actual generation: first sample the uniform Beta parameter, then the
half-copy/half-independent pair kernel. -/
def halfCopyLaw : Measure (Bool × Bool) :=
  (betaMeasure 1 1).bind halfCopyKernel

instance halfCopyLaw_probability : IsProbabilityMeasure halfCopyLaw where
  measure_univ := by
    rw [halfCopyLaw, Measure.bind_apply MeasurableSet.univ
      halfCopyKernel.aemeasurable]
    simp

private theorem halfCopyLaw_atom (a b : Bool) :
    halfCopyLaw {(a, b)} =
      if a = b then (5 / 12 : ℝ≥0∞) else 1 / 12 := by
  rw [halfCopyLaw, Measure.bind_apply (measurableSet_singleton _)
    halfCopyKernel.aemeasurable]
  simp_rw [halfCopyKernel_singleton]
  exact beta11_pairAtom_integral a b

private theorem halfCopyLaw_apply (s : Set (Bool × Bool)) :
    halfCopyLaw s =
      ∑ a : Bool, ∑ b : Bool,
        if (a, b) ∈ s then
          (if a = b then (5 / 12 : ℝ≥0∞) else 1 / 12) else 0 := by
  have h := Measure.tsum_indicator_apply_singleton halfCopyLaw s
    (show MeasurableSet s from .of_discrete)
  rw [tsum_fintype] at h
  simpa only [Fintype.sum_prod_type, Set.indicator_apply,
    halfCopyLaw_atom] using h.symm

/-- The actual generated law is exchangeable, has positive non-copy mass,
and its actual conditional future probability is 5/6 rather than 2/3. -/
theorem half_copy_exchangeable_counterexample :
    halfCopyLaw.map Prod.swap = halfCopyLaw ∧
    halfCopyLaw {z | z.1 ≠ z.2} = (1 / 6 : ℝ≥0∞) ∧
    0 < halfCopyLaw {z | z.1 ≠ z.2} ∧
    0 < halfCopyLaw {z | z.1 = true} ∧
    (ProbabilityTheory.cond halfCopyLaw {z | z.1 = true})
      {z | z.2 = true} = (5 / 6 : ℝ≥0∞) ∧
    (ProbabilityTheory.cond halfCopyLaw {z | z.1 = true})
      {z | z.2 = true} ≠ (2 / 3 : ℝ≥0∞) := by
  have hswap : halfCopyLaw.map Prod.swap = halfCopyLaw := by
    apply Measure.ext_of_singleton
    rintro ⟨a, b⟩
    rw [Measure.map_apply measurable_swap (measurableSet_singleton _)]
    have he : Prod.swap ⁻¹' {(a, b)} = {(b, a)} := by
      ext z
      simp [Prod.ext_iff, and_comm]
    rw [he, halfCopyLaw_atom, halfCopyLaw_atom]
    cases a <;> cases b <;> simp
  have hneq : halfCopyLaw {z | z.1 ≠ z.2} = (1 / 6 : ℝ≥0∞) := by
    norm_num [halfCopyLaw_apply, Fintype.univ_bool]
  have hfirst : halfCopyLaw {z | z.1 = true} = (1 / 2 : ℝ≥0∞) := by
    norm_num [halfCopyLaw_apply, Fintype.univ_bool]
  have hc :
      (ProbabilityTheory.cond halfCopyLaw {z | z.1 = true})
        {z | z.2 = true} = (5 / 6 : ℝ≥0∞) := by
    rw [ProbabilityTheory.cond_apply
      (show MeasurableSet {z : Bool × Bool | z.1 = true} from .of_discrete)]
    norm_num [halfCopyLaw_apply, Fintype.univ_bool]
  refine ⟨hswap, hneq, ?_, ?_, hc, ?_⟩
  · rw [hneq]
    norm_num
  · rw [hfirst]
    norm_num
  · rw [hc]
    norm_num

open scoped MeasureTheory

private def fixedDataEvent : Set (Bool × Bool) := {z | z.1 = true}
private def nextSuccessEvent : Set (Bool × Bool) := {z | z.2 = true}

/-- Condition the actual joint kernel on the declared data event and project
its future coordinate. At a zero data mass, select the false Dirac version. -/
def observedFutureKernel (joint : Kernel ℝ (Bool × Bool)) : Kernel ℝ Bool := by
  classical
  refine
    { toFun := fun θ => if joint θ fixedDataEvent = 0 then Measure.dirac false
        else (ProbabilityTheory.cond (joint θ) fixedDataEvent).map Prod.snd
      measurable' := ?_ }
  apply Measure.measurable_of_measurable_coe
  intro s hs
  change Measurable (fun θ =>
    (if joint θ fixedDataEvent = 0 then Measure.dirac false
      else (ProbabilityTheory.cond (joint θ) fixedDataEvent).map Prod.snd) s)
  simp only [apply_ite]
  simp_rw [Measure.map_apply measurable_snd hs,
    ProbabilityTheory.cond_apply
      (show MeasurableSet fixedDataEvent from .of_discrete)]
  exact Measurable.ite
    (measurableSet_eq
      (joint.measurable_coe (show MeasurableSet fixedDataEvent from .of_discrete))
      measurable_const)
    measurable_const
    ((joint.measurable_coe
      (show MeasurableSet fixedDataEvent from .of_discrete)).inv.mul
      (joint.measurable_coe
        (show MeasurableSet (fixedDataEvent ∩ Prod.snd ⁻¹' s) from .of_discrete)))

instance observedFutureKernel_markov (joint : Kernel ℝ (Bool × Bool))
    [IsMarkovKernel joint] : IsMarkovKernel (observedFutureKernel joint) where
  isProbabilityMeasure θ := by
    classical
    change IsProbabilityMeasure
      (if joint θ fixedDataEvent = 0 then Measure.dirac false
        else (ProbabilityTheory.cond (joint θ) fixedDataEvent).map Prod.snd)
    by_cases hz : joint θ fixedDataEvent = 0
    · rw [if_pos hz]
      infer_instance
    · rw [if_neg hz]
      letI : IsProbabilityMeasure (ProbabilityTheory.cond (joint θ) fixedDataEvent) :=
        ProbabilityTheory.cond_isProbabilityMeasure hz
      exact Measure.isProbabilityMeasure_map measurable_snd.aemeasurable

private theorem normalized_beta_absolutelyContinuous (α β : ℝ) (s f : ℕ) :
    volume.withDensity (normalizedBetaLikelihood α β s f) ≪ betaMeasure α β := by
  let c : ℝ≥0∞ :=
    (∫⁻ y, betaPDF α β y * ENNReal.ofReal (bernoulliLikelihood s f y))⁻¹
  let w : ℝ → ℝ≥0∞ := fun θ => c * ENNReal.ofReal (bernoulliLikelihood s f θ)
  have hw : Measurable w := by
    dsimp [w]
    unfold bernoulliLikelihood
    fun_prop
  have heq :
      volume.withDensity (normalizedBetaLikelihood α β s f) =
        (betaMeasure α β).withDensity w := by
    rw [betaMeasure, ← withDensity_mul volume
      (measurable_betaPDFReal α β).ennreal_ofReal hw]
    congr 1
    funext θ
    dsimp [w, c, normalizedBetaLikelihood]
    ring
  rw [heq]
  exact withDensity_absolutelyContinuous _ _

private theorem cond_event_of_indepSet
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    {E F : Set Ω} (hE : MeasurableSet E)
    (hpos : 0 < μ E) (hind : IndepSet E F μ) :
    ProbabilityTheory.cond μ E F = μ F := by
  rw [ProbabilityTheory.cond_apply hE μ F,
    hind.measure_inter_eq_mul, ← mul_assoc,
    ENNReal.inv_mul_cancel (ne_of_gt hpos) (measure_ne_top μ E), one_mul]

/-- Given-parameter independence of the observed data event and future success,
together with the count likelihood and Bernoulli marginal, supplies the future
channel from the same actual joint kernel. No posterior channel is assumed. -/
theorem beta_future_success_of_conditional_independence
    (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) (s f : ℕ)
    (joint : Kernel ℝ (Bool × Bool)) [IsMarkovKernel joint]
    (dataLaw : ∀ᵐ θ ∂betaMeasure α β,
      joint θ {z | z.1 = true} = ENNReal.ofReal (bernoulliLikelihood s f θ))
    (independent : ∀ᵐ θ ∂betaMeasure α β,
      IndepSet {z | z.1 = true} {z | z.2 = true} (joint θ))
    (futureLaw : ∀ᵐ θ ∂betaMeasure α β,
      joint θ {z | z.2 = true} = ENNReal.ofReal θ) :
    ((volume.withDensity (normalizedBetaLikelihood α β s f)).bind
      (observedFutureKernel joint)) {true} =
      ENNReal.ofReal ((α + s) / ((α + s) + (β + f))) := by
  apply beta_future_success_of_channel α β hα hβ s f (observedFutureKernel joint)
  have hAC := normalized_beta_absolutelyContinuous α β s f
  have hd := hAC.ae_le dataLaw
  have hi := hAC.ae_le independent
  have hf := hAC.ae_le futureLaw
  have hsupport :
      ∀ᵐ θ ∂(volume.withDensity (normalizedBetaLikelihood α β s f)),
        0 < θ ∧ θ < 1 := by
    rw [positive_real_beta_posterior_measure α β hα hβ s f, betaMeasure,
      ae_withDensity_iff
        (measurable_betaPDFReal (α + s) (β + f)).ennreal_ofReal]
    exact Filter.Eventually.of_forall fun θ hθ => by
      by_contra hout
      exact hθ (by simp [betaPDF, betaPDFReal, hout])
  filter_upwards [hd, hi, hf, hsupport] with θ hdθ hiθ hfθ hθ
  have hl : 0 < bernoulliLikelihood s f θ := by
    unfold bernoulliLikelihood
    exact mul_pos (pow_pos hθ.1 _) (pow_pos (sub_pos.mpr hθ.2) _)
  have hpos : 0 < joint θ fixedDataEvent := by
    change 0 < joint θ {z | z.1 = true}
    rw [hdθ]
    exact ENNReal.ofReal_pos.mpr hl
  change (if joint θ fixedDataEvent = 0 then Measure.dirac false
    else (ProbabilityTheory.cond (joint θ) fixedDataEvent).map Prod.snd) {true} =
      ENNReal.ofReal θ
  rw [if_neg (ne_of_gt hpos),
    Measure.map_apply measurable_snd (measurableSet_singleton true)]
  change (ProbabilityTheory.cond (joint θ) fixedDataEvent) nextSuccessEvent =
    ENNReal.ofReal θ
  rw [cond_event_of_indepSet (joint θ)
    (show MeasurableSet fixedDataEvent from .of_discrete) hpos hiθ, hfθ]
end

end JurisLean.Candidates.BetaFutureSampling20261031