import JurisLean.Candidates.MeasuredPolicy20261027
import JurisLean.Candidates.LearningRisk20261027
import JurisLean.Candidates.LearningFiniteClass20261027
import JurisLean.Candidates.LearningERM20261027
import Mathlib.Probability.ProbabilityMassFunction.Integrals

open scoped BigOperators

namespace JurisLean.Candidates.U12_3MeasuredPolicyBridge20261030

open MeasureTheory ProbabilityTheory
open JurisLean.Candidates.Final20261021
open JurisLean.Candidates.MeasuredPolicy20261027
open JurisLean.Candidates.PolicyEvaluation20261027
open JurisLean.Candidates.LearningRisk20261027
open JurisLean.Candidates.LearningFiniteClass20261027
open JurisLean.Candidates.LearningERM20261027

/-!
CI_NOT_RUN.

This finite Bernoulli law bridges the actual PolicyDatum m = Fin m × Bool × Bool.
It does not restrict the existing general measurable-space uniform bound or
replace the general bounded-outcome IPW/clipping obligations.

The mathematical law below must be the law of the actual iid observations.
Interpreting its response means as potential-outcome means additionally requires
the original consistency, exchangeability, coverage and frozen-environment
conditions. SourceRef fields do not prove those causal claims.
-/

/-- U12.3 blocker: the actual Bool datum needs an explicit logging law,
rather than an assumed score expectation. -/
def frozenPolicyAtom {m : Nat}
    (mass : Fin m → ℚ) (logging : List ℚ)
    (outcome : Fin m → Bool → ℚ) (z : PolicyDatum m) : ℚ :=
  bernoulliVisibleLaw mass (policyProbability logging) outcome
    z.1 z.2.1 z.2.2

/-- U12.3 blocker: the proposed logging atoms must form a real probability law. -/
theorem frozenPolicyAtom_probability {m : Nat}
    (mass : Fin m → ℚ) (hm : ∀ x, 0 ≤ mass x)
    (hmass : ∑ x, mass x = 1)
    (logging : List ℚ)
    (hl : ∀ x : Fin m,
      0 ≤ logging.getD x.val 0 ∧ logging.getD x.val 0 ≤ 1)
    (outcome : Fin m → Bool → ℚ)
    (hy : ∀ x a, 0 ≤ outcome x a ∧ outcome x a ≤ 1) :
    (∀ z, 0 ≤ frozenPolicyAtom mass logging outcome z) ∧
      (∑ z, frozenPolicyAtom mass logging outcome z) = 1 := by
  have actionNonnegative (x : Fin m) (a : Bool) :
      0 ≤ policyProbability logging x a := by
    cases a
    · simpa [policyProbability] using sub_nonneg.mpr (hl x).2
    · simpa [policyProbability] using (hl x).1
  have responseNonnegative (x : Fin m) (a y : Bool) :
      0 ≤ (if y then outcome x a else 1 - outcome x a) := by
    cases y
    · simpa using sub_nonneg.mpr (hy x a).2
    · simpa using (hy x a).1
  constructor
  · intro z
    change 0 ≤ mass z.1 * policyProbability logging z.1 z.2.1 *
      (if z.2.2 then outcome z.1 z.2.1 else 1 - outcome z.1 z.2.1)
    exact mul_nonneg
      (mul_nonneg (hm z.1) (actionNonnegative z.1 z.2.1))
      (responseNonnegative z.1 z.2.1 z.2.2)
  · calc
      (∑ z, frozenPolicyAtom mass logging outcome z) = ∑ x, mass x := by
        simp only [Fintype.sum_prod_type]
        apply Finset.sum_congr rfl
        intro x _
        simp [frozenPolicyAtom, bernoulliVisibleLaw, policyProbability,
          Fintype.sum_bool] <;> ring
      _ = 1 := hmass

/-- U12.3 blocker: instantiate the proved atoms as an actual PMF.
No score/value identity is a constructor field. -/
noncomputable def frozenPolicyJointPMF {m : Nat}
    (mass : Fin m → ℚ) (hm : ∀ x, 0 ≤ mass x)
    (hmass : ∑ x, mass x = 1)
    (logging : List ℚ)
    (hl : ∀ x : Fin m,
      0 ≤ logging.getD x.val 0 ∧ logging.getD x.val 0 ≤ 1)
    (outcome : Fin m → Bool → ℚ)
    (hy : ∀ x a, 0 ≤ outcome x a ∧ outcome x a ≤ 1) :
    PMF (PolicyDatum m) := by
  have probability :=
    frozenPolicyAtom_probability mass hm hmass logging hl outcome hy
  let w : PolicyDatum m → ℝ :=
    fun z => (frozenPolicyAtom mass logging outcome z : ℝ)
  have nonnegative (z : PolicyDatum m) : 0 ≤ w z := by
    dsimp [w]
    exact_mod_cast probability.1 z
  have normalized : ∑ z, w z = 1 := by
    dsimp [w]
    exact_mod_cast probability.2
  exact PMF.ofFintype (fun z => ENNReal.ofReal (w z)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun z _ => nonnegative z),
      normalized]
    exact ENNReal.ofReal_one)

/-- U12.3 blocker: provide the actual score's measurable instance to the existing
uniform bound. This uses only the actual finite datum carrier. -/
theorem actual_policy_score_measurable {m : Nat}
    [MeasurableSpace (PolicyDatum m)]
    [MeasurableSingletonClass (PolicyDatum m)]
    (logging table : List ℚ) :
    Measurable (fun z : PolicyDatum m => (policyScore logging table z : ℝ)) :=
  measurable_of_finite _

/-- U12.3 blocker: derive integrability and E[actual score] = finite value
from the constructed logging law, then reuse finite_policy_ipw.
The nonzero condition is policy coverage, not a causal truth certificate. -/
theorem actual_policy_score_integrable_and_mean {m : Nat}
    [MeasurableSpace (PolicyDatum m)]
    [MeasurableSingletonClass (PolicyDatum m)]
    (mass : Fin m → ℚ) (hm : ∀ x, 0 ≤ mass x)
    (hmass : ∑ x, mass x = 1)
    (logging : List ℚ)
    (hl : ∀ x : Fin m,
      0 ≤ logging.getD x.val 0 ∧ logging.getD x.val 0 ≤ 1)
    (outcome : Fin m → Bool → ℚ)
    (hy : ∀ x a, 0 ≤ outcome x a ∧ outcome x a ≤ 1)
    (table : List ℚ)
    (support : ∀ x a,
      policyProbability table x a ≠ 0 →
        policyProbability logging x a ≠ 0) :
    Integrable (fun z => (policyScore logging table z : ℝ))
        (frozenPolicyJointPMF mass hm hmass logging hl outcome hy).toMeasure ∧
      (∫ z, (policyScore logging table z : ℝ)
        ∂(frozenPolicyJointPMF mass hm hmass logging hl outcome hy).toMeasure) =
        (policyValue mass (policyProbability table) outcome : ℝ) := by
  have probability :=
    frozenPolicyAtom_probability mass hm hmass logging hl outcome hy
  have atomReal (z : PolicyDatum m) :
      ((frozenPolicyJointPMF mass hm hmass logging hl outcome hy) z).toReal =
        (frozenPolicyAtom mass logging outcome z : ℝ) := by
    change (ENNReal.ofReal
      (frozenPolicyAtom mass logging outcome z : ℝ)).toReal = _
    exact ENNReal.toReal_ofReal (by exact_mod_cast probability.1 z)
  have algebra :
      (∑ z : PolicyDatum m,
        frozenPolicyAtom mass logging outcome z *
          policyScore logging table z) =
        policyValue mass (policyProbability table) outcome := by
    calc
      _ = importanceValue mass (policyProbability logging)
          (policyProbability table) outcome := by
        unfold importanceValue
        simp only [Fintype.sum_prod_type]
        apply Finset.sum_congr rfl
        intro x _
        simp [frozenPolicyAtom, bernoulliVisibleLaw, policyScore,
          Behavior.indicator, Fintype.sum_bool] <;> ring
      _ = _ :=
        finite_policy_ipw mass (policyProbability logging)
          (policyProbability table) outcome support
  refine ⟨.of_finite, ?_⟩
  rw [PMF.integral_eq_sum]
  simp only [atomReal, smul_eq_mul]
  have realAlgebra := congrArg (fun q : ℚ => (q : ℝ)) algebra
  push_cast at realAlgebra
  exact realAlgebra

/-- U12.3 blocker: find? does not optimize the entire class.
Compute its actual empirical shortfall over that same fixed class. -/
def policyOptimizationGap {m n : Nat}
    (logging : List ℚ) (data : Fin n → PolicyDatum m)
    (chosen : List ℚ) : List (List ℚ) → ℚ
  | [] => 0
  | h :: rest =>
      max
        (empiricalScore (policyScore logging) data h -
          empiricalScore (policyScore logging) data chosen)
        (policyOptimizationGap logging data chosen rest)

/-- U12.3 blocker: establish the empirical near-optimization premise from
the computed gap, rather than assuming a winner. -/
theorem policyOptimizationGap_dominates {m n : Nat}
    (logging : List ℚ) (data : Fin n → PolicyDatum m)
    (chosen : List ℚ) (family : List (List ℚ)) :
    ∀ h ∈ family,
      empiricalScore (policyScore logging) data h -
        empiricalScore (policyScore logging) data chosen ≤
          policyOptimizationGap logging data chosen family := by
  induction family with
  | nil => simp
  | cons candidate rest ih =>
      intro h member
      rcases List.mem_cons.mp member with rfl | member
      · exact le_max_left _ _
      · exact (ih h member).trans (le_max_right _ _)

/-- U12.3 blocker: connect the actual Some/None selector to 2ε + gap.
The oracle is written as -riskInf(-value), using the existing risk interface.
None is abstention, not a policy recommendation. -/
theorem actual_find_policy_oracle_on_uniform_event {m n : Nat}
    (plan : PolicyPlan) (data : Fin n → PolicyDatum m)
    (allowed : List (List ℚ)) (value : List ℚ → ℝ) (ε : ℝ)
    (uniform : ∀ h ∈ plan.family,
      |(empiricalScore (policyScore plan.logging) data h : ℝ) - value h| ≤ ε) :
    match choosePolicy plan data allowed with
    | none => True
    | some chosen =>
        -riskInf (fun h => -value h) (plan.family.toFinset : Set (List ℚ)) -
            value chosen ≤
          2 * ε +
            (policyOptimizationGap plan.logging data chosen plan.family : ℝ) := by
  classical
  cases selected : choosePolicy plan data allowed with
  | none => trivial
  | some chosen =>
      obtain ⟨_, _, member, _, _⟩ :=
        selected_policy_reads_numeric_bounds_and_permission
          plan data allowed chosen selected
      have oracle := u01_1_uniform_event_erm_oracle
        (fun h => -value h)
        (fun h => -(empiricalScore (policyScore plan.logging) data h : ℝ))
        (plan.family.toFinset : Set (List ℚ))
        chosen (List.mem_toFinset.mpr member) ε
        (policyOptimizationGap plan.logging data chosen plan.family : ℝ)
        (by
          intro h hh
          simpa only [neg_sub_neg] using
            uniform h (List.mem_toFinset.mp hh))
        (by
          intro h hh
          have gap :
              (empiricalScore (policyScore plan.logging) data h : ℝ) -
                  (empiricalScore (policyScore plan.logging) data chosen : ℝ) ≤
                (policyOptimizationGap plan.logging data chosen plan.family : ℝ) := by
            exact_mod_cast policyOptimizationGap_dominates
              plan.logging data chosen plan.family h (List.mem_toFinset.mp hh)
          linarith)
      linarith

/-- U12.3 blocker: supply the actual selector, score and bounds to the existing
iid theorem. This proves a score-population oracle bound; causal value meaning
is supplied separately by the constructed-law bridge and identification premises. -/
theorem actual_find_policy_oracle_probability
    {Ω : Type*} {m n : Nat}
    [MeasurableSpace Ω] [MeasurableSpace (PolicyDatum m)]
    [MeasurableSingletonClass (PolicyDatum m)]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (P : Measure (PolicyDatum m)) [IsProbabilityMeasure P]
    (plan : PolicyPlan) (supported : policyClassSupported m plan = true)
    (nonempty : plan.family.toFinset.Nonempty) (positive : 0 < n)
    (sample : Fin n → Ω → PolicyDatum m)
    (sampleMeasurable : ∀ i, Measurable (sample i))
    (independent : iIndepFun sample μ)
    (law : ∀ i, IdentDistrib (sample i) id μ P)
    (allowed : List (List ℚ))
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) :
    1 - δ ≤ μ.real {w |
      match choosePolicy plan (fun i => sample i w) allowed with
      | none => True
      | some chosen =>
          -riskInf
              (fun h => -(∫ z, (policyScore plan.logging h z : ℝ) ∂P))
              (plan.family.toFinset : Set (List ℚ)) -
            (∫ z, (policyScore plan.logging chosen z : ℝ) ∂P) ≤
          2 * ((plan.weightBound : ℝ) *
            finiteRadius n plan.family.toFinset.card δ) +
          (policyOptimizationGap plan.logging (fun i => sample i w)
            chosen plan.family : ℝ)} := by
  have weightPositiveQ : 0 < plan.weightBound :=
    (of_decide_eq_true supported).1
  have weightPositive : (0 : ℝ) < plan.weightBound := by
    exact_mod_cast weightPositiveQ
  have uniform := bounded_policy_score_uniform μ P positive
    plan.family.toFinset nonempty sample sampleMeasurable independent law
    (fun h z => (policyScore plan.logging h z : ℝ))
    (fun h _ => actual_policy_score_measurable plan.logging h)
    (plan.weightBound : ℝ) weightPositive
    (fun h hh z =>
      supported_scores_are_bounded plan supported h
        (List.mem_toFinset.mp hh) z)
    δ hδ hδ1
  apply le_trans uniform
  apply measureReal_mono (μ := μ) (h₂ := measure_ne_top μ _)
  intro w hw
  apply actual_find_policy_oracle_on_uniform_event
    plan (fun i => sample i w) allowed
    (fun h => ∫ z, (policyScore plan.logging h z : ℝ) ∂P)
    ((plan.weightBound : ℝ) * finiteRadius n plan.family.toFinset.card δ)
  intro h hh
  have bound := hw h (List.mem_toFinset.mpr hh)
  simpa only [empiricalScore_cast, empiricalMean] using bound

/-- U12.3 blocker: the actual selector's probability bound must be about
finite policyValue under the explicitly constructed logging law, rather than
stop at an uninterpreted score expectation. The iid law is bound to that PMF. -/
theorem actual_find_frozen_policyValue_probability
    {Ω : Type*} {m n : Nat}
    [MeasurableSpace Ω] [MeasurableSpace (PolicyDatum m)]
    [MeasurableSingletonClass (PolicyDatum m)]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (plan : PolicyPlan) (supported : policyClassSupported m plan = true)
    (mass : Fin m → ℚ) (hm : ∀ x, 0 ≤ mass x)
    (hmass : ∑ x, mass x = 1)
    (outcome : Fin m → Bool → ℚ)
    (hy : ∀ x a, 0 ≤ outcome x a ∧ outcome x a ≤ 1)
    (nonempty : plan.family.toFinset.Nonempty) (positive : 0 < n)
    (sample : Fin n → Ω → PolicyDatum m)
    (sampleMeasurable : ∀ i, Measurable (sample i))
    (independent : iIndepFun sample μ)
    (law : ∀ i, IdentDistrib (sample i) id μ
      (frozenPolicyJointPMF mass hm hmass plan.logging
        ((of_decide_eq_true supported).2.2.1) outcome hy).toMeasure)
    (allowed : List (List ℚ))
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) :
    1 - δ ≤ μ.real {w |
      match choosePolicy plan (fun i => sample i w) allowed with
      | none => True
      | some chosen =>
          -riskInf
              (fun h => -(policyValue mass (policyProbability h) outcome : ℝ))
              (plan.family.toFinset : Set (List ℚ)) -
            (policyValue mass (policyProbability chosen) outcome : ℝ) ≤
          2 * ((plan.weightBound : ℝ) *
            finiteRadius n plan.family.toFinset.card δ) +
          (policyOptimizationGap plan.logging (fun i => sample i w)
            chosen plan.family : ℝ)} := by
  classical
  have checks := of_decide_eq_true supported
  let hl : ∀ x : Fin m,
      0 ≤ plan.logging.getD x.val 0 ∧ plan.logging.getD x.val 0 ≤ 1 :=
    checks.2.2.1
  let d := frozenPolicyJointPMF mass hm hmass plan.logging hl outcome hy
  let P : Measure (PolicyDatum m) := d.toMeasure
  haveI : IsProbabilityMeasure P := by
    dsimp [P]
    infer_instance
  have means (h : List ℚ) (member : h ∈ plan.family) :
      (∫ z, (policyScore plan.logging h z : ℝ) ∂P) =
        (policyValue mass (policyProbability h) outcome : ℝ) := by
    exact (actual_policy_score_integrable_and_mean
      mass hm hmass plan.logging hl outcome hy h
      (fun x a => ((checks.2.2.2 h member).2 x a).2.2.1)).2
  have oracleEq :
      riskInf (fun h => -(∫ z, (policyScore plan.logging h z : ℝ) ∂P))
          (plan.family.toFinset : Set (List ℚ)) =
        riskInf
          (fun h => -(policyValue mass (policyProbability h) outcome : ℝ))
          (plan.family.toFinset : Set (List ℚ)) := by
    unfold riskInf
    congr 1
    ext r
    constructor
    · rintro ⟨h, hh, rfl⟩
      refine ⟨h, hh, ?_⟩
      rw [means h (List.mem_toFinset.mp hh)]
    · rintro ⟨h, hh, rfl⟩
      refine ⟨h, hh, ?_⟩
      rw [means h (List.mem_toFinset.mp hh)]
  have raw := actual_find_policy_oracle_probability
    μ P plan supported nonempty positive sample sampleMeasurable
    independent law allowed δ hδ hδ1
  apply le_trans raw
  apply measureReal_mono (μ := μ) (h₂ := measure_ne_top μ _)
  intro w hw
  cases selected : choosePolicy plan (fun i => sample i w) allowed with
  | none => simp only [Set.mem_setOf_eq, selected]
  | some chosen =>
      simp only [Set.mem_setOf_eq, selected] at hw ⊢
      have member :=
        (selected_policy_reads_numeric_bounds_and_permission
          plan (fun i => sample i w) allowed chosen selected).2.2.1
      rw [oracleEq, means chosen member] at hw
      exact hw


/-- U12.3 blocker: the existing pointwise clipping identity and finite upper
bound do not yet expose the exact expectation bias. Derive clipped/tail
integrability from the actual full weighted outcome, without a global weight cap. -/
theorem clipped_weighted_expectation_exact
    {Z : Type*} [MeasurableSpace Z]
    (P : Measure Z) (w y : Z → ℝ) (c : ℝ)
    (weightMeasurable : Measurable w) (outcomeMeasurable : Measurable y)
    (weightNonnegative : ∀ z, 0 ≤ w z) (capNonnegative : 0 ≤ c)
    (outcomeBounded : ∀ z, 0 ≤ y z ∧ y z ≤ 1)
    (fullIntegrable : Integrable (fun z => w z * y z) P) :
    Integrable (fun z => min (w z) c * y z) P ∧
      Integrable (fun z => max (w z - c) 0 * y z) P ∧
      (∫ z, w z * y z ∂P) - (∫ z, min (w z) c * y z ∂P) =
        ∫ z, max (w z - c) 0 * y z ∂P := by
  have clipMeasurable : Measurable (fun z => min (w z) c * y z) :=
    (weightMeasurable.min measurable_const).mul outcomeMeasurable
  have clipNormBound (z : Z) : ‖min (w z) c * y z‖ ≤ w z * y z := by
    have nonnegative : 0 ≤ min (w z) c * y z :=
      mul_nonneg (le_min (weightNonnegative z) capNonnegative)
        (outcomeBounded z).1
    rw [Real.norm_eq_abs, abs_of_nonneg nonnegative]
    exact mul_le_mul_of_nonneg_right (min_le_left _ _) (outcomeBounded z).1
  have clipIntegrable : Integrable (fun z => min (w z) c * y z) P :=
    Integrable.mono' fullIntegrable clipMeasurable.aestronglyMeasurable
      (ae_of_all _ clipNormBound)
  have point (z : Z) :
      w z * y z - min (w z) c * y z = max (w z - c) 0 * y z :=
    (Policy.u12_3_clipped_bias (w z) c (y z) (weightNonnegative z)
      capNonnegative (outcomeBounded z).1 (outcomeBounded z).2).1
  have difference : (fun z => w z * y z - min (w z) c * y z) =
      (fun z => max (w z - c) 0 * y z) := funext point
  have tailIntegrable : Integrable (fun z => max (w z - c) 0 * y z) P := by
    rw [← difference]
    exact fullIntegrable.sub clipIntegrable
  refine ⟨clipIntegrable, tailIntegrable, ?_⟩
  calc
    _ = ∫ z, w z * y z - min (w z) c * y z ∂P :=
      (integral_sub fullIntegrable clipIntegrable).symm
    _ = _ := integral_congr_ae (ae_of_all _ point)

/-- U12.3 blocker: instantiate exact clipping bias for the actual score and
constructed logging distribution, replacing the full-score expectation by
finite policyValue through the proved IPW bridge. -/
theorem actual_policy_clipping_bias {m : Nat}
    [MeasurableSpace (PolicyDatum m)]
    [MeasurableSingletonClass (PolicyDatum m)]
    (plan : PolicyPlan) (supported : policyClassSupported m plan = true)
    (mass : Fin m → ℚ) (hm : ∀ x, 0 ≤ mass x)
    (hmass : ∑ x, mass x = 1)
    (outcome : Fin m → Bool → ℚ)
    (hy : ∀ x a, 0 ≤ outcome x a ∧ outcome x a ≤ 1)
    (table : List ℚ) (member : table ∈ plan.family)
    (c : ℝ) (capNonnegative : 0 ≤ c) :
    let d := frozenPolicyJointPMF mass hm hmass plan.logging
      ((of_decide_eq_true supported).2.2.1) outcome hy
    let weight : PolicyDatum m → ℝ := fun z =>
      ((policyProbability table z.1 z.2.1 /
        policyProbability plan.logging z.1 z.2.1 : ℚ) : ℝ)
    let result : PolicyDatum m → ℝ := fun z => (Behavior.indicator z.2.2 : ℝ)
    (policyValue mass (policyProbability table) outcome : ℝ) -
        (∫ z, min (weight z) c * result z ∂d.toMeasure) =
      ∫ z, max (weight z - c) 0 * result z ∂d.toMeasure := by
  classical
  have checks := of_decide_eq_true supported
  let hl : ∀ x : Fin m,
      0 ≤ plan.logging.getD x.val 0 ∧ plan.logging.getD x.val 0 ≤ 1 :=
    checks.2.2.1
  let d := frozenPolicyJointPMF mass hm hmass plan.logging hl outcome hy
  let weight : PolicyDatum m → ℝ := fun z =>
    ((policyProbability table z.1 z.2.1 /
      policyProbability plan.logging z.1 z.2.1 : ℚ) : ℝ)
  let result : PolicyDatum m → ℝ := fun z => (Behavior.indicator z.2.2 : ℝ)
  change (policyValue mass (policyProbability table) outcome : ℝ) -
      (∫ z, min (weight z) c * result z ∂d.toMeasure) =
    ∫ z, max (weight z - c) 0 * result z ∂d.toMeasure
  have mean := actual_policy_score_integrable_and_mean
    mass hm hmass plan.logging hl outcome hy table
    (fun x a => ((checks.2.2.2 table member).2 x a).2.2.1)
  have fullEq : (fun z : PolicyDatum m => weight z * result z) =
      (fun z => (policyScore plan.logging table z : ℝ)) := by
    funext z
    simp only [weight, result, policyScore, Rat.cast_mul]
  have weightNonnegative (z : PolicyDatum m) : 0 ≤ weight z := by
    dsimp [weight]
    exact_mod_cast ((checks.2.2.2 table member).2 z.1 z.2.1).2.2.2.1
  have outcomeBounded (z : PolicyDatum m) : 0 ≤ result z ∧ result z ≤ 1 := by
    cases truth : z.2.2 <;> norm_num [result, Behavior.indicator, truth]
  have fullIntegrable : Integrable (fun z => weight z * result z) d.toMeasure := by
    rw [fullEq]
    exact mean.1
  have bias := clipped_weighted_expectation_exact d.toMeasure weight result c
    (measurable_of_finite _) (measurable_of_finite _)
    weightNonnegative capNonnegative outcomeBounded fullIntegrable
  have exactBias := bias.2.2
  rw [fullEq, mean.2] at exactBias
  exact exactBias

end JurisLean.Candidates.U12_3MeasuredPolicyBridge20261030
