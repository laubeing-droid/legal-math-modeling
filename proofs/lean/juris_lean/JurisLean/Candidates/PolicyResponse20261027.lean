import JurisLean.Candidates.Final20261021.Policy
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecificLimits.Normed

/-!
Original 12.1, 12.2 and the information boundary of 12.6 / S12.
The finite response table and logit model are stated models, not claims about
actual human response. Stability and allowed legal policies remain separate.
-/

namespace JurisLean.Candidates.PolicyResponse20261027

open Filter Function
open scoped Topology

def preparationScore (b : Fin 3) : ℚ := if b.val = 0 then 0 else 1
def preparationQuality (b : Fin 3) : ℚ := if b.val = 1 then 1 else 0
def preparationCost (b : Fin 3) : ℚ := if b.val = 1 then 3/5 else if b.val = 2 then 1/10 else 0
def preparationUtility (threshold : ℚ) (b : Fin 3) : ℚ :=
  (if threshold ≤ preparationScore b then 1 else 0) - preparationCost b

theorem finite_response_payoffs (threshold : ℚ) (positive : 0 < threshold) (small : threshold ≤ 1) :
    preparationUtility threshold 0 = 0 ∧
    preparationUtility threshold 1 = 2/5 ∧ preparationUtility threshold 2 = 9/10 ∧
    (∀ b, b ≠ 2 → preparationUtility threshold b < preparationUtility threshold 2) := by
  have zero : ¬ threshold ≤ 0 := not_le.mpr positive
  refine ⟨?_, ?_, ?_, ?_⟩
  · norm_num [preparationUtility, preparationScore, preparationCost, zero, small]
  · norm_num [preparationUtility, preparationScore, preparationCost, zero, small]
  · norm_num [preparationUtility, preparationScore, preparationCost, zero, small]
  · intro b different
    fin_cases b <;>
      norm_num [preparationUtility, preparationScore, preparationCost, zero, small, Fin.ext_iff] at *

theorem score_only_cannot_distinguish_preparation (passProbability : ℚ → ℚ) :
    passProbability (preparationScore 1) = passProbability (preparationScore 2) ∧
    preparationQuality 1 = 1 ∧ preparationQuality 2 = 0 := by
  norm_num [preparationScore, preparationQuality]

noncomputable def logitPreparation (beta : ℝ) (b : Fin 3) : ℝ :=
  Real.exp (beta * ((preparationUtility (1/2) b : ℝ) - 9/10)) /
    ∑ i : Fin 3, Real.exp (beta * ((preparationUtility (1/2) i : ℝ) - 9/10))

theorem logit_is_original_softmax (beta : ℝ) (b : Fin 3) :
    logitPreparation beta b =
      Real.exp (beta * (preparationUtility (1/2) b : ℝ)) /
        ∑ i : Fin 3, Real.exp (beta * (preparationUtility (1/2) i : ℝ)) := by
  have factor (i : Fin 3) :
      Real.exp (beta * ((preparationUtility (1/2) i : ℝ) - 9/10)) =
        Real.exp (-beta * (9/10)) * Real.exp (beta * (preparationUtility (1/2) i : ℝ)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  unfold logitPreparation
  simp_rw [factor]
  rw [← Finset.mul_sum]
  exact mul_div_mul_left _ _ (Real.exp_ne_zero _)

theorem logit_is_probability (beta : ℝ) :
    (∑ b : Fin 3, logitPreparation beta b) = 1 ∧ ∀ b, 0 < logitPreparation beta b := by
  have total : 0 < ∑ i : Fin 3, Real.exp (beta * ((preparationUtility (1/2) i : ℝ) - 9/10)) :=
    Finset.sum_pos (fun _ _ => Real.exp_pos _) Finset.univ_nonempty
  constructor
  · simp only [logitPreparation, ← Finset.sum_div]
    exact div_self total.ne'
  · intro b
    exact div_pos (Real.exp_pos _) total

noncomputable def logitQuality (beta : ℝ) : ℝ :=
  ∑ b : Fin 3, logitPreparation beta b * (preparationQuality b : ℝ)
noncomputable def logitScore (beta : ℝ) : ℝ :=
  ∑ b : Fin 3, logitPreparation beta b * (preparationScore b : ℝ)

theorem logit_actual_means (beta : ℝ) :
    logitQuality beta = Real.exp (-(1/2) * beta) /
      (Real.exp (-(9/10) * beta) + Real.exp (-(1/2) * beta) + 1) ∧
    logitScore beta = (Real.exp (-(1/2) * beta) + 1) /
      (Real.exp (-(9/10) * beta) + Real.exp (-(1/2) * beta) + 1) := by
  have weight (b : Fin 3) :
      Real.exp (beta * ((preparationUtility (1/2) b : ℝ) - 9/10)) =
      if b.val = 0 then Real.exp (-(9/10) * beta)
      else if b.val = 1 then Real.exp (-(1/2) * beta) else 1 := by
    fin_cases b <;>
      norm_num [preparationUtility, preparationScore, preparationCost] <;> ring
  constructor <;>
    norm_num [logitQuality, logitScore, logitPreparation, weight,
      preparationQuality, preparationScore, Fin.sum_univ_succ] <;> ring

theorem logit_zero_means :
    logitQuality 0 = 1/3 ∧ logitScore 0 = 2/3 := by
  rw [(logit_actual_means 0).1, (logit_actual_means 0).2]
  norm_num

theorem logit_high_rationality_limits :
    Tendsto logitQuality atTop (𝓝 0) ∧ Tendsto logitScore atTop (𝓝 1) := by
  have first : Tendsto (fun beta : ℝ => Real.exp (-(9/10) * beta)) atTop (𝓝 0) := by
    simpa only [neg_mul] using Real.tendsto_exp_neg_atTop_nhds_zero.comp
      (tendsto_id.const_mul_atTop (show (0 : ℝ) < 9/10 by norm_num))
  have second : Tendsto (fun beta : ℝ => Real.exp (-(1/2) * beta)) atTop (𝓝 0) := by
    simpa only [neg_mul] using Real.tendsto_exp_neg_atTop_nhds_zero.comp
      (tendsto_id.const_mul_atTop (show (0 : ℝ) < 1/2 by norm_num))
  have denominator : Tendsto
      (fun beta : ℝ => Real.exp (-(9/10) * beta) + Real.exp (-(1/2) * beta) + 1)
      atTop (𝓝 1) := by
    simpa using (first.add second).add_const 1
  constructor
  · convert second.div denominator (by norm_num : (1 : ℝ) ≠ 0) using 1
    · ext beta
      exact (logit_actual_means beta).1
    · norm_num
  · convert (second.add_const 1).div denominator (by norm_num : (1 : ℝ) ≠ 0) using 1
    · ext beta
      exact (logit_actual_means beta).2
    · norm_num

-- One algebraic implementation is used over Q for exact execution and over R
-- for the original full-domain convergence statements.
def affineResponse {K : Type*} [Field K] (q x : K) : K := 1/2 + q*(x-1/2)
def dampedResponse {K : Type*} [Field K] (rate x : K) : K :=
  (1-rate)*x + rate*(1-x)

theorem affine_iterate_formula {K : Type*} [Field K] (q x : K) (n : Nat) :
    (affineResponse q)^[n] x = 1/2 + q^n*(x-1/2) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply', ih]
      unfold affineResponse
      rw [pow_succ]
      ring

theorem original_maps_and_unique_fixed_points (x : ℝ) :
    affineResponse (1/2) x = 1/4+x/2 ∧ affineResponse (-1) x = 1-x ∧
    (affineResponse (1/2) x = x ↔ x = 1/2) ∧
    (affineResponse (-1) x = x ↔ x = 1/2) := by
  unfold affineResponse
  constructor
  · ring
  constructor
  · ring
  constructor <;> constructor <;> intro h <;> linarith

theorem affine_converges_to_center (q x : ℝ) (contractive : |q| < 1) :
    Tendsto (fun n : Nat => (affineResponse q)^[n] x) atTop (𝓝 (1/2)) := by
  have powers := tendsto_pow_atTop_nhds_zero_of_abs_lt_one contractive
  have shifted : Tendsto (fun n : Nat => (1/2 : ℝ) + q^n*(x-1/2)) atTop
      (𝓝 ((1/2 : ℝ) + 0*(x-1/2))) :=
    (powers.mul_const (x-1/2)).const_add (1/2 : ℝ)
  simpa only [affine_iterate_formula, zero_mul, add_zero] using shifted

theorem reflection_has_no_limit_except_center (x : ℝ) (away : x ≠ 1/2) :
    ¬ ∃ limit, Tendsto (fun n : Nat => (affineResponse (-1))^[n] x) atTop (𝓝 limit) := by
  rintro ⟨limit, converges⟩
  have shifted := converges.comp (tendsto_add_atTop_nat 1)
  have reflected : Tendsto (fun n : Nat => (affineResponse (-1))^[n+1] x)
      atTop (𝓝 (1-limit)) := by
    convert tendsto_const_nhds.sub converges using 1
    ext n
    rw [Function.iterate_succ_apply']
    unfold affineResponse
    ring
  have unique := tendsto_nhds_unique shifted reflected
  have center : limit = 1/2 := by linarith
  subst limit
  have distance (n : Nat) : |(affineResponse (-1))^[n] x - 1/2| = |x-1/2| := by
    rw [affine_iterate_formula]
    simp [abs_mul, abs_pow]
  have normLimit := (converges.sub_const (1/2)).abs
  have constantLimit : Tendsto (fun _ : Nat => |x-1/2|) atTop (𝓝 0) := by
    simpa only [distance, sub_self, abs_zero] using normLimit
  have zero : |x-1/2| = 0 := tendsto_nhds_unique tendsto_const_nhds constantLimit
  exact away (sub_eq_zero.mp (abs_eq_zero.mp zero))

theorem damped_as_affine (rate : ℝ) :
    dampedResponse rate = affineResponse (1-2*rate) := by
  funext x
  unfold dampedResponse affineResponse
  ring

theorem damped_preserves_unit_interval (rate x : ℝ)
    (hr : rate ∈ Set.Icc 0 1) (hx : x ∈ Set.Icc 0 1) :
    dampedResponse rate x ∈ Set.Icc 0 1 := by
  have h0 := mul_nonneg (sub_nonneg.mpr hr.2) hx.1
  have h1 := mul_nonneg hr.1 (sub_nonneg.mpr hx.2)
  have h2 := mul_nonneg hr.1 hx.1
  have h3 := mul_nonneg (sub_nonneg.mpr hr.2) (sub_nonneg.mpr hx.2)
  unfold dampedResponse
  constructor <;> nlinarith

theorem damping_converges_for_all_iff (rate : ℝ) :
    (∀ x ∈ Set.Icc (0 : ℝ) 1,
      Tendsto (fun n : Nat => (dampedResponse rate)^[n] x) atTop (𝓝 (1/2))) ↔
      0 < rate ∧ rate < 1 := by
  constructor
  · intro all
    have atZero := all 0 (by norm_num)
    have scaled := (atZero.sub_const (1/2)).mul_const (-2)
    simp only [sub_self, zero_mul] at scaled
    have powers : Tendsto (fun n : Nat => (1-2*rate)^n) atTop (𝓝 0) := by
      convert scaled using 1
      ext n
      rw [damped_as_affine, affine_iterate_formula]
      ring
    have normBound := tendsto_pow_atTop_nhds_zero_iff_norm_lt_one.mp powers
    have absBound : |1-2*rate| < 1 := by simpa [Real.norm_eq_abs] using normBound
    obtain ⟨lower, upper⟩ := abs_lt.mp absBound
    constructor <;> linarith
  · rintro ⟨positive, below⟩ x _
    rw [damped_as_affine]
    exact affine_converges_to_center _ _ (abs_lt.mpr ⟨by linarith, by linarith⟩)

noncomputable def localResponse (x : ℝ) : ℝ := if x ≤ 1/2 then x/2 else 1

theorem local_affine_behavior_does_not_give_global_contraction :
    (∀ x ≤ (1/2 : ℝ), localResponse x = x/2) ∧
    localResponse 0 = 0 ∧ localResponse 1 = 1 := by
  refine ⟨fun x hx => by simp only [localResponse, if_pos hx], ?_, ?_⟩ <;>
    norm_num [localResponse]

theorem stable_fixed_point_can_be_outside_legal_constraint :
    affineResponse (1/2 : ℝ) (1/2) = 1/2 ∧
    (∀ x : ℝ, Tendsto (fun n : Nat => (affineResponse (1/2))^[n] x) atTop (𝓝 (1/2))) ∧
    (1/2 : ℝ) ∉ Set.Icc 0 (1/4) := by
  refine ⟨by norm_num [affineResponse], fun x => affine_converges_to_center _ x (by norm_num), ?_⟩
  norm_num

-- The two legal environments have the same behavioral data, response and
-- value input; only the independently supplied admissible set differs.
theorem behavior_only_cannot_recover_admissible_sets {Data : Type*}
    (observations : Data) (algorithm : Data → Finset Nat) :
    ¬ (algorithm observations = {1} ∧ algorithm observations = ∅) := by
  rintro ⟨one, empty⟩
  rw [one] at empty
  exact Finset.singleton_ne_empty 1 empty

end JurisLean.Candidates.PolicyResponse20261027

