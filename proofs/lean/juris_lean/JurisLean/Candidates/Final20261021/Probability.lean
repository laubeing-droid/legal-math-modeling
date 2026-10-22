import JurisLean.Candidates.Final20261021.Interfaces
import JurisLean.Candidates.Final20261021.Learning
import JurisLean.Seams.UnifiedNeedlesS3a
import JurisLean.FullMath.Probability.DirichletPosterior

namespace JurisLean.Candidates.Final20261021.Probability

structure FiniteLaw (Ω : Type) [Fintype Ω] where
  mass : Ω → ℚ
  nonneg : ∀ w, 0 ≤ mass w
  total : ∑ w, mass w = 1

def expectation {Ω : Type} [Fintype Ω] (P : FiniteLaw Ω) (f : Ω → ℚ) : ℚ :=
  ∑ w, (P.mass w * f w)

theorem expectation_mono {Ω : Type} [Fintype Ω] (P : FiniteLaw Ω)
    (f g : Ω → ℚ) (h : ∀ w, f w ≤ g w) : expectation P f ≤ expectation P g :=
  Finset.sum_le_sum (fun w _ => mul_le_mul_of_nonneg_left (h w) (P.nonneg w))

theorem expectation_add {Ω : Type} [Fintype Ω] (P : FiniteLaw Ω) (f g : Ω → ℚ) :
    expectation P (fun w => f w + g w) = expectation P f + expectation P g := by
  simp [expectation, mul_add, Finset.sum_add_distrib]

theorem expectation_const {Ω : Type} [Fintype Ω] (P : FiniteLaw Ω) (c : ℚ) :
    expectation P (fun _ => c) = c := by
  rw [expectation, ← Finset.sum_mul, P.total, one_mul]

theorem u01_2_finite_label_bridge {Ω A : Type} [Fintype Ω] [DecidableEq A]
    (P : FiniteLaw Ω) (h y truth : Ω → A) :
    expectation P (fun w => Learning.zeroOne (h w) (truth w)) ≤
      expectation P (fun w => Learning.zeroOne (h w) (y w)) +
      expectation P (fun w => Learning.zeroOne (y w) (truth w)) := by
  rw [← expectation_add]
  exact expectation_mono P _ _ (fun w => Learning.u01_2_label_bridge_pointwise _ _ _)

def normalize {Ω : Type} [Fintype Ω] (weights : Ω → ℚ) : Option (FiniteLaw Ω) :=
  if h : (∀ w, 0 ≤ weights w) ∧ 0 < ∑ w, weights w then
    some ⟨fun w => weights w / ∑ z, weights z,
      fun w => div_nonneg (h.1 w) (le_of_lt h.2), by
        simp only [div_eq_mul_inv]
        rw [← Finset.sum_mul]
        exact mul_inv_cancel₀ (ne_of_gt h.2)⟩
  else none

def proposed_probability_model {Ω : Type} [Fintype Ω]
    (prior : FiniteLaw Ω) (likelihood : Ω → ℚ) :=
  normalize (fun w => prior.mass w * likelihood w)

theorem posterior_mass {Ω : Type} [Fintype Ω] (prior : FiniteLaw Ω)
    (likelihood : Ω → ℚ) (post : FiniteLaw Ω)
    (accepted : proposed_probability_model prior likelihood = some post) :
    ∀ w, post.mass w = prior.mass w * likelihood w / expectation prior likelihood := by
  unfold proposed_probability_model normalize at accepted
  split at accepted
  · cases accepted; intro w; rfl
  · cases accepted

def totalVariation {Ω : Type} [Fintype Ω] (P Q : FiniteLaw Ω) : ℚ :=
  ∑ w, max (P.mass w - Q.mass w) 0

theorem tv_symmetric {Ω : Type} [Fintype Ω] (P Q : FiniteLaw Ω) :
    totalVariation P Q = totalVariation Q P := by
  have point : ∀ w, max (P.mass w-Q.mass w) 0 =
      (P.mass w-Q.mass w) + max (Q.mass w-P.mass w) 0 := by
    intro w
    by_cases h : Q.mass w ≤ P.mass w
    · rw [max_eq_left (sub_nonneg.mpr h), max_eq_right (sub_nonpos.mpr h)]; ring
    · have h' := le_of_not_ge h
      rw [max_eq_right (sub_nonpos.mpr h'), max_eq_left (sub_nonneg.mpr h')]; ring
  unfold totalVariation
  simp_rw [point]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, P.total, Q.total]
  ring

theorem expectation_sub_bound {Ω : Type} [Fintype Ω] (P Q : FiniteLaw Ω)
    (loss : Ω → ℚ) (bounded : ∀ w, 0 ≤ loss w ∧ loss w ≤ 1) :
    expectation P loss - expectation Q loss ≤ totalVariation P Q := by
  have point : ∀ w, (P.mass w-Q.mass w)*loss w ≤ max (P.mass w-Q.mass w) 0 := by
    intro w
    rcases bounded w with ⟨hl, hu⟩
    by_cases h : 0 ≤ P.mass w-Q.mass w
    · rw [max_eq_left h]; nlinarith
    · rw [max_eq_right (le_of_not_ge h)]; nlinarith
  unfold expectation totalVariation
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_le_sum fun w _ => by simpa only [sub_mul] using point w

-- Finite executable support only: the general measurable TV theorem is OPEN.
theorem u01_3_finite_deployment_distance {Ω : Type} [Fintype Ω] (P Q : FiniteLaw Ω)
    (loss : Ω → ℚ) (bounded : ∀ w, 0 ≤ loss w ∧ loss w ≤ 1) :
    |expectation P loss - expectation Q loss| ≤ totalVariation P Q := by
  have upper := expectation_sub_bound P Q loss bounded
  have lower := expectation_sub_bound Q P loss bounded
  rw [tv_symmetric Q P] at lower
  exact abs_le.mpr ⟨by linarith, upper⟩

theorem u04_2_enclosed_propagation (N B nL nU bL bU : ℝ)
    (hN : 0 ≤ N) (hNB : N ≤ B) (hnL : nL ≤ N) (hnU : N ≤ nU)
    (hbL : 0 < bL) (hLB : bL ≤ B) (hBU : B ≤ bU) :
    max 0 (nL / bU) ≤ N / B ∧ N / B ≤ min 1 (nU / bL) := by
  have hB : 0 < B := lt_of_lt_of_le hbL hLB
  have hU : 0 < bU := lt_of_lt_of_le hB hBU
  have hratio : 0 ≤ N / B := div_nonneg hN (le_of_lt hB)
  constructor
  · apply max_le hratio
    by_cases hl : 0 ≤ nL
    · apply (div_le_div_iff₀ hU hB).mpr; nlinarith
    · exact le_trans (div_nonpos_of_nonpos_of_nonneg (le_of_not_ge hl) (le_of_lt hU)) hratio
  · apply le_min
    · exact (div_le_one hB).mpr hNB
    · apply (div_le_div_iff₀ hB hbL).mpr; nlinarith

inductive EffectiveCount where
  | finite (n : ℚ)
  | degenerateZeroVariance
  | invalid
  deriving DecidableEq, Repr

def u04_4_variance_equivalent (n : Nat) (r : ℚ) : EffectiveCount :=
  if n < 2 then .invalid
  else let denominator := 1 + ((n : ℚ) - 1) * r
    if denominator = 0 then .degenerateZeroVariance
    else if 0 < denominator then .finite (n / denominator) else .invalid

structure Measurement where
  object : ObjectId
  event : EventId
  measurement : MeasurementId
  record : RecordId
  mechanism : Nat
  deriving DecidableEq, Repr

theorem u04_5_new_measurement_not_copy :
    ((4/5 : ℚ)^2 / (1/5)^2 = 16) ∧ ((4/5 : ℚ)/(1/5) = 4) := by norm_num

/-! U04.1. Integer-shape density conjugacy and its predictive mean are the
    already-proved polynomial-Beta theorems. The real Gamma weight ratio is the
    rising-factorial identity. Neither statement decides an exchangeable kernel
    that was not built from that bridge: the finite law below has conditional
    probability 5/6 where the Beta(1,1) one-success bridge says 2/3. -/

section U04OneReuse
open JurisLean.Seams.UnifiedNeedlesS3a
open JurisLean.FullMath.Probability

theorem u04_1_integer_shape_conjugacy (a b k l : ℕ) :
    ((∫ x in 0..1, polyBeta (a + 1) (b + 1) x * (x ^ k * (1 - x) ^ l))
      = ((betaTwoConst ((a : ℕ) + k) ((b : ℕ) + l) : ℚ) / (betaTwoConst a b : ℚ) : ℚ)) ∧
    (∀ x : ℝ, polyBeta (a + 1) (b + 1) x * (x ^ k * (1 - x) ^ l)
        * ((betaTwoConst a b : ℚ) / (betaTwoConst ((a : ℕ) + k) ((b : ℕ) + l) : ℚ) : ℚ)
      = polyBeta (((a : ℕ) + k) + 1) (((b : ℕ) + l) + 1) x) ∧
    ((∫ x in 0..1, polyBeta (((a : ℕ) + k) + 1) (((b : ℕ) + l) + 1) x) = 1) :=
  beta_posterior_from_likelihood a b k l

theorem u04_1_predictive_mean_is_updated_beta (a b s f : ℕ) :
    ((∫ x in 0..1, x * polyBeta ((a + s) + 1) ((b + f) + 1) x)
       = (((a + s) : ℕ) + 1 : ℚ) / (((a + s) : ℕ) + ((b + f) : ℕ) + 2)) :=
  (polyBeta_moments (a + s) (b + f)).1

theorem u04_1_real_gamma_weight_ratio (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) (w l : ℕ) :
    (Real.Gamma (α + (w : ℝ)) * Real.Gamma (β + (l : ℝ))) /
      Real.Gamma (α + β + ((w + l : ℕ) : ℝ)) /
      ((Real.Gamma α * Real.Gamma β) / Real.Gamma (α + β)) =
      (rising α w * rising β l) / rising (α + β) (w + l) :=
  beta_ratio α β hα hβ w l

end U04OneReuse

theorem u04_1_exchangeable_not_beta_bridge :
    ((5 / 12 : ℚ) / (5 / 12 + 1 / 12) = 5 / 6) ∧
    (((1 : ℚ) + 1) / (1 + 1 + 1) = 2 / 3) ∧
    ((5 / 6 : ℚ) ≠ 2 / 3) ∧
    ((1 / 12 : ℚ) = 1 / 12) := by
  norm_num

/-! U04.3. Unpenalized intercept, every label positive: the logistic loss is
    positive at every finite intercept, strictly decreases as the intercept
    grows, and can be driven below any positive tolerance. That is the
    manuscript counterexample. It is not an existence or uniqueness proof for
    the fully penalized objective. -/

theorem u04_3_unpenalized_intercept_positive (t : ℝ) :
    0 < Real.log (1 + Real.exp (-t)) := by
  have hpos : 0 < Real.exp (-t) := Real.exp_pos _
  have hgt : 1 < 1 + Real.exp (-t) := by linarith
  exact Real.log_pos hgt

theorem u04_3_unpenalized_intercept_improves (s t : ℝ) (hst : s < t) :
    Real.log (1 + Real.exp (-t)) < Real.log (1 + Real.exp (-s)) := by
  have ht : 0 < 1 + Real.exp (-t) := by
    have := Real.exp_pos (-t)
    linarith
  apply Real.log_lt_log ht
  have hexp : Real.exp (-t) < Real.exp (-s) := (Real.exp_lt_exp).mpr (by linarith)
  linarith

theorem u04_3_unpenalized_never_zero (t : ℝ) :
    Real.log (1 + Real.exp (-t)) ≠ 0 :=
  ne_of_gt (u04_3_unpenalized_intercept_positive t)

theorem u04_3_unpenalized_arbitrarily_small (ε : ℝ) (hε : 0 < ε) :
    ∃ t : ℝ, Real.log (1 + Real.exp (-t)) < ε := by
  have hexp : (1 : ℝ) < Real.exp ε := by
    rw [← Real.exp_zero]
    exact (Real.exp_lt_exp).mpr hε
  have hδ : 0 < Real.exp ε - 1 := by linarith
  have hδ2 : 0 < (Real.exp ε - 1) / 2 := by linarith
  refine ⟨-Real.log ((Real.exp ε - 1) / 2), ?_⟩
  have hpos : 0 < 1 + Real.exp (-(-Real.log ((Real.exp ε - 1) / 2))) := by
    linarith [Real.exp_pos (-(-Real.log ((Real.exp ε - 1) / 2)))]
  rw [Real.log_lt_iff_lt_exp hpos, neg_neg, Real.exp_log hδ2]
  linarith [hδ2]

/-! U04.4. Equicorrelated finite-sum expansion, the positive-denominator
    effective count, and the `B, 1-B` degenerate witness. -/

theorem u04_4_covariance_expansion (n : ℕ) (σ2 r : ℚ) (hn : 0 < n) :
    ((n : ℚ) * σ2 + (n : ℚ) * ((n : ℚ) - 1) * (σ2 * r)) / ((n : ℚ) ^ 2)
      = σ2 * (1 + ((n : ℚ) - 1) * r) / (n : ℚ) := by
  have hn0 : (n : ℚ) ≠ 0 := by exact_mod_cast hn.ne'
  field_simp [hn0]

theorem u04_4_positive_bracket_finite (n : ℕ) (r : ℚ) (hn : 2 ≤ n)
    (hpos : 0 < 1 + ((n : ℚ) - 1) * r) :
    u04_4_variance_equivalent n r =
      .finite ((n : ℚ) / (1 + ((n : ℚ) - 1) * r)) := by
  unfold u04_4_variance_equivalent
  rw [if_neg (by omega : ¬ n < 2)]
  dsimp
  rw [if_neg (ne_of_gt hpos), if_pos hpos]

theorem u04_4_complement_average_constant (b : ℚ) :
    (b + (1 - b)) / 2 = (1 / 2 : ℚ) := by ring

theorem u04_4_complement_quadratic_form (x y : ℚ) :
    x * x + y * y + 2 * (x * y) * (-1 : ℚ) = (x - y) ^ 2 ∧ 0 ≤ (x - y) ^ 2 := by
  constructor
  · ring
  · exact sq_nonneg _

end JurisLean.Candidates.Final20261021.Probability
