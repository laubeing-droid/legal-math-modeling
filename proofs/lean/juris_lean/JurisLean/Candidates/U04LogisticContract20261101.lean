import JurisLean.Candidates.Final20261021.Probability
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Strong
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.Sigmoid
import Mathlib.Topology.Order.Compact

/-!
Frozen topic04 L155: the actual binary logistic objective, its identification
boundary and the fully penalized finite-dimensional minimizer. The unpenalized
separation counterexample remains the existing Final20261021.Probability result.
This is a mathematical contract, not a numerical optimizer or a calibration claim.
-/

noncomputable section

open scoped BigOperators
open Set

namespace JurisLean.Candidates.U04LogisticContract20261101

abbrev Parameter (d : ℕ) := EuclideanSpace ℝ (Fin d)

variable {d n : ℕ}

def scoreMap (x : Fin d → ℚ) : Parameter d →ₗ[ℝ] ℝ where
  toFun β := ∑ j, (x j : ℝ) * β j
  map_add' β γ := by
    simp only [PiLp.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' c β := by
    simp only [PiLp.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    ring

def probability (x : Fin d → ℚ) (β : Parameter d) : ℝ :=
  Real.sigmoid (scoreMap x β)

theorem probability_strict_bounds (x : Fin d → ℚ) (β : Parameter d) :
    0 < probability x β ∧ probability x β < 1 :=
  ⟨Real.sigmoid_pos _, Real.sigmoid_lt_one _⟩

def softplus (z : ℝ) : ℝ := -Real.log (Real.sigmoid (-z))

theorem softplus_eq_log_one_add_exp (z : ℝ) :
    softplus z = Real.log (1 + Real.exp z) := by
  simp only [softplus, Real.sigmoid_def, neg_neg, Real.log_inv]

private theorem softplus_pos (z : ℝ) : 0 < softplus z := by
  rw [softplus_eq_log_one_add_exp]
  simpa only [neg_neg] using
    Final20261021.Probability.u04_3_unpenalized_intercept_positive (-z)

private theorem hasDerivAt_softplus (z : ℝ) :
    HasDerivAt softplus (Real.sigmoid z) z := by
  have hs : HasDerivAt (fun t : ℝ => Real.sigmoid (-t))
      (Real.sigmoid (-z) * (1 - Real.sigmoid (-z)) * (-1)) z :=
    (Real.hasDerivAt_sigmoid (-z)).comp z ((hasDerivAt_id z).neg)
  have hl := (hs.log (ne_of_gt (Real.sigmoid_pos (-z)))).neg
  apply hl.congr_deriv
  have hc :
      -(Real.sigmoid (-z) * (1 - Real.sigmoid (-z)) * (-1) / Real.sigmoid (-z)) =
        1 - Real.sigmoid (-z) := by
    field_simp [ne_of_gt (Real.sigmoid_pos (-z))] <;> ring
  rw [hc, Real.sigmoid_neg]
  ring

private theorem continuous_softplus : Continuous softplus :=
  continuous_iff_continuousAt.mpr fun z => (hasDerivAt_softplus z).continuousAt

private theorem strictConvexOn_softplus : StrictConvexOn ℝ univ softplus := by
  apply strictConvexOn_of_deriv2_pos convex_univ continuous_softplus.continuousOn
  intro z hz
  change 0 < deriv (deriv softplus) z
  have hd : deriv softplus = Real.sigmoid :=
    funext fun t => (hasDerivAt_softplus t).deriv
  rw [hd, Real.deriv_sigmoid]
  exact mul_pos (Real.sigmoid_pos z) (sub_pos.mpr (Real.sigmoid_lt_one z))

def signedScore (x : Fin d → ℚ) (y : Bool) : Parameter d →ₗ[ℝ] ℝ :=
  if y then -(scoreMap x) else scoreMap x

def loss (x : Fin d → ℚ) (y : Bool) (β : Parameter d) : ℝ :=
  softplus (signedScore x y β)

theorem loss_eq_cross_entropy (x : Fin d → ℚ) (y : Bool) (β : Parameter d) :
    loss x y β =
      -(if y then (1 : ℝ) else 0) * Real.log (probability x β) -
      (1 - (if y then (1 : ℝ) else 0)) * Real.log (1 - probability x β) := by
  cases y <;> simp [loss, signedScore, softplus, probability, Real.sigmoid_neg]

private theorem continuous_loss (x : Fin d → ℚ) (y : Bool) :
    Continuous (loss x y) :=
  continuous_softplus.comp (signedScore x y).continuous_of_finiteDimensional

private theorem convexOn_loss (x : Fin d → ℚ) (y : Bool) :
    ConvexOn ℝ univ (loss x y) := by
  simpa only [loss, Set.preimage_univ, Function.comp_def] using
    strictConvexOn_softplus.convexOn.comp_linearMap (signedScore x y)

def empiricalLoss (X : Fin n → Fin d → ℚ) (Y : Fin n → Bool)
    (β : Parameter d) : ℝ :=
  (n : ℝ)⁻¹ * ∑ i, loss (X i) (Y i) β

private theorem empiricalLoss_nonneg (X : Fin n → Fin d → ℚ)
    (Y : Fin n → Bool) (β : Parameter d) : 0 ≤ empiricalLoss X Y β := by
  apply mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg n))
  exact Finset.sum_nonneg fun i hi => le_of_lt (softplus_pos _)

private theorem continuous_empiricalLoss (X : Fin n → Fin d → ℚ)
    (Y : Fin n → Bool) : Continuous (empiricalLoss X Y) := by
  exact continuous_const.mul
    (continuous_finset_sum _ fun i hi => continuous_loss (X i) (Y i))

private theorem convexOn_empiricalLoss (X : Fin n → Fin d → ℚ)
    (Y : Fin n → Bool) : ConvexOn ℝ univ (empiricalLoss X Y) := by
  refine ⟨convex_univ, ?_⟩
  intro β hβ γ hγ a b ha hb hab
  have hsum :
      (∑ i, loss (X i) (Y i) (a • β + b • γ)) ≤
        ∑ i, (a * loss (X i) (Y i) β + b * loss (X i) (Y i) γ) := by
    apply Finset.sum_le_sum
    intro i hi
    simpa only [smul_eq_mul] using
      (convexOn_loss (X i) (Y i)).2 hβ hγ ha hb hab
  change (n : ℝ)⁻¹ * (∑ i, loss (X i) (Y i) (a • β + b • γ)) ≤
    a * ((n : ℝ)⁻¹ * ∑ i, loss (X i) (Y i) β) +
      b * ((n : ℝ)⁻¹ * ∑ i, loss (X i) (Y i) γ)
  calc
    _ ≤ (n : ℝ)⁻¹ *
        ∑ i, (a * loss (X i) (Y i) β + b * loss (X i) (Y i) γ) :=
      mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr (Nat.cast_nonneg n))
    _ = _ := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      ring

def objective (X : Fin n → Fin d → ℚ) (Y : Fin n → Bool)
    (reg : ℝ) (β : Parameter d) : ℝ :=
  empiricalLoss X Y β + reg / 2 * ‖β‖ ^ 2

private theorem continuous_objective (X : Fin n → Fin d → ℚ)
    (Y : Fin n → Bool) (reg : ℝ) : Continuous (objective X Y reg) :=
  (continuous_empiricalLoss X Y).add (continuous_const.mul (continuous_norm.pow 2))

private theorem strictConvexOn_objective (X : Fin n → Fin d → ℚ)
    (Y : Fin n → Bool) (reg : ℝ) (hreg : 0 < reg) :
    StrictConvexOn ℝ univ (objective X Y reg) := by
  have hs : StrongConvexOn univ reg (objective X Y reg) := by
    rw [strongConvexOn_iff_convex]
    simpa [objective] using convexOn_empiricalLoss X Y
  exact hs.strictConvexOn hreg

/-- The statement covers a nonempty finite sample and penalizes every free coordinate.
No design-rank assumption is needed for this positive full L2 penalty. -/
theorem fully_regularized_unique_minimum (X : Fin n → Fin d → ℚ)
    (Y : Fin n → Bool) (hn : 0 < n) (reg : ℝ) (hreg : 0 < reg) :
    ∃! β : Parameter d, IsMinOn (objective X Y reg) univ β := by
  let f := objective X Y reg
  have hf : Continuous f := continuous_objective X Y reg
  have hf0 : 0 ≤ f 0 := by
    simpa [f, objective] using empiricalLoss_nonneg X Y (0 : Parameter d)
  let R : ℝ := 2 * f 0 / reg + 1
  have hR : 1 ≤ R := by
    have hdiv : 0 ≤ 2 * f 0 / reg :=
      div_nonneg (mul_nonneg (by norm_num) hf0) (le_of_lt hreg)
    dsimp [R]
    linarith
  have h0 : (0 : Parameter d) ∈ Metric.closedBall 0 R := by
    change dist (0 : Parameter d) 0 ≤ R
    simpa using le_trans (by norm_num : (0 : ℝ) ≤ 1) hR
  obtain ⟨β, hβ, hmin⟩ :=
    (isCompact_closedBall (0 : Parameter d) R).exists_isMinOn ⟨0, h0⟩ hf.continuousOn
  have hregR : reg / 2 * R = f 0 + reg / 2 := by
    dsimp [R]
    field_simp [ne_of_gt hreg] <;> ring
  have hglobal : IsMinOn f univ β := by
    intro γ hγ
    by_cases hball : γ ∈ Metric.closedBall 0 R
    · exact hmin hball
    · have hnorm : R < ‖γ‖ := by
        have hnot : ¬ dist γ (0 : Parameter d) ≤ R := hball
        simpa only [dist_zero_right, not_le] using hnot
      have hone : 1 ≤ ‖γ‖ := le_trans hR (le_of_lt hnorm)
      have hsq : ‖γ‖ ≤ ‖γ‖ ^ 2 := by
        nlinarith [mul_nonneg (norm_nonneg γ) (sub_nonneg.mpr hone)]
      have hzero_le : f 0 ≤ reg / 2 * ‖γ‖ ^ 2 := by
        calc
          f 0 ≤ reg / 2 * R := by rw [hregR]; linarith
          _ ≤ reg / 2 * ‖γ‖ :=
            mul_le_mul_of_nonneg_left (le_of_lt hnorm) (le_of_lt (half_pos hreg))
          _ ≤ reg / 2 * ‖γ‖ ^ 2 :=
            mul_le_mul_of_nonneg_left hsq (le_of_lt (half_pos hreg))
      have hpenalty : reg / 2 * ‖γ‖ ^ 2 ≤ f γ := by
        have hfit := empiricalLoss_nonneg X Y γ
        dsimp [f, objective]
        linarith
      exact (hmin h0).trans (hzero_le.trans hpenalty)
  refine ⟨β, hglobal, ?_⟩
  intro γ hγ
  exact (strictConvexOn_objective X Y reg hreg).eq_of_isMinOn
    hγ hglobal (mem_univ γ) (mem_univ β)

/-- Identification of the full family uses rational coordinate vectors. -/
theorem full_family_identifiable (β γ : Parameter d)
    (h : ∀ x : Fin d → ℚ, probability x β = probability x γ) : β = γ := by
  classical
  ext i
  have hi := Real.sigmoid_injective (h (fun j => if j = i then 1 else 0))
  simpa [scoreMap, apply_ite, ite_mul, eq_comm] using hi

/-- For a fixed observed design, probability identification is exactly score-map
injectivity; it is not implied by regularizer uniqueness. -/
theorem sample_identifiability_iff (X : Fin n → Fin d → ℚ) :
    Function.Injective (fun β : Parameter d => fun i => probability (X i) β) ↔
      Function.Injective (fun β : Parameter d => fun i => scoreMap (X i) β) := by
  constructor
  · intro h β γ hs
    apply h
    funext i
    exact congrArg Real.sigmoid (congrFun hs i)
  · intro h β γ hp
    apply h
    funext i
    exact Real.sigmoid_injective (congrFun hp i)

/-- This is the exact old all-positive intercept loss, not another separation proof. -/
theorem positive_intercept_is_existing_loss (t : ℝ) :
    objective (fun _ : Fin 1 => fun _ : Fin 1 => (1 : ℚ))
      (fun _ : Fin 1 => true) 0 (WithLp.toLp 2 (fun _ : Fin 1 => t)) =
        Real.log (1 + Real.exp (-t)) := by
  simp [objective, empiricalLoss, loss, signedScore, scoreMap,
    softplus_eq_log_one_add_exp]

theorem unregularized_sample_has_no_minimum :
    ¬ ∃ β : Parameter 1,
      IsMinOn
        (objective (fun _ : Fin 1 => fun _ : Fin 1 => (1 : ℚ))
          (fun _ : Fin 1 => true) 0) univ β := by
  rintro ⟨β, hmin⟩
  have hle (s : ℝ) :
      Real.log (1 + Real.exp (-(β 0))) ≤ Real.log (1 + Real.exp (-s)) := by
    have hrep : β = WithLp.toLp 2 (fun _ : Fin 1 => β 0) := by
      ext i
      fin_cases i <;> rfl
    have hineq := hmin (mem_univ (WithLp.toLp 2 (fun _ : Fin 1 => s)))
    rw [hrep] at hineq
    simpa only [Set.mem_setOf_eq, positive_intercept_is_existing_loss] using hineq
  have himprove :=
    Final20261021.Probability.u04_3_unpenalized_intercept_improves
      (β 0) (β 0 + 1) (lt_add_one (β 0))
  exact (not_lt_of_ge (hle (β 0 + 1))) himprove

/-- On zero features every parameter predicts one half. A deployment with true
rate one is therefore not calibrated by any optimizer of this model. -/
theorem zero_feature_probability_not_one (β : Parameter d) :
    probability (fun _ : Fin d => (0 : ℚ)) β = (1 : ℝ) / 2 ∧
      probability (fun _ : Fin d => (0 : ℚ)) β ≠ 1 := by
  norm_num [probability, scoreMap, Real.sigmoid_zero]

end JurisLean.Candidates.U04LogisticContract20261101
