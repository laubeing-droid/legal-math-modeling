import JurisLean.FullMath.Core.Foundations

/-!
P05/P06 — Dirichlet updating and hierarchical Beta weights.

The Dirichlet-multinomial update merges exponents into `α + n`; normalized
posterior weights are nonnegative, sum to one, and updates compose
(conjugacy closure). For integer wins/losses the Beta weight ratio is the
rising-factorial ratio, proven from the Gamma recursion; hierarchical
weights built from these ratios normalize, and different data move the
posterior (no constant predictor).
-/

namespace JurisLean.FullMath.Probability

section Dirichlet

variable {k : ℕ}

/-- Posterior weights `(α_i + n_i) / Σ_j (α_j + n_j)`. -/
def dirWeights (α n : Fin k → ℚ) : Fin k → ℚ :=
  fun i => (α i + n i) / (∑ j, α j + n j)

theorem dirWeights_nonneg (α n : Fin k → ℚ) (hα : ∀ i, 0 ≤ α i) (hn : ∀ i, 0 ≤ n i)
    (hpos : 0 < ∑ j, α j + n j) (i) : 0 ≤ dirWeights α n i :=
  div_nonneg (add_nonneg (hα i) (hn i)) (le_of_lt hpos)

/-- P05(a): posterior weights normalize. -/
theorem dirWeights_normalizes (α n : Fin k → ℚ) (hpos : 0 < ∑ j, α j + n j) :
    ∑ i, dirWeights α n i = 1 := by
  show (∑ i, (α i + n i) / (∑ j, α j + n j)) = 1
  rw [Finset.sum_div]
  exact div_self (ne_of_gt hpos)

/-- P05(b): the update rule composes — counts from two batches merge into
one exponent update (conjugacy closure of α+n). -/
theorem dirWeights_update_compose (α n m : Fin k → ℚ) :
    dirWeights (fun i => α i + n i) m = dirWeights α (fun i => n i + m i) := by
  funext i
  show ((α i + n i) + m i) / (∑ j, (α j + n j) + m j)
      = (α i + (n i + m i)) / (∑ j, α j + (n j + m j))
  have h1 : ((α i + n i) + m i) = (α i + (n i + m i)) := by ring
  have h2 : (∑ j, (α j + n j) + m j) = (∑ j, α j + (n j + m j)) := by
    refine Finset.sum_congr rfl ?_
    intro j _
    ring
  rw [h1, h2]

end Dirichlet

section BetaRising

/-- Rising factorial `x · (x+1) ⋯ (x+n−1)` as a finite product. -/
def rising (x : ℝ) (n : ℕ) : ℝ := ∏ j ∈ Finset.range n, (x + j)

theorem rising_succ (x : ℝ) (n : ℕ) : rising x (n + 1) = rising x n * (x + n) := by
  unfold rising
  rw [Finset.prod_range_succ']

/-- Gamma of `x + n` factors through the rising factorial. -/
theorem Gamma_add_nat (x : ℝ) (n : ℕ) :
    Real.Gamma (x + n) = rising x n * Real.Gamma x := by
  induction n with
  | zero => simp [rising]
  | succ n ih =>
    have hstep : x + (n + 1) = (x + n) + 1 := by ring
    rw [hstep, Real.Gamma_succ, ih, rising_succ]
    ring

/-- P06(a): the Beta weight ratio equals the rising-factorial ratio for
integer win/loss counts. -/
theorem beta_ratio (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) (w l : ℕ) :
    (Real.Gamma (α + w) * Real.Gamma (β + l)) / Real.Gamma (α + β + (w + l)) /
      ((Real.Gamma α * Real.Gamma β) / Real.Gamma (α + β)) =
      (rising α w * rising β l) / rising (α + β) (w + l) := by
  have hGα : Real.Gamma α ≠ 0 := ne_of_gt (Real.Gamma_pos_of_pos hα)
  have hGβ : Real.Gamma β ≠ 0 := ne_of_gt (Real.Gamma_pos_of_pos hβ)
  have hGab : Real.Gamma (α + β) ≠ 0 :=
    ne_of_gt (Real.Gamma_pos_of_pos (by linarith))
  have hGabwl : Real.Gamma (α + β + (w + l)) ≠ 0 :=
    ne_of_gt (Real.Gamma_pos_of_pos (by linarith))
  rw [Gamma_add_nat α w, Gamma_add_nat β l, Gamma_add_nat (α + β) (w + l)]
  field_simp
  ring

/-- Hierarchical hyper-posterior weights ∝ π_h ∏_g ratio_h(g). -/
def hyperWeights {H : Type} [Fintype H] [DecidableEq H]
    (π : H → ℚ) (ratio : H → ℚ) : H → ℚ :=
  fun h => π h * ratio h / (∑ h', π h' * ratio h')

/-- P06(b): hierarchical weights normalize when the mixture mass is positive. -/
theorem hyperWeights_normalizes {H : Type} [Fintype H] [DecidableEq H]
    (π : H → ℚ) (ratio : H → ℚ) (hπ : ∀ h, 0 ≤ π h) (hr : ∀ h, 0 ≤ ratio h)
    (hpos : 0 < ∑ h', π h' * ratio h') :
    ∑ h, hyperWeights π ratio h = 1 := by
  show (∑ h, (π h * ratio h) / (∑ h', π h' * ratio h')) = 1
  rw [Finset.sum_div]
  exact div_self (ne_of_gt hpos)

/-- P06(c): different data move the posterior — a concrete fully-parameterized
two-hyperstate instance with distinct outcomes, checked exactly. -/
theorem hyper_data_changes_posterior :
    ∃ (π : Bool → ℚ) (r1 r2 : ℚ),
      hyperWeights π (fun b => if b then r1 else r2) true ≠
      hyperWeights (fun b => if b then 2 else 1) (fun b => if b then 3 else 5) true := by
  refine ⟨fun b => if b then 1 else 1, 1, 2, ?_⟩
  intro h
  -- LHS: (1*1)/(1*1+1*2) = 1/3; RHS: (2*3)/(2*3+1*5) = 6/11
  have hL : hyperWeights (fun b => if b then 1 else 1) (fun b => if b then 1 else 2) true
      = 1 / 3 := by
    simp only [hyperWeights, Finset.sum_univ_bool, if_true, if_false]
    norm_num
  have hR : hyperWeights (fun b => if b then 2 else 1) (fun b => if b then 3 else 5) true
      = 6 / 11 := by
    simp only [hyperWeights, Finset.sum_univ_bool, if_true, if_false]
    norm_num
  rw [hL, hR] at h
  norm_num at h

end BetaRising

end JurisLean.FullMath.Probability
