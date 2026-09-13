import JurisLean.FullMath.Core.Foundations

/-!
P07 — Model averaging: the predictive mixture is a convex combination of
the retained models' predictions, so it stays inside their bracket; the
Bayes update by the evidence marginal renormalizes the weights; and the
robust bracket survives the update (no retained model is silently
dropped).
-/

namespace JurisLean.FullMath.Probability

variable {m : ℕ}

/-- Predictive mixture with weights `ws` over model predictions `ps`. -/
def mix (ws ps : Fin m → ℚ) : ℚ :=
  Finset.sum Finset.univ (fun j : Fin m => ws j * ps j)

/-- P07(a): a normalized nonnegative mixture of retained predictions stays
within the retained models' bracket — the robust bound covers every
retained model, hence the average. -/
theorem mixture_within_retained (ws ps : Fin m → ℚ) (lo hi : ℚ)
    (hw : ∀ j, 0 ≤ ws j)
    (hw1 : Finset.sum Finset.univ (fun j : Fin m => ws j) = 1)
    (hlo : ∀ j, lo ≤ ps j) (hhi : ∀ j, ps j ≤ hi) :
    lo ≤ mix ws ps ∧ mix ws ps ≤ hi := by
  constructor
  · have h1 : Finset.sum Finset.univ (fun j : Fin m => ws j * lo)
        ≤ Finset.sum Finset.univ (fun j : Fin m => ws j * ps j) :=
      Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (hlo j) (hw j))
    rw [Finset.sum_mul, hw1, one_mul] at h1
    exact h1
  · have h2 : Finset.sum Finset.univ (fun j : Fin m => ws j * ps j)
        ≤ Finset.sum Finset.univ (fun j : Fin m => ws j * hi) :=
      Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (hhi j) (hw j))
    rw [Finset.sum_mul, hw1, one_mul] at h2
    exact h2

/-- The evidence marginal under likelihoods `Ls`. -/
def evid (ws Ls : Fin m → ℚ) : ℚ :=
  Finset.sum Finset.univ (fun j : Fin m => ws j * Ls j)

/-- P07(b): the Bayes model-averaging update divides each weight by the
evidence marginal; the updated weights are nonnegative and normalized. -/
theorem mixture_update_normalizes (ws Ls : Fin m → ℚ) (hw : ∀ j, 0 ≤ ws j)
    (hL : ∀ j, 0 ≤ Ls j) (hZ : 0 < evid ws Ls) :
    (0 : ℚ) ≤ Finset.sum Finset.univ
        (fun j : Fin m => ws j * Ls j / evid ws Ls) ∧
      Finset.sum Finset.univ
        (fun j : Fin m => ws j * Ls j / evid ws Ls) = 1 := by
  constructor
  · refine Finset.sum_nonneg (fun j _ => ?_)
    exact div_nonneg (mul_nonneg (hw j) (hL j)) (le_of_lt hZ)
  · have hsplit : Finset.sum Finset.univ
          (fun j : Fin m => ws j * Ls j / evid ws Ls)
        = Finset.sum Finset.univ (fun j : Fin m => ws j * Ls j) / evid ws Ls :=
      (Finset.sum_div Finset.univ
        (fun j : Fin m => ws j * Ls j) (evid ws Ls)).symm
    rw [hsplit, div_eq_one_iff_eq (ne_of_gt hZ)]
    rfl

/-- P07(c): after the update the mixture of any bracketed predictions is
still within the same bracket — the robust bound is update-stable. -/
theorem mixture_update_still_bracketed (ws Ls ps : Fin m → ℚ) (lo hi : ℚ)
    (hw : ∀ j, 0 ≤ ws j) (hL : ∀ j, 0 ≤ Ls j) (hZ : 0 < evid ws Ls)
    (hlo : ∀ j, lo ≤ ps j) (hhi : ∀ j, ps j ≤ hi) :
    lo ≤ Finset.sum Finset.univ
        (fun j : Fin m => ws j * Ls j / evid ws Ls * ps j) ∧
      Finset.sum Finset.univ
        (fun j : Fin m => ws j * Ls j / evid ws Ls * ps j) ≤ hi := by
  have key := mixture_update_normalizes ws Ls hw hL hZ
  have hw' : ∀ j, (0 : ℚ) ≤ ws j * Ls j / evid ws Ls := fun j =>
    div_nonneg (mul_nonneg (hw j) (hL j)) (le_of_lt hZ)
  have hsplit : Finset.sum Finset.univ
      (fun j : Fin m => ws j * Ls j / evid ws Ls * ps j)
    = Finset.sum Finset.univ
        (fun j : Fin m => (ws j * Ls j / evid ws Ls) * ps j) := rfl
  rw [hsplit]
  have step := mixture_within_retained
    (fun j => ws j * Ls j / evid ws Ls) ps lo hi hw' key.2 hlo hhi
  exact step

end JurisLean.FullMath.Probability
