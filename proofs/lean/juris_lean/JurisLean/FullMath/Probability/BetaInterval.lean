import JurisLean.FullMath.Core.Foundations

/-!
P10 — Latent win-rate confidence interval. For integer Beta parameters
the regularized incomplete beta has an exact rational form (upper binomial
tail), so endpoint brackets are exact; a mixture of such components then
holds posterior mass at least `1 − δ` by convexity whenever each retained
component does.
-/

namespace JurisLean.FullMath.Probability

/-- Exact Beta CDF for integer parameters: the upper binomial tail identity
`I_x(a, b) = Σ_{j≥a} C(a+b−1, j) x^j (1−x)^(a+b−1−j)`. -/
def betaCDF (a b : ℕ) (x : ℚ) : ℚ :=
  Finset.sum Finset.univ (fun j : Fin (a + b) =>
    if (a : ℕ) ≤ j.val then
      ((Nat.choose (a + b - 1) j.val : ℕ) : ℚ) * x ^ j.val * (1 - x) ^ (a + b - 1 - j.val)
    else 0)

/-- P10(a): at zero mass the exact CDF vanishes (for `a ≥ 1`). -/
theorem betaCDF_zero (a b : ℕ) (ha : 0 < a) : betaCDF a b 0 = 0 := by
  refine Finset.sum_eq_zero (fun j _ => ?_)
  by_cases hja : a ≤ j.val
  · have hj1 : j.val ≠ 0 := by omega
    rw [if_pos hja, zero_pow hj1]
    ring
  · rw [if_neg hja]

/-- P10(b): at full mass the exact CDF equals one (for `a, b ≥ 1`): only
the top binomial term survives. -/
theorem betaCDF_one (a b : ℕ) (ha : 0 < a) (hb : 0 < b) : betaCDF a b 1 = 1 := by
  have hmem : (⟨a + b - 1, by omega⟩ : Fin (a + b)) ∈ Finset.univ := Finset.mem_univ _
  refine Finset.sum_eq_single (⟨a + b - 1, by omega⟩ : Fin (a + b))
    (fun j _ _ => ?_) hmem
  · by_cases hja : a ≤ j.val
    · rw [if_pos hja]
      have hpos : a + b - 1 - j.val ≠ 0 := by omega
      rw [sub_self, zero_pow hpos, mul_zero]
    · rw [if_neg hja]
  · rw [if_pos (by omega : a ≤ a + b - 1)]
    have hch : Nat.choose (a + b - 1) (a + b - 1) = 1 := Nat.choose_self _
    rw [hch]
    norm_num

/-- Interval mass from the exact CDF. -/
def betaMass (a b : ℕ) (l u : ℚ) : ℚ := betaCDF a b u - betaCDF a b l

/-- P10(c): total interval mass is exactly one — endpoint brackets are
exact, not asymptotic. -/
theorem beta_mass_total_one (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    betaMass a b 0 1 = 1 := by
  simp only [betaMass, betaCDF_one a b ha hb, betaCDF_zero a b ha]
  ring

/-- P10(d): a two-model mixture's interval mass is the convex combination
of component masses; if every retained component bracket gives at least
`1 − δ`, the mixture does too — exact CDF brackets compose. -/
theorem beta_mixture_mass (a1 b1 a2 b2 : ℕ) (w delta : ℚ) (l u : ℚ)
    (hw : 0 ≤ w) (hw1 : w ≤ 1)
    (h1 : 1 - delta ≤ betaMass a1 b1 l u)
    (h2 : 1 - delta ≤ betaMass a2 b2 l u) :
    1 - delta ≤ w * betaMass a1 b1 l u + (1 - w) * betaMass a2 b2 l u := by
  nlinarith [hw, hw1, h1, h2]

end JurisLean.FullMath.Probability
