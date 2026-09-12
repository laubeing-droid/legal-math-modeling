import JurisLean.FullMath.Core.Foundations

/-!
P10 — Unprocessed mass bounds.

With verified counts `a` (in favor), `b` (against), unprocessed upper mass
`u`, rejected/unknown mass `v` and total unprocessed bound `r`, the true
ratio is bracketed:

`a / (a + b + r) ≤ (a + u) / (a + b + u + v) ≤ (a + r) / (a + b + r)`.

The `a + b = 0` case is a separate degenerate branch, never hidden behind a
totalized division.
-/

namespace JurisLean.FullMath.Probability

/-- P10(a): the unprocessed-mass bracket, for positive verified mass and
total unprocessed mass `u + v ≤ r`. -/
theorem unprocessed_mass_bounds (a b u v r : ℚ)
    (ha : 0 < a) (hb : 0 ≤ b) (hu : 0 ≤ u) (hv : 0 ≤ v) (hr : 0 ≤ r)
    (huv : u + v ≤ r) :
    a / (a + b + r) ≤ (a + u) / (a + b + u + v) ∧
    (a + u) / (a + b + u + v) ≤ (a + r) / (a + b + r) := by
  have hur : u ≤ r := by nlinarith
  have hvr : v ≤ r := by nlinarith
  have hden1 : 0 < a + b + r := by positivity
  have hden2 : 0 < a + b + u + v := by positivity
  constructor
  · rw [div_le_div_iff hden1 hden2]
    have h1 : a * v ≤ a * r := mul_le_mul_of_nonneg_left hvr (le_of_lt ha)
    nlinarith [h1, mul_nonneg hu hb, mul_nonneg hu hr]
  · rw [div_le_div_iff hden2 hden1]
    have h2 : u * b ≤ r * b := mul_le_mul_of_nonneg_right hur hb
    nlinarith [h2, mul_nonneg hr v]

/-- P10(b): the zero-verified-mass case is degenerate — no positive lower
bound is possible, stated as a concrete instance with all mass unprocessed. -/
theorem unprocessed_mass_degenerate (u v : ℚ) (hu : 0 < u) (hv : 0 < v) :
    (0 + u) / (0 + 0 + u + v) < 1 ∧ 0 < (0 + u) / (0 + 0 + u + v) := by
  have hden : 0 < 0 + 0 + u + v := by positivity
  constructor
  · rw [div_lt_one hden]
    nlinarith
  · exact div_pos hu hden

end JurisLean.FullMath.Probability
