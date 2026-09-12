import JurisLean.FullMath.Core.Foundations

/-!
P11 — Brier score separation.

For a Bernoulli outcome `Y` with success probability `p`, the expected
Brier excess of forecast `q` over the calibrated forecast `p` is exactly
`(q − p)²`: `E[(q−Y)²] − E[(p−Y)²] = (q−p)²`, with equality iff `q = p`.
Sample scores do not thereby prove calibration — that distinction is kept
in the E01 contract module.
-/

namespace JurisLean.FullMath.Probability

/-- Expectation under `P(Y = 1) = p` over `Bool`. -/
def expBern (p : ℝ) (f : Bool → ℝ) : ℝ :=
  (1 - p) * f false + p * f true

/-- P11(a): the two-point expansion identity. -/
theorem brier_excess_identity (p q : ℝ) :
    expBern p (fun y => (q - (if y then 1 else 0)) ^ 2) -
    expBern p (fun y => (p - (if y then 1 else 0)) ^ 2) = (q - p) ^ 2 := by
  simp only [expBern]
  ring

/-- P11(b): equality of expected Brier scores holds iff the forecasts agree. -/
theorem brier_excess_zero_iff (p q : ℝ) :
    expBern p (fun y => (q - (if y then 1 else 0)) ^ 2) -
    expBern p (fun y => (p - (if y then 1 else 0)) ^ 2) = 0 ↔ q = p := by
  rw [brier_excess_identity]
  constructor
  · intro h
    exact (pow_eq_zero_iff two_ne_zero).mp h
  · intro h
    rw [h, sub_self, sq_zero]

end JurisLean.FullMath.Probability
