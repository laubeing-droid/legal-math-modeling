import JurisLean.FullMath.Core.Foundations

/-!
P08 — Posterior misspecification outer bounds.

A contaminated posterior `P* = (1−ε)P + εQ` over an event with baseline
bounds `[l, u]` stays inside `[(1−ε)l, (1−ε)u + ε]`. Contamination and
conditioning do not commute: a concrete rational instance shows ε belonging
to the prior stage must be conditioned first, never reused raw.
-/

namespace JurisLean.FullMath.Probability

/-- P08(a): contamination bounds. -/
theorem contamination_bounds (eps p q l u : ℝ)
    (he0 : 0 ≤ eps) (he1 : eps ≤ 1)
    (hpl : l ≤ p) (hpu : p ≤ u) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    (1 - eps) * l ≤ (1 - eps) * p + eps * q ∧
    (1 - eps) * p + eps * q ≤ (1 - eps) * u + eps := by
  constructor <;> nlinarith

/-- The contaminated mixture. -/
def contaminate {α : Type} (eps : ℝ) (P Q : α → ℝ) : α → ℝ :=
  fun x => (1 - eps) * P x + eps * Q x

/-- P08(b): pointwise sandwich of the contaminated value. -/
theorem contaminate_bound {α : Type} (eps : ℝ) (P Q : α → ℝ) (x : α)
    (hP : (0 : ℝ) ≤ P x) (hPu : P x ≤ 1) (hQ : 0 ≤ Q x) (hQu : Q x ≤ 1)
    (he0 : 0 ≤ eps) (he1 : eps ≤ 1) :
    (1 - eps) * P x ≤ contaminate eps P Q x ∧
    contaminate eps P Q x ≤ (1 - eps) * 1 + eps := by
  constructor <;> nlinarith [he0, he1, hP, hPu, hQ, hQu]

/-- P08(c): contamination and conditioning do not commute — a fully
explicit rational instance on a three-point space with hypothesis `H = {a}`
and evidence `E = {a, b}`:

- clean prior `P`: `P(a) = 1/10, P(b) = 1/10, P(c) = 8/10`;
- contaminator `Q`: `Q(a) = 1/2, Q(b) = 0, Q(c) = 1/2`;
- `ε = 1/2`.

Conditioning first then contaminating gives
`(1−ε)·P(H|E) + ε·Q(H|E) = 3/4`, while contaminating first gives
`P*(H|E) = 6/7`. The two differ, so a prior-stage ε may never be reused
across conditioning. -/
theorem contaminate_condition_do_not_commute :
    ((1 - 1 / 2) * 1 / 2 + 1 / 2 * 1) ≠
      ((1 / 2 * 1 / 10 + 1 / 2 * 1 / 2) /
        (1 / 2 * (1 / 10 + 1 / 10) + 1 / 2 * (1 / 2 + 0))) := by
  norm_num

end JurisLean.FullMath.Probability
