import JurisLean.FullMath.Core.Foundations

/-!
N04 — Convexity: PSD quadratic forms and one-dimensional KKT sufficiency.

A diagonal-nonnegative quadratic form is PSD in the LDLᵀ-reduced
coordinates (the reduction itself is a rational factorization step); a
one-dimensional strictly-convex objective with a nonnegativity constraint
satisfies the KKT sufficiency theorem with explicit multipliers.
-/

namespace JurisLean.FullMath.Numeric

/-! PSD in reduced coordinates. -/

/-- Quadratic form with nonnegative diagonal in the reduced basis. -/
def reducedForm (d x : Fin n → ℚ) : ℚ := ∑ i, d i * x i * x i

/-- Nonnegativity of each term `d i * x i * x i`. -/
theorem term_nonneg (d : Fin n → ℚ) (x : Fin n → ℚ) (i : Fin n) (hd : 0 ≤ d i) :
    0 ≤ d i * x i * x i := by
  nlinarith [sq_nonneg (x i), hd]

/-- N04(a): the reduced form is nonnegative when the diagonal is. -/
theorem reduced_nonneg {n : ℕ} (d x : Fin n → ℚ) (hd : ∀ i, 0 ≤ d i) :
    0 ≤ reducedForm d x :=
  Finset.sum_nonneg (fun i _ => term_nonneg d x i (hd i))

/-! One-dimensional KKT sufficiency. -/

/-- The objective `f(x) = h/2 x² + g x`. -/
def quad1 (h g x : ℚ) : ℚ := h / 2 * x * x + g * x

/-- Subgradient lower bound for `h ≥ 0` (convexity). -/
theorem quad1_convex_bound (h g x y : ℚ) (hh : 0 ≤ h) :
    quad1 h g x - quad1 h g y - (h * y + g) * (x - y) = h / 2 * (x - y) * (x - y) := by
  unfold quad1
  field_simp
  ring

/-- N04(b): for `h ≥ 0` the quadratic objective lies above every tangent. -/
theorem quad1_convex (h g x y : ℚ) (hh : 0 ≤ h) :
    quad1 h g y + (h * y + g) * (x - y) ≤ quad1 h g x := by
  have key := quad1_convex_bound h g x y hh
  have hnn : 0 ≤ h / 2 * (x - y) * (x - y) := by
    have h2 : 0 ≤ h / 2 := div_nonneg hh (by norm_num)
    nlinarith [h2, sq_nonneg (x - y)]
  linarith [key, hnn]

/-- KKT certificate in one dimension with constraint `x ≥ l`. -/
structure KKT1 where
  h : ℚ
  g : ℚ
  l : ℚ
  hh : 0 ≤ h
  xstar : ℚ
  hlb : l ≤ xstar
  mu : ℚ
  hmu : 0 ≤ mu
  hstation : h * xstar + g - mu = 0
  hcompl : mu * (xstar - l) = 0

/-- N04(c): a verified KKT certificate makes the point globally optimal over
`[l, ∞)`. -/
theorem kkt1_sufficient (k : KKT1) :
    ∀ x, k.l ≤ x → quad1 k.h k.g k.xstar ≤ quad1 k.h k.g x := by
  intro x hxl
  have hbase := quad1_convex k.h k.g x k.xstar k.hh
  -- quad1(xstar) + (h*xstar + g)(x − xstar) ≤ quad1(x)
  have hstation : k.h * k.xstar + k.g = k.mu := by linarith [k.hstation]
  rw [hstation] at hbase
  -- quad1(xstar) + mu(x − xstar) ≤ quad1(x)
  by_cases hcase : k.xstar = k.l
  · -- xstar = l: mu (x − xstar) = mu (x − l) ≥ 0 since x ≥ l
    subst hcase
    have hmu1 : 0 ≤ k.mu * (x - k.l) := mul_nonneg k.hmu (by linarith)
    have := k.hcompl
    have hbase' : quad1 k.h k.g k.l + k.mu * (x - k.l) ≤ quad1 k.h k.g x := hbase
    linarith
  · -- xstar > l: complementary slackness forces mu = 0
    have hgt : k.l < k.xstar := by
      rcases lt_or_eq_of_le k.hlb with hlt | rfl
      · exact hlt
      · exact absurd rfl hcase
    have hmu0 : k.mu = 0 := by
      by_contra hne
      have hpos : 0 < k.mu := by
        rcases lt_or_le 0 k.mu with h | h
        · exact h
        · exact absurd (le_antisymm k.hmu h) (by linarith)
      have : k.mu * (k.xstar - k.l) ≠ 0 := by
        intro hzero
        have := mul_eq_zero.mp hzero
        rcases this with h | h
        · exact hne h
        · linarith
      exact absurd k.hcompl this
    subst hmu0
    have : (0 : ℚ) * (x - k.xstar) = 0 := by ring
    rw [this] at hbase
    linarith [hbase]

end JurisLean.FullMath.Numeric
