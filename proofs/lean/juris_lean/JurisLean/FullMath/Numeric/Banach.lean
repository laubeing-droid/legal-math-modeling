import JurisLean.FullMath.Core.Foundations

/-!
N07/N08 — Projected gradient iteration on a real interval.

For `K = [l, u]` nonempty, `a > 0`, the projected map
`T(x) = clip_K((1−ηa)x − ηb)` is a `k`-contraction with `k = |1−ηa|` (which
is `< 1` exactly when `0 < ηa < 2`); one-dimensional clipping is
nonexpansive; the explicit fixed point is `clip_K(−b/a)`; with per-step
error `≤ ε` the residual obeys `e_{n+1} ≤ k e_n + ε` and therefore stays at
`ε/(1−k) + kⁿ e₀`.
-/

namespace JurisLean.FullMath.Numeric

section Banach

/-- Clipping to a closed interval, branch definition. -/
def clip (l u x : ℝ) : ℝ := if x < l then l else if u < x then u else x

theorem clip_mem (l u x : ℝ) (h : l ≤ u) : l ≤ clip l u x ∧ clip l u x ≤ u := by
  unfold clip
  by_cases hx : x < l
  · rw [if_pos hx]
    exact ⟨le_refl l, h⟩
  · by_cases hxu : u < x
    · rw [if_neg hx, if_pos hxu]
      exact ⟨h, le_refl u⟩
    · rw [if_neg hx, if_neg hxu]
      exact ⟨by linarith, by linarith⟩

/-- N07(a): clipping is nonexpansive. -/
theorem clip_nonexpansive (l u x y : ℝ) (h : l ≤ u) :
    |clip l u x - clip l u y| ≤ |x - y| := by
  unfold clip
  split_ifs <;> rw [abs_le_abs_iff] <;> nlinarith

/-- The projected gradient map. -/
def T (l u a b η x : ℝ) : ℝ := clip l u ((1 - η * a) * x - η * b)

/-- N07(b): T is Lipschitz with factor `|1 − ηa|`. -/
theorem T_contraction (l u a b η x y : ℝ) (h : l ≤ u) :
    |T l u a b η x - T l u a b η y| ≤ |1 - η * a| * |x - y| := by
  have key := clip_nonexpansive l u ((1 - η * a) * x - η * b) ((1 - η * a) * y - η * b) h
  have hsub : ((1 - η * a) * x - η * b) - ((1 - η * a) * y - η * b) = (1 - η * a) * (x - y) := by
    ring
  rw [hsub] at key
  simpa [T, abs_mul] using key

/-- Interior fixed point: `−b/a` inside the interval stays fixed. -/
theorem T_fixed_interior (l u a b η : ℝ) (ha : 0 < a)
    (hlu : l ≤ -(b / a)) (hbu : -(b / a) ≤ u) :
    T l u a b η (-(b / a)) = -(b / a) := by
  have hval : (1 - η * a) * (-(b / a)) - η * b = -(b / a) := by
    field_simp
    ring
  show clip l u ((1 - η * a) * (-(b / a)) - η * b) = -(b / a)
  rw [hval]
  unfold clip
  rw [if_neg (by linarith), if_neg (by linarith)]

/-- Lower boundary: when `a·l + b > 0` the point `l` stays fixed. -/
theorem T_fixed_lower (l u a b η : ℝ) (ha : 0 < a) (hη : 0 < η) (hlu : l ≤ u)
    (hpos : 0 < a * l + b) : T l u a b η l = l := by
  have hkey : (1 - η * a) * l - η * b < l := by nlinarith [mul_pos hη hpos]
  show clip l u ((1 - η * a) * l - η * b) = l
  unfold clip
  rw [if_pos hkey]

/-- Upper boundary: when `a·u + b < 0` the point `u` stays fixed. -/
theorem T_fixed_upper (l u a b η : ℝ) (ha : 0 < a) (hη : 0 < η) (hlu : l ≤ u)
    (hneg : a * u + b < 0) : T l u a b η u = u := by
  have hnotlt : ¬ ((1 - η * a) * u - η * b < l) := by
    nlinarith [mul_pos hη (by linarith : (0 : ℝ) < a * u + b), hlu]
  have hkey : u < (1 - η * a) * u - η * b := by nlinarith [mul_neg hη hneg]
  show clip l u ((1 - η * a) * u - η * b) = u
  unfold clip
  rw [if_neg hnotlt, if_pos hkey]

/-- N07(c): the explicit fixed point of T is `clip_K(−b/a)`. -/
theorem T_fixed_point (l u a b η : ℝ) (hlu : l ≤ u) (ha : 0 < a) (hη : 0 < η) :
    T l u a b η (clip l u (-(b / a))) = clip l u (-(b / a)) := by
  have hnegdiv : -(b / a) = (-b) / a := neg_div b a
  rcases lt_or_le (-(b / a)) l with hlt | hge
  · have hpos : 0 < a * l + b := by
      rw [hnegdiv] at hlt
      have := (div_lt_iff ha).mp hlt
      linarith
    have hclipl : clip l u (-(b / a)) = l := by
      unfold clip
      rw [if_pos hlt]
    rw [hclipl, T_fixed_lower l u a b η ha hη hlu hpos]
  · rcases lt_or_le u (-(b / a)) with hug | hle
    · have hneg : a * u + b < 0 := by
        rw [hnegdiv] at hug
        have := (lt_div_iff ha).mp hug
        linarith
      have hclipu : clip l u (-(b / a)) = u := by
        unfold clip
        rw [if_neg (by linarith), if_pos hug]
      rw [hclipu, T_fixed_upper l u a b η ha hη hlu hneg]
    · have hclipi : clip l u (-(b / a)) = -(b / a) := by
        unfold clip
        rw [if_neg (by linarith), if_neg (by linarith)]
      rw [hclipi, T_fixed_interior l u a b η ha hge hle]

/-- N08: with per-step error `≤ ε`, the residual obeys
`e_{n+1} ≤ k e_n + ε` and stays at `ε/(1−k) + kⁿ e₀` for any `k < 1`. -/
theorem residual_error_bound (k e0 eps : ℝ) (hk1 : 0 ≤ k) (hk2 : k < 1)
    (step : ℕ → ℝ) (h0 : step 0 ≤ e0)
    (hrec : ∀ n, step (n + 1) ≤ k * step n + eps) :
    ∀ n, step n ≤ k ^ n * e0 + eps / (1 - k) := by
  intro n
  induction n with
  | zero =>
    rw [pow_zero, mul_one]
    linarith
  | succ n ih =>
    have h1 := hrec n
    have hden : 0 < 1 - k := by linarith
    have hsplit : k * (k ^ n * e0 + eps / (1 - k)) = k ^ (n + 1) * e0 + k * eps / (1 - k) := by
      rw [pow_succ]
      ring
    have hclose : k * eps / (1 - k) + eps = eps / (1 - k) := by
      field_simp
      ring
    calc step (n + 1) ≤ k * step n + eps := h1
      _ ≤ k * (k ^ n * e0 + eps / (1 - k)) + eps := by nlinarith
      _ = k ^ (n + 1) * e0 + (k * eps / (1 - k) + eps) := hsplit
      _ = k ^ (n + 1) * e0 + eps / (1 - k) := by rw [hclose]
      _ ≤ k ^ (n + 1) * e0 + eps / (1 - k) := le_refl _

end Banach

end JurisLean.FullMath.Numeric
