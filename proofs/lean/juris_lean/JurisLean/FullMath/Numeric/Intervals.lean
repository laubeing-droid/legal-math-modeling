import JurisLean.FullMath.Core.Foundations

/-!
N02 — Interval arithmetic soundness over the rationals.

Closed intervals with endpoint-ordered operations; inclusion for addition,
the four-endpoint rule for multiplication (the standard two-level
monotonicity argument), and reciprocals when zero is excluded from the
denominator. A span over seen candidates is a span of what was seen, never
automatically a global bound.
-/

namespace JurisLean.FullMath.Numeric

/-- A closed interval with ordered endpoints. -/
structure Iv where
  lo : ℚ
  hi : ℚ
  hle : lo ≤ hi

namespace Iv

/-- Membership. -/
def mem (x : ℚ) (i : Iv) : Prop := i.lo ≤ x ∧ x ≤ i.hi

/-- Addition. -/
def add (i j : Iv) : Iv where
  lo := i.lo + j.lo
  hi := i.hi + j.hi
  hle := by linarith [i.hle, j.hle]

/-- N02(a): addition is sound. -/
theorem add_sound (i j : Iv) (x y : ℚ) (hx : mem x i) (hy : mem y j) :
    mem (x + y) (add i j) := by
  constructor <;> linarith

/-- Multiplication: the four-endpoint rule. -/
def mul (i j : Iv) : Iv where
  lo := min (min (i.lo * j.lo) (i.lo * j.hi)) (min (i.hi * j.lo) (i.hi * j.hi))
  hi := max (max (i.lo * j.lo) (i.lo * j.hi)) (max (i.hi * j.lo) (i.hi * j.hi))
  hle := by
    calc min (min (i.lo * j.lo) (i.lo * j.hi)) (min (i.hi * j.lo) (i.hi * j.hi))
        ≤ min (i.lo * j.lo) (i.lo * j.hi) := min_le_left _ _
      _ ≤ i.lo * j.lo := min_le_left _ _
      _ ≤ max (i.lo * j.lo) (i.lo * j.hi) := le_max_left _ _
      _ ≤ max (max (i.lo * j.lo) (i.lo * j.hi)) (max (i.hi * j.lo) (i.hi * j.hi)) :=
          le_max_left _ _

/-- For fixed second factor `y`, products with `x ∈ i` lie between the two
endpoint products against `y` (monotonicity up to sign). -/
theorem fixed_y_bounds (i : Iv) (x y : ℚ) (hx : mem x i) :
    min (i.lo * y) (i.hi * y) ≤ x * y ∧ x * y ≤ max (i.lo * y) (i.hi * y) := by
  rcases le_total 0 y with hyn | hyn
  · constructor
    · calc min (i.lo * y) (i.hi * y) ≤ i.lo * y := min_le_left _ _
      _ ≤ x * y := mul_le_mul_of_nonneg_right hx.1 hyn
    · calc x * y ≤ i.hi * y := mul_le_mul_of_nonneg_right hx.2 hyn
      _ ≤ max (i.lo * y) (i.hi * y) := le_max_right _ _
  · constructor
    · have key : (-y) * i.hi ≤ (-y) * x := mul_le_mul_of_nonneg_left hx.2 (by linarith)
      ring_nf at key
      calc min (i.lo * y) (i.hi * y) ≤ i.hi * y := min_le_right _ _
      _ ≤ x * y := by linarith
    · have key : (-y) * i.lo ≤ (-y) * x := mul_le_mul_of_nonneg_left hx.1 (by linarith)
      ring_nf at key
      calc x * y ≤ i.lo * y := by linarith
      _ ≤ max (i.lo * y) (i.hi * y) := le_max_left _ _

/-- For fixed first factor `a`, products with `y ∈ j` lie between the two
endpoint products with `a`. -/
theorem fixed_x_bounds (j : Iv) (a y : ℚ) (hy : mem y j) :
    min (a * j.lo) (a * j.hi) ≤ a * y ∧ a * y ≤ max (a * j.lo) (a * j.hi) := by
  rcases le_total 0 a with han | han
  · constructor
    · calc min (a * j.lo) (a * j.hi) ≤ a * j.lo := min_le_left _ _
      _ ≤ a * y := mul_le_mul_of_nonneg_left hy.1 han
    · calc a * y ≤ a * j.hi := mul_le_mul_of_nonneg_left hy.2 han
      _ ≤ max (a * j.lo) (a * j.hi) := le_max_right _ _
  · constructor
    · have key : j.hi * (-a) ≤ y * (-a) := mul_le_mul_of_nonneg_right hy.2 (by linarith)
      ring_nf at key
      calc min (a * j.lo) (a * j.hi) ≤ a * j.hi := min_le_right _ _
      _ ≤ a * y := by linarith
    · have key : j.lo * (-a) ≤ y * (-a) := mul_le_mul_of_nonneg_right hy.1 (by linarith)
      ring_nf at key
      calc a * y ≤ a * j.lo := by linarith
      _ ≤ max (a * j.lo) (a * j.hi) := le_max_left _ _

/-- N02(b): the four-endpoint multiplication contains every product. -/
theorem mul_sound (i j : Iv) (x y : ℚ) (hx : mem x i) (hy : mem y j) :
    mem (x * y) (mul i j) := by
  obtain ⟨hlo1, hhi1⟩ := fixed_y_bounds i x y hx
  obtain ⟨hlo2, hhi2⟩ := fixed_x_bounds j i.lo y hy
  obtain ⟨hlo3, hhi3⟩ := fixed_x_bounds j i.hi y hy
  constructor
  · calc min (min (i.lo * j.lo) (i.lo * j.hi)) (min (i.hi * j.lo) (i.hi * j.hi))
        ≤ min (i.lo * y) (i.hi * y) := min_le_min hlo2 hlo3
    _ ≤ x * y := hlo1
  · calc x * y ≤ max (i.lo * y) (i.hi * y) := hhi1
    _ ≤ max (max (i.lo * j.lo) (i.lo * j.hi)) (max (i.hi * j.lo) (i.hi * j.hi)) := by
        refine max_le ?_ ?_
        · calc i.lo * y ≤ max (i.lo * j.lo) (i.lo * j.hi) := hhi2
          _ ≤ max (max (i.lo * j.lo) (i.lo * j.hi)) (max (i.hi * j.lo) (i.hi * j.hi)) :=
              le_max_left _ _
        · calc i.hi * y ≤ max (i.hi * j.lo) (i.hi * j.hi) := hhi3
          _ ≤ max (max (i.lo * j.lo) (i.lo * j.hi)) (max (i.hi * j.lo) (i.hi * j.hi)) :=
              le_max_right _ _

/-! Reciprocals with zero excluded from the denominator. -/

/-- Reciprocal order, positive denominators. -/
theorem one_div_le_one_div_pos {a b : ℚ} (ha : 0 < a) (hab : a ≤ b) :
    1 / b ≤ 1 / a := one_div_le_one_div_of_le ha hab

/-- Reciprocal order, negative denominators. -/
theorem one_div_le_one_div_neg {a b : ℚ} (hb : b < 0) (hab : a ≤ b) :
    1 / b ≤ 1 / a := by
  have h1 : 1 / (-a) ≤ 1 / (-b) := one_div_le_one_div_of_le (by linarith) (by linarith)
  rw [one_div_neg_eq_neg_one_div, one_div_neg_eq_neg_one_div] at h1
  linarith

/-- The reciprocal interval of a zero-free interval. -/
def recip (j : Iv) (hz : 0 < j.lo ∨ j.hi < 0) : Iv where
  lo := 1 / j.hi
  hi := 1 / j.lo
  hle := by
    rcases hz with hp | hp
    · exact one_div_le_one_div_pos hp j.hle
    · exact one_div_le_one_div_neg hp j.hle

/-- N02(c): reciprocation is sound for zero-free denominators. -/
theorem recip_sound (j : Iv) (hz : 0 < j.lo ∨ j.hi < 0) (y : ℚ) (hy : mem y j) :
    mem (1 / y) (recip j hz) := by
  rcases hz with hp | hp
  · have hypos : 0 < y := lt_of_lt_of_le hp hy.1
    exact ⟨one_div_le_one_div_pos hypos hy.2, one_div_le_one_div_pos hp hy.1⟩
  · have hyneg : y < 0 := lt_of_le_of_lt hy.2 hp
    exact ⟨one_div_le_one_div_neg hp hy.2, one_div_le_one_div_neg hyneg hy.1⟩

end Iv

/-- N02(d): an honest concrete witness that a seen-span need not be a global
bound — the span {20, 30} excludes 0 and 100 of the declared domain. -/
theorem seen_span_not_global_bound :
    ¬ ∀ d ∈ [0, 20, 30, 100], Iv.mem d ⟨20, 30, by norm_num⟩ := by
  intro h
  have h0 := h 0 (by norm_num)
  norm_num at h0

end JurisLean.FullMath.Numeric
