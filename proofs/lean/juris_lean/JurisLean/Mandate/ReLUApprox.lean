import Mathlib

/-!
# Mandate module — a two-layer ReLU network with a stability constant it computes

The audit's judgement on the certified-approximator mandate item (R-07) was that the
existing carrier, `Mandate/DerivedCertificate.lean`, bounds the error of an iterated
*rational linear contraction*. That is not a network. A first attempt was built on
`abs_add` and a division-rewriting lemma that do not exist under those names in the
pinned toolchain, and the compiler rejected it in run 36336037802 (subject `be08e5d`);
the failure text is booked in `docs/master-plan/03_证明战役台账.md`.

This is the second attempt, built only out of what already elaborates green elsewhere in
this package: `max_eq_left` / `max_eq_right` on `max x 0`, `by_cases h : 0 ≤ a` for the
sign split, `linarith` for the linear part, and `norm_num` for every numeric fact. Two
rules were set from that failure and are followed here: no Mathlib name is used that is
not already in green use in this repository, and no rational is computed by hand.

The result is stated two-sided rather than with `|·|`, which is what keeps every step
inside linear arithmetic: if each input coordinate moves by at most `E`, the output moves
by at most `lip · E`, where `lip` is read off the weight rows.

What is deliberately NOT claimed:
* Universal approximation, or any density statement about networks.
* A *least* Lipschitz constant. `lip` adds absolute weights row by row and is not
  optimised; the claim is computable, not tight.
* Width or depth generality: two inputs, two hidden units, one output unit. The argument
  repeats, but no `Fin n` or `Matrix` machinery is claimed here.
* Anything about legal outcomes. This is the approximator carrier's arithmetic.

Status: awaiting its first CI elaboration. Nothing here is attested until a round builds it.
-/

namespace JurisLean.Mandate.ReLUApprox

/-! ## The network -/

/-- ReLU, as `max x 0`, so the sign split uses the `max` lemmas this package already
relies on. -/
def relu : ℚ → ℚ := fun x => max x 0

/-- First hidden unit: weights `1` and `-1`, bias `1`. -/
def h1 (x : ℚ × ℚ) : ℚ := relu (x.1 - x.2 + 1)

/-- Second hidden unit: weights `-1` and `3`, bias `2`. -/
def h2 (x : ℚ × ℚ) : ℚ := relu (-x.1 + 3 * x.2 + 2)

/-- Output unit: ReLU applied to weights `2` and `1` over the hidden layer. -/
def out (x : ℚ × ℚ) : ℚ := relu (2 * h1 x + h2 x)

/-- The stability constant, read off the weight rows: the hidden units contribute `1+1`
and `1+3`, the output layer weights those by `2` and `1`. -/
def lip : ℚ := 2 * (1 + 1) + 1 * (1 + 3)

/-- The constant is positive, so the bound is not carried by a radius of `0`. -/
theorem lip_pos : 0 < lip := by norm_num [lip]

/-- The constant is `8`, checked rather than assumed: the bound comes out of the module's
own arithmetic. -/
theorem lip_eq : lip = 8 := by norm_num [lip]

/-! ## ReLU preserves a two-sided bound -/

/--
A ReLU unit cannot widen a two-sided bound on how far its argument moved. Four sign
cases: where both arguments are non-negative `relu` is the identity and the bound is the
hypothesis; where one is negative the unit clamps to `0` and the residual inequality is
linear arithmetic against `0 ≤ E`.
-/
theorem relu_between {a b E : ℚ} (hE : 0 ≤ E) (lo : -E ≤ a - b) (hi : a - b ≤ E) :
    -E ≤ relu a - relu b ∧ relu a - relu b ≤ E := by
  by_cases ha : 0 ≤ a
  · by_cases hb : 0 ≤ b
    · rw [show relu a = a from max_eq_left ha, show relu b = b from max_eq_left hb]
      exact ⟨lo, hi⟩
    · have hb0 : b ≤ 0 := le_of_lt (lt_of_not_ge hb)
      rw [show relu a = a from max_eq_left ha, show relu b = 0 from max_eq_right hb0]
      exact ⟨by linarith, by linarith⟩
  · have ha0 : a ≤ 0 := le_of_lt (lt_of_not_ge ha)
    by_cases hb : 0 ≤ b
    · rw [show relu a = 0 from max_eq_right ha0, show relu b = b from max_eq_left hb]
      exact ⟨by linarith, by linarith⟩
    · have hb0 : b ≤ 0 := le_of_lt (lt_of_not_ge hb)
      rw [show relu a = 0 from max_eq_right ha0, show relu b = 0 from max_eq_right hb0]
      exact ⟨by linarith, by linarith⟩

/-! ## Layer by layer -/

/-- The first hidden unit moves by at most `2 · E`: its weight row is `1`, `-1`. -/
theorem h1_between {x y : ℚ × ℚ} {E : ℚ} (hE : 0 ≤ E)
    (lo₁ : -E ≤ x.1 - y.1) (hi₁ : x.1 - y.1 ≤ E)
    (lo₂ : -E ≤ x.2 - y.2) (hi₂ : x.2 - y.2 ≤ E) :
    -2 * E ≤ h1 x - h1 y ∧ h1 x - h1 y ≤ 2 * E := by
  refine relu_between (by linarith : 0 ≤ 2 * E)
    (by show -2 * E ≤ (x.1 - x.2 + 1) - (y.1 - y.2 + 1); linarith)
    (by show (x.1 - x.2 + 1) - (y.1 - y.2 + 1) ≤ 2 * E; linarith)

/-- The second hidden unit moves by at most `4 · E`: its weight row is `-1`, `3`. -/
theorem h2_between {x y : ℚ × ℚ} {E : ℚ} (hE : 0 ≤ E)
    (lo₁ : -E ≤ x.1 - y.1) (hi₁ : x.1 - y.1 ≤ E)
    (lo₂ : -E ≤ x.2 - y.2) (hi₂ : x.2 - y.2 ≤ E) :
    -4 * E ≤ h2 x - h2 y ∧ h2 x - h2 y ≤ 4 * E := by
  refine relu_between (by linarith : 0 ≤ 4 * E)
    (by show -4 * E ≤ (-x.1 + 3 * x.2 + 2) - (-y.1 + 3 * y.2 + 2); linarith)
    (by show (-x.1 + 3 * x.2 + 2) - (-y.1 + 3 * y.2 + 2) ≤ 4 * E; linarith)

/--
**The two-layer ReLU network is stable with the computed constant.** If each input
coordinate moves by at most `E`, the output moves by at most `lip · E`. Nothing is handed
in by a caller: `lip` is the row arithmetic above and the hidden units enter only through
`h1_between` and `h2_between`.
-/
theorem out_stable {x y : ℚ × ℚ} {E : ℚ} (hE : 0 ≤ E)
    (lo₁ : -E ≤ x.1 - y.1) (hi₁ : x.1 - y.1 ≤ E)
    (lo₂ : -E ≤ x.2 - y.2) (hi₂ : x.2 - y.2 ≤ E) :
    -lip * E ≤ out x - out y ∧ out x - out y ≤ lip * E := by
  obtain ⟨hlo₁, hhi₁⟩ := h1_between hE lo₁ hi₁ lo₂ hi₂
  obtain ⟨hlo₂, hhi₂⟩ := h2_between hE lo₁ hi₁ lo₂ hi₂
  rw [lip_eq]
  refine relu_between (by linarith : 0 ≤ 8 * E)
    (by show -8 * E ≤ (2 * h1 x + h2 x) - (2 * h1 y + h2 y); linarith)
    (by show (2 * h1 x + h2 x) - (2 * h1 y + h2 y) ≤ 8 * E; linarith)

/-! ## The network is not a constant function -/

/-- Values at two points, computed by the checker rather than by hand, so the bound above
is a bound on a moving function. -/
theorem out_origin : out (0, 0) = 4 := by norm_num [out, h1, h2, relu]

/-- The other corner. -/
theorem out_at_one : out (1, 0) = 5 := by norm_num [out, h1, h2, relu]

/-- The network is not constant: a `lip = 0` claim would be false. -/
theorem out_not_constant : out (0, 0) ≠ out (1, 0) := by
  rw [out_origin, out_at_one]; norm_num

/-- Zero radius means equal inputs mean equal outputs: the degenerate end of the
stability bound, which is what keeps a sign error in it from passing. -/
theorem out_eq_of_zero_radius {x y : ℚ × ℚ} (h : x.1 = y.1) (h' : x.2 = y.2) :
    out x = out y := by
  have key := out_stable (by norm_num : (0 : ℚ) ≤ 0)
    (by rw [h]; exact neg_zero.le) (by rw [h]; exact le_refl _)
    (by rw [h']; exact neg_zero.le) (by rw [h']; exact le_refl _)
  rw [mul_zero] at key
  exact le_antisymm (sub_nonpos.mp key.2) (sub_nonneg.mp key.1)

end JurisLean.Mandate.ReLUApprox
