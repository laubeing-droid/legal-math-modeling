import Mathlib

/-!
# Mandate module — a two-layer ReLU network with a stability constant it computes

The audit's judgement on the certified-approximator mandate item (R-07) was that the
existing carrier, `Mandate/DerivedCertificate.lean`, bounds the error of an iterated
*rational linear contraction*. That is not a network. Three earlier attempts were
rejected by CI, each for a different reason, and the diagnoses are on file in
`docs/master-plan/03_证明战役台账.md`: guessed lemma names plus hand arithmetic (run
36336037802), a `show` block placed in an argument position whose implicit arguments
were still metavariables (run 36338968515), and a named argument `(E := 2 * E)` whose
right-hand `E` was captured by `relu_between`'s own implicit binder of the same name
(run 36341001563).

This file is written against those three findings:

* every lemma name here already elaborates green elsewhere in this package --
  `max_eq_left`, `max_eq_right`, `lt_of_not_ge`, `le_of_lt`, `sub_nonpos`, `sub_nonneg`,
  `le_antisymm` -- with tactics `by_cases`, `linarith`, `norm_num`, `simp only`;
* notation: `-2 * E` parses as `(-2) * E`, which is defequable with
  `-(2 * E)` but not the shape `relu_between` produces, and unification is not
  defeq-tolerant (run 36343993012's three errors, all at column 31, said exactly this);
* no rational is computed by hand: `norm_num` discharges every numeric fact, including
  the two point values;
* `relu_between` is applied **positionally** with its radius fact hoisted into a named
  `have`, so nothing is unified against a metavariable and no binder name is reused.

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

Status: elaborated green in CI run 36344882459 (subject 1b6a8d6a9), whose release
certificate lists these nine declarations and whose axiom log names 559 targets with no
`sorryAx`. It is built by the audit surface, not imported by the release root: joining
the root is a separate step and is booked in `PENDING_CI_MODULES` until then. Later
commits do not inherit that verdict.
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
    -(2 * E) ≤ h1 x - h1 y ∧ h1 x - h1 y ≤ 2 * E := by
  have hE2 : 0 ≤ (2 : ℚ) * E := by linarith
  have arg : -(2 * E) ≤ (x.1 - x.2 + 1) - (y.1 - y.2 + 1) ∧
      (x.1 - x.2 + 1) - (y.1 - y.2 + 1) ≤ 2 * E := by
    constructor <;> linarith
  have key := relu_between hE2 arg.1 arg.2
  simp only [h1] at ⊢
  exact key

/-- The second hidden unit moves by at most `4 · E`: its weight row is `-1`, `3`. -/
theorem h2_between {x y : ℚ × ℚ} {E : ℚ} (hE : 0 ≤ E)
    (lo₁ : -E ≤ x.1 - y.1) (hi₁ : x.1 - y.1 ≤ E)
    (lo₂ : -E ≤ x.2 - y.2) (hi₂ : x.2 - y.2 ≤ E) :
    -(4 * E) ≤ h2 x - h2 y ∧ h2 x - h2 y ≤ 4 * E := by
  have hE4 : 0 ≤ (4 : ℚ) * E := by linarith
  have arg : -(4 * E) ≤ (-x.1 + 3 * x.2 + 2) - (-y.1 + 3 * y.2 + 2) ∧
      (-x.1 + 3 * x.2 + 2) - (-y.1 + 3 * y.2 + 2) ≤ 4 * E := by
    constructor <;> linarith
  have key := relu_between hE4 arg.1 arg.2
  simp only [h2] at ⊢
  exact key

/--
**The two-layer ReLU network is stable with the computed constant.** If each input
coordinate moves by at most `E`, the output moves by at most `lip · E`. Nothing is handed
in by a caller: `lip` is the row arithmetic above and the hidden units enter only through
`h1_between` and `h2_between`.
-/
theorem out_stable {x y : ℚ × ℚ} {E : ℚ} (hE : 0 ≤ E)
    (lo₁ : -E ≤ x.1 - y.1) (hi₁ : x.1 - y.1 ≤ E)
    (lo₂ : -E ≤ x.2 - y.2) (hi₂ : x.2 - y.2 ≤ E) :
    -(lip * E) ≤ out x - out y ∧ out x - out y ≤ lip * E := by
  obtain ⟨hlo₁, hhi₁⟩ := h1_between hE lo₁ hi₁ lo₂ hi₂
  obtain ⟨hlo₂, hhi₂⟩ := h2_between hE lo₁ hi₁ lo₂ hi₂
  rw [lip_eq]
  have hE8 : 0 ≤ (8 : ℚ) * E := by linarith
  have arg : -(8 * E) ≤ (2 * h1 x + h2 x) - (2 * h1 y + h2 y) ∧
      (2 * h1 x + h2 x) - (2 * h1 y + h2 y) ≤ 8 * E := by
    constructor <;> linarith
  have key := relu_between hE8 arg.1 arg.2
  simp only [out] at ⊢
  exact key

/-! ## The network is not a constant function -/

/-- Values at two points, computed by the checker rather than by hand, so the bound above
is a bound on a moving function. -/
theorem out_origin : out (0, 0) = 4 := by norm_num [out, h1, h2, relu]

/-- The other corner. -/
theorem out_at_one : out (1, 0) = 5 := by norm_num [out, h1, h2, relu]

/-- The network is not constant: a `lip = 0` claim would be false. -/
theorem out_not_constant : out (0, 0) ≠ out (1, 0) := by
  rw [out_origin, out_at_one]; norm_num

end JurisLean.Mandate.ReLUApprox
