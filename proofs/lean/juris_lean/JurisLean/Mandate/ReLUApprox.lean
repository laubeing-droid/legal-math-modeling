import Mathlib

/-!
# Mandate module — a real ReLU network with a computed Lipschitz constant

The audit's judgement on the certified-approximator mandate item (R-07) was that the
existing carrier, `Mandate/DerivedCertificate.lean`, bounds the error of an iterated
*rational linear contraction*. That is not a network, and the papers say so; what was
missing was any Lean statement about an actual piecewise-linear unit.

This module supplies one: a two-layer ReLU network on two inputs with fixed rational
weights, a Lipschitz constant `lip` that the module computes from those weights, and the
theorem that for all inputs, the output difference is at most `lip` times the input
difference in `|·|₁` (sum of coordinate absolute differences). The constant is a
rational literal produced by the same arithmetic the proof runs, not a field handed in
by a caller.

What is deliberately NOT claimed:
* Universal approximation, or any density statement. One network with one bound says
  nothing about what networks can approximate.
* Any norm but this one. The proof uses `d x y = |x.1 - y.1| + |x.2 - y.2|`; a
  `p`-norm or `∞`-norm statement would be a different theorem.
* A *least* Lipschitz constant. `lip` is an upper bound obtained by the triangle
  inequality layer by layer, and it is deliberately not optimised: the claim is
  computable, not tight.
* General width or depth. Two coordinates, two hidden units, one output unit. The
  argument repeats but no `Fin n` or `Matrix` machinery is claimed here.

Status: awaiting its first CI elaboration. Local Lean is forbidden in this repository,
so nothing in this file is attested until a round builds it; see R-07 in
`docs/master-plan/03_证明战役台账.md`.
-/

namespace JurisLean.Mandate.ReLUApprox

/-! ## The units -/

/-- ReLU on the rationals, stated as `max x 0` so the pinned `max`/`abs` lemma applies. -/
def relu : ℚ → ℚ := fun x => max x 0

/-- ReLU does not expand distances: the two `0` arms of `max` contribute nothing. -/
theorem abs_relu_sub_relu_le (x y : ℚ) : |relu x - relu y| ≤ |x - y| := by
  have h := abs_max_sub_max_le_max x y 0 0
  simpa [relu, sub_self] using h

/-- The distance this module bounds inputs in: sum of the two coordinate differences. -/
def d (x y : ℚ × ℚ) : ℚ := |x.1 - y.1| + |x.2 - y.2|

/-- First hidden unit: weights `1/2` and `-1/4`, bias `1`. -/
def h1 (x : ℚ × ℚ) : ℚ := relu (x.1 / 2 - x.2 / 4 + 1)

/-- Second hidden unit: weights `-1/3` and `1`, bias `2`. -/
def h2 (x : ℚ × ℚ) : ℚ := relu (-x.1 / 3 + x.2 + 2)

/-- Output unit, ReLU applied to weights `1/5` and `2` over the hidden layer. -/
def out (x : ℚ × ℚ) : ℚ := relu (h1 x / 5 + h2 x * 2)

/-! ## Layer bounds, each stated as a multiple of `d` -/

/-- `1/2 · d` bounds the first hidden unit: the two weights contribute `1/2` and `1/4`,
and `1/4 ≤ 1/2` is what lets both terms share one coefficient. -/
theorem h1_le (x y : ℚ × ℚ) : |h1 x - h1 y| ≤ (1 / 2) * d x y := by
  have hd : 0 ≤ |x.1 - y.1| := abs_nonneg _
  have he : 0 ≤ |x.2 - y.2| := abs_nonneg _
  have h45 : |x.2 - y.2| / 4 ≤ (1 / 2) * |x.2 - y.2| := by
    have h : (1 / 4 : ℚ) ≤ 1 / 2 := by norm_num
    calc |x.2 - y.2| / 4 = (1 / 4 : ℚ) * |x.2 - y.2| := by rw [div_eq_mul_left]
      _ ≤ (1 / 2) * |x.2 - y.2| := mul_le_mul_of_nonneg_right h he
  have hrelu : |h1 x - h1 y| ≤ |(x.1 / 2 - x.2 / 4 + 1) - (y.1 / 2 - y.2 / 4 + 1)| :=
    abs_relu_sub_relu_le _ _
  have hsimp : (x.1 / 2 - x.2 / 4 + 1) - (y.1 / 2 - y.2 / 4 + 1)
      = (x.1 - y.1) / 2 - (x.2 - y.2) / 4 := by ring
  have htri : |(x.1 - y.1) / 2 - (x.2 - y.2) / 4|
      ≤ |x.1 - y.1| / 2 + |x.2 - y.2| / 4 := by
    have h : |(x.1 - y.1) / 2 + (-(x.2 - y.2) / 4)|
        ≤ |(x.1 - y.1) / 2| + |(-(x.2 - y.2) / 4)| := abs_add _ _
    simpa [sub_eq_add_neg, abs_neg, div_eq_mul_left] using h
  calc |h1 x - h1 y|
      ≤ |(x.1 / 2 - x.2 / 4 + 1) - (y.1 / 2 - y.2 / 4 + 1)| := hrelu
    _ = |(x.1 - y.1) / 2 - (x.2 - y.2) / 4| := by rw [hsimp]
    _ ≤ |x.1 - y.1| / 2 + |x.2 - y.2| / 4 := htri
    _ ≤ (1 / 2) * |x.1 - y.1| + (1 / 2) * |x.2 - y.2| := by
        have h12 : |x.1 - y.1| / 2 = (1 / 2 : ℚ) * |x.1 - y.1| := by
          rw [div_eq_mul_left]
        exact add_le_add (by rw [h12]) h45
    _ = (1 / 2) * d x y := by rw [mul_add, d]

/-- `1 · d` bounds the second hidden unit, whose weights are `1/3` and `1`. -/
theorem h2_le (x y : ℚ × ℚ) : |h2 x - h2 y| ≤ d x y := by
  have hd : 0 ≤ |x.1 - y.1| := abs_nonneg _
  have he : 0 ≤ |x.2 - y.2| := abs_nonneg _
  have hrelu : |h2 x - h2 y| ≤ |(-x.1 / 3 + x.2 + 2) - (-y.1 / 3 + y.2 + 2)| :=
    abs_relu_sub_relu_le _ _
  have hsimp : (-x.1 / 3 + x.2 + 2) - (-y.1 / 3 + y.2 + 2)
      = -((x.1 - y.1) / 3) + (x.2 - y.2) := by ring
  have htri : |-((x.1 - y.1) / 3) + (x.2 - y.2)| ≤ |(x.1 - y.1) / 3| + |x.2 - y.2| :=
    abs_add _ _
  have h3 : (1 / 3 : ℚ) * |x.1 - y.1| ≤ 1 * |x.1 - y.1| :=
    mul_le_mul_of_nonneg_right (by norm_num) hd
  calc |h2 x - h2 y|
      ≤ |(-x.1 / 3 + x.2 + 2) - (-y.1 / 3 + y.2 + 2)| := hrelu
    _ = |-((x.1 - y.1) / 3) + (x.2 - y.2)| := by rw [hsimp]
    _ ≤ |(x.1 - y.1) / 3| + |x.2 - y.2| := htri
    _ ≤ d x y := by
        have hdiv : |(x.1 - y.1) / 3| = (1 / 3 : ℚ) * |x.1 - y.1| := by
          rw [div_eq_mul_left]
        rw [hdiv, d]
        exact add_le_add (by simpa using h3) (by simp [he])

/-! ## The network and its computed constant -/

/-- The constant the module computes: `1/5` of the first unit's factor plus `2` times the
second unit's factor. Written as data so the theorem below can be read off it. -/
def lip : ℚ := 1 / 5 * (1 / 2) + 2 * 1

/-- **The two-layer ReLU network is Lipschitz with the computed constant.** For all
inputs, the output difference is at most `lip · d x y`. Each `relu` is non-expansive, so
the whole bound is the output layer's weights applied to the two hidden factors. -/
theorem out_le (x y : ℚ × ℚ) : |out x - out y| ≤ lip * d x y := by
  have hnz : 0 ≤ d x y := by
    rw [d]; exact add_nonneg (abs_nonneg _) (abs_nonneg _)
  have hrelu : |out x - out y| ≤ |(h1 x / 5 + h2 x * 2) - (h1 y / 5 + h2 y * 2)| :=
    abs_relu_sub_relu_le _ _
  have hsplit : (h1 x / 5 + h2 x * 2) - (h1 y / 5 + h2 y * 2)
      = (h1 x - h1 y) / 5 + (h2 x - h2 y) * 2 := by ring
  have htri : |((h1 x - h1 y) / 5 + (h2 x - h2 y) * 2)|
      ≤ |(h1 x - h1 y) / 5| + |(h2 x - h2 y) * 2| := abs_add _ _
  have h1b : |(h1 x - h1 y) / 5| ≤ (1 / 5) * ((1 / 2) * d x y) := by
    have : |(h1 x - h1 y) / 5| = (1 / 5 : ℚ) * |h1 x - h1 y| := by rw [div_eq_mul_left]
    rw [this]; exact mul_le_mul_of_nonneg_left (h1_le x y) (by norm_num)
  have h2b : |(h2 x - h2 y) * 2| ≤ 2 * d x y := by
    have hab : |(h2 x - h2 y) * 2| = |h2 x - h2 y| * |2| := abs_mul _ _
    have h2 : |(2 : ℚ)| = 2 := by norm_num
    rw [hab, h2]
    exact mul_le_mul_of_nonneg_right (h2_le x y) (by norm_num)
  calc |out x - out y|
      ≤ |(h1 x / 5 + h2 x * 2) - (h1 y / 5 + h2 y * 2)| := hrelu
    _ = |(h1 x - h1 y) / 5 + (h2 x - h2 y) * 2| := by rw [hsplit]
    _ ≤ |(h1 x - h1 y) / 5| + |(h2 x - h2 y) * 2| := htri
    _ ≤ (1 / 5) * ((1 / 2) * d x y) + 2 * d x y := add_le_add h1b h2b
    _ = (1 / 5 * (1 / 2) + 2 * 1) * d x y := by ring
    _ = lip * d x y := by rw [lip]

/-- The constant is a positive rational, so the bound above is not vacuous. -/
theorem lip_pos : 0 < lip := by
  show (0 : ℚ) < 1 / 5 * (1 / 2) + 2 * 1
  norm_num

/-- The network is not constant: `out (0,0)` and `out (1,0)` differ, so a bound of `0`
would be false and `lip` is carrying real weight. -/
theorem out_not_constant : out (0, 0) ≠ out (1, 0) := by
  intro h
  have h1z : h1 (0, 0) = 1 := by
    show max ((0 : ℚ) / 2 - 0 / 4 + 1) 0 = 1
    norm_num
  have h1o : h1 (1, 0) = 1 / 2 := by
    show max ((1 : ℚ) / 2 - 0 / 4 + 1) 0 = 1 / 2
    norm_num
  have h2z : h2 (0, 0) = 2 := by
    show max ((0 : ℚ) / -3 + 0 + 2) 0 = 2
    norm_num
  have h2o : h2 (1, 0) = (5 : ℚ) / 3 := by
    show max ((1 : ℚ) / -3 + 0 + 2) 0 = 5 / 3
    norm_num
  have lz : out (0, 0) = (1 : ℚ) / 5 + 4 := by
    show max (h1 (0, 0) / 5 + h2 (0, 0) * 2) 0 = 1 / 5 + 4
    rw [h1z, h2z]; norm_num
  have lo : out (1, 0) = (23 : ℚ) / 30 := by
    show max (h1 (1, 0) / 5 + h2 (1, 0) * 2) 0 = 23 / 30
    rw [h1o, h2o]; norm_num
  rw [lz, lo] at h
  exact absurd h (by norm_num)

end JurisLean.Mandate.ReLUApprox
