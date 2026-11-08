import Mathlib

/-!
Sequential feedback gains for one response-measurement-learning loop.
This file derives the cross coefficients of the actual composite map. It does
not reprove Banach's theorem or assume that every legal process is contractive.
Status: source reviewed only; CI_NOT_RUN. No local Lean execution.
-/

namespace LegalMath20261108.SequentialFeedback

variable {X T Y : Type*}

def advance (response : X → T → X) (measure : X → Y)
    (learn : T → Y → T) (p : X × T) : X × T :=
  let next := response p.1 p.2
  (next, learn p.2 (measure next))

section Metric

variable [PseudoMetricSpace X] [PseudoMetricSpace T] [PseudoMetricSpace Y]

/-- The learning component consumes the new response, yielding cross matrix
`[[a,b],[c*m*a,d+c*m*b]]`. The hypotheses concern the three separate maps,
not the composite conclusion. -/
theorem sequential_gain
    (response : X → T → X) (measure : X → Y) (learn : T → Y → T)
    (a b c d m : ℝ) (hc : 0 ≤ c) (hm : 0 ≤ m)
    (hR : ∀ x t x' t', dist (response x t) (response x' t') ≤
      a * dist x x' + b * dist t t')
    (hM : ∀ x x', dist (measure x) (measure x') ≤ m * dist x x')
    (hU : ∀ t y t' y', dist (learn t y) (learn t' y') ≤
      d * dist t t' + c * dist y y') (p q : X × T) :
    dist (advance response measure learn p).1 (advance response measure learn q).1 ≤
        a * dist p.1 q.1 + b * dist p.2 q.2 ∧
    dist (advance response measure learn p).2 (advance response measure learn q).2 ≤
        (c * m * a) * dist p.1 q.1 + (d + c * m * b) * dist p.2 q.2 := by
  constructor
  · exact hR p.1 p.2 q.1 q.2
  · change dist (learn p.2 (measure (response p.1 p.2)))
      (learn q.2 (measure (response q.1 q.2))) ≤ _
    calc
      _ ≤ d * dist p.2 q.2 +
          c * dist (measure (response p.1 p.2)) (measure (response q.1 q.2)) :=
        hU p.2 _ q.2 _
      _ ≤ d * dist p.2 q.2 +
          c * (m * dist (response p.1 p.2) (response q.1 q.2)) :=
        add_le_add_left (mul_le_mul_of_nonneg_left (hM _ _) hc) _
      _ ≤ d * dist p.2 q.2 +
          c * (m * (a * dist p.1 q.1 + b * dist p.2 q.2)) :=
        add_le_add_left (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (hR _ _ _ _) hm) hc) _
      _ = _ := by ring

/-- A row-sum specialization of the existing weighted matrix criterion. -/
theorem sequential_max_bound
    (response : X → T → X) (measure : X → Y) (learn : T → Y → T)
    (a b c d m r : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (hm : 0 ≤ m)
    (hR : ∀ x t x' t', dist (response x t) (response x' t') ≤
      a * dist x x' + b * dist t t')
    (hM : ∀ x x', dist (measure x) (measure x') ≤ m * dist x x')
    (hU : ∀ t y t' y', dist (learn t y) (learn t' y') ≤
      d * dist t t' + c * dist y y')
    (rowR : a + b ≤ r) (rowU : c * m * a + d + c * m * b ≤ r)
    (p q : X × T) :
    max (dist (advance response measure learn p).1 (advance response measure learn q).1)
        (dist (advance response measure learn p).2 (advance response measure learn q).2) ≤
      r * max (dist p.1 q.1) (dist p.2 q.2) := by
  let D := max (dist p.1 q.1) (dist p.2 q.2)
  have hx : dist p.1 q.1 ≤ D := le_max_left _ _
  have ht : dist p.2 q.2 ≤ D := le_max_right _ _
  have hD : 0 ≤ D := le_trans dist_nonneg hx
  have gain := sequential_gain response measure learn a b c d m hc hm hR hM hU p q
  apply max_le
  · calc
      _ ≤ a * dist p.1 q.1 + b * dist p.2 q.2 := gain.1
      _ ≤ a * D + b * D := add_le_add
        (mul_le_mul_of_nonneg_left hx ha) (mul_le_mul_of_nonneg_left ht hb)
      _ = (a + b) * D := by ring
      _ ≤ r * D := mul_le_mul_of_nonneg_right rowR hD
  · have hca : 0 ≤ c * m * a := mul_nonneg (mul_nonneg hc hm) ha
    have hdb : 0 ≤ d + c * m * b := add_nonneg hd (mul_nonneg (mul_nonneg hc hm) hb)
    calc
      _ ≤ (c * m * a) * dist p.1 q.1 + (d + c * m * b) * dist p.2 q.2 := gain.2
      _ ≤ (c * m * a) * D + (d + c * m * b) * D := add_le_add
        (mul_le_mul_of_nonneg_left hx hca) (mul_le_mul_of_nonneg_left ht hdb)
      _ = (c * m * a + d + c * m * b) * D := by ring
      _ ≤ r * D := mul_le_mul_of_nonneg_right rowU hD

end Metric

/-- A nonconstant, mutually coupled mean-response example. -/
def responseExample (x t : ℝ) : ℝ := x / 4 + t / 2 + 1 / 8

def learnExample (t y : ℝ) : ℝ := t / 4 + y / 2 + 1 / 8

def exampleStep : ℝ × ℝ → ℝ × ℝ := advance responseExample id learnExample

theorem example_step_formula (x t : ℝ) :
    exampleStep (x,t) = (x / 4 + t / 2 + 1 / 8, x / 8 + t / 2 + 3 / 16) := by
  apply Prod.ext
  · rfl
  · dsimp [exampleStep, advance, responseExample, learnExample]
    ring

theorem example_square_invariant (x t : ℝ)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    0 ≤ (exampleStep (x,t)).1 ∧ (exampleStep (x,t)).1 ≤ 1 ∧
    0 ≤ (exampleStep (x,t)).2 ∧ (exampleStep (x,t)).2 ≤ 1 := by
  rw [example_step_formula]
  dsimp
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

theorem example_fixed_point : exampleStep (1/2, 1/2) = (1/2, 1/2) := by
  rw [example_step_formula]
  norm_num

theorem example_error_bound (x t : ℝ) :
    max |(exampleStep (x,t)).1 - 1/2| |(exampleStep (x,t)).2 - 1/2| ≤
      (3/4 : ℝ) * max |x - 1/2| |t - 1/2| := by
  let D := max |x - 1/2| |t - 1/2|
  have hx : |x - 1/2| ≤ D := le_max_left _ _
  have ht : |t - 1/2| ≤ D := le_max_right _ _
  have hD : 0 ≤ D := le_trans (abs_nonneg _) hx
  have xb := abs_le.mp hx
  have tb := abs_le.mp ht
  rw [example_step_formula]
  apply max_le
  · apply abs_le.mpr
    constructor <;> dsimp <;> linarith [xb.1, xb.2, tb.1, tb.2]
  · apply abs_le.mpr
    constructor <;> dsimp <;> linarith [xb.1, xb.2, tb.1, tb.2]

def iterateExample : Nat → ℝ × ℝ → ℝ × ℝ
  | 0, p => p
  | n + 1, p => exampleStep (iterateExample n p)

theorem example_geometric_bound (n : Nat) (p : ℝ × ℝ) :
    max |(iterateExample n p).1 - 1/2| |(iterateExample n p).2 - 1/2| ≤
      (3/4 : ℝ)^n * max |p.1 - 1/2| |p.2 - 1/2| := by
  induction n with
  | zero => simp [iterateExample]
  | succ n ih =>
    calc
      _ ≤ (3/4 : ℝ) *
          max |(iterateExample n p).1 - 1/2| |(iterateExample n p).2 - 1/2| :=
        example_error_bound _ _
      _ ≤ (3/4 : ℝ) * ((3/4 : ℝ)^n * max |p.1 - 1/2| |p.2 - 1/2|) :=
        mul_le_mul_of_nonneg_left ih (by norm_num)
      _ = _ := by rw [pow_succ]; ring

/-- Zero dependence on each component's own old input does not bound the
cross feedback: response doubles the parameter and learning doubles response. -/
theorem zero_self_dependence_can_expand :
    advance (fun (_x t : ℝ) => 2*t) id (fun (_t y : ℝ) => 2*y) (0,1) = (2,4) ∧
    max |(2:ℝ)| |(4:ℝ)| > max |(0:ℝ)| |(1:ℝ)| := by
  norm_num [advance]

end LegalMath20261108.SequentialFeedback
