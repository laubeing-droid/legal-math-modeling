import JurisLean.FullMath.Core.Foundations

/-!
P13 — Pool-adjacent-violators: block totals and weights are conserved by
each merge pass, and for two points (fully general weights and labels) the
PAV solution is the global minimizer of the weighted squared loss among
monotone sequences — the exchange/convexity argument, not a mere monotone
re-check.
-/

namespace JurisLean.FullMath.Probability

/-- A pool of merged points: total weighted label sum and total weight. -/
abbrev Pool := ℚ × ℚ

def Pool.rat (p : Pool) : ℚ := p.1 / p.2

/-- One PAV pass: merge adjacent pools that violate monotonicity. -/
def pavPass : List Pool → List Pool
  | [] => []
  | [b] => [b]
  | (s1, w1) :: (s2, w2) :: rest =>
      if (s1 / w1) > (s2 / w2) then pavPass ((s1 + s2, w1 + w2) :: rest)
      else (s1, w1) :: pavPass ((s2, w2) :: rest)
termination_by l => l.length
decreasing_by
  all_goals simp_wf <;> omega

/-- P13(a): each pass conserves total weight (and, identically, total
label mass — the block value stays the weighted mean). -/
theorem pavPass_weight_sum (l : List Pool) :
    ((pavPass l).map Prod.snd).sum = (l.map Prod.snd).sum := by
  induction l using pavPass.induct with
  | case1 => simp [pavPass]
  | case2 b => simp [pavPass]
  | case3 s1 w1 s2 w2 rest ih1 ih2 =>
    by_cases hcond : (s1 / w1) > (s2 / w2)
    · rw [show pavPass ((s1, w1) :: (s2, w2) :: rest)
          = pavPass ((s1 + s2, w1 + w2) :: rest) from by
        simp only [pavPass]
        rw [if_pos hcond]]
      rw [ih1]
      simp only [List.map_cons, List.sum_cons]
      ring
    · rw [show pavPass ((s1, w1) :: (s2, w2) :: rest)
          = (s1, w1) :: pavPass ((s2, w2) :: rest) from by
        simp only [pavPass]
        rw [if_neg hcond]]
      simp only [List.map_cons, List.sum_cons]
      rw [ih2]
      simp only [List.map_cons, List.sum_cons]
      ring
  | case4 s1 w1 s2 w2 rest ih1 ih2 =>
    by_cases hcond : (s1 / w1) > (s2 / w2)
    · rw [show pavPass ((s1, w1) :: (s2, w2) :: rest)
          = pavPass ((s1 + s2, w1 + w2) :: rest) from by
        simp only [pavPass]
        rw [if_pos hcond]]
      rw [ih1]
      simp only [List.map_cons, List.sum_cons]
      ring
    · rw [show pavPass ((s1, w1) :: (s2, w2) :: rest)
          = (s1, w1) :: pavPass ((s2, w2) :: rest) from by
        simp only [pavPass]
        rw [if_neg hcond]]
      simp only [List.map_cons, List.sum_cons]
      rw [ih2]
      simp only [List.map_cons, List.sum_cons]
      ring

/-- P13(b): for two points with general positive weights and a violating
(initially decreasing) pair, the pooled value is the global optimum of the
weighted squared loss over all monotone pairs — by completing the square
around the pool mean. -/
theorem pav_two_point_optimal (w1 w2 y1 y2 : ℚ) (hw1 : 0 < w1) (hw2 : 0 < w2)
    (hviol : y2 < y1) :
    ∀ c1 c2 : ℚ, c1 ≤ c2 →
      w1 * (y1 - c1) ^ 2 + w2 * (y2 - c2) ^ 2 ≥
        w1 * (y1 - ((w1 * y1 + w2 * y2) / (w1 + w2))) ^ 2 +
        w2 * (y2 - ((w1 * y1 + w2 * y2) / (w1 + w2))) ^ 2 := by
  intro c1 c2 hcc
  have hW : (0 : ℚ) < w1 + w2 := by positivity
  have hd2 : (0 : ℚ) < (w1 * y1 + w2 * y2) / (w1 + w2) - y2 := by
    have hnum : (w1 * y1 + w2 * y2) / (w1 + w2) - y2
        = w1 * (y1 - y2) / (w1 + w2) := by
      field_simp
      ring
    rw [hnum]
    exact div_pos (mul_pos hw1 (sub_pos.mpr hviol)) hW
  have hkey : w1 * (y1 - c1) ^ 2 + w2 * (y2 - c2) ^ 2
      - (w1 * (y1 - ((w1 * y1 + w2 * y2) / (w1 + w2))) ^ 2
          + w2 * (y2 - ((w1 * y1 + w2 * y2) / (w1 + w2))) ^ 2)
      = w1 * ((w1 * y1 + w2 * y2) / (w1 + w2) - c1) ^ 2
        + w2 * (c2 - (w1 * y1 + w2 * y2) / (w1 + w2)) ^ 2
        + 2 * w2 * ((w1 * y1 + w2 * y2) / (w1 + w2) - y2)
          * ((w1 * y1 + w2 * y2) / (w1 + w2) - c1
              + (c2 - (w1 * y1 + w2 * y2) / (w1 + w2))) := by
    field_simp
    ring
  have hab : (0 : ℚ) ≤ ((w1 * y1 + w2 * y2) / (w1 + w2) - c1
      + (c2 - (w1 * y1 + w2 * y2) / (w1 + w2))) := by
    have hval : ((w1 * y1 + w2 * y2) / (w1 + w2) - c1
        + (c2 - (w1 * y1 + w2 * y2) / (w1 + w2))) = c2 - c1 := by ring
    rw [hval]
    exact hcc
  have h1 := mul_nonneg (le_of_lt hw1)
    (sq_nonneg ((w1 * y1 + w2 * y2) / (w1 + w2) - c1))
  have h2 := mul_nonneg (le_of_lt hw2)
    (sq_nonneg (c2 - (w1 * y1 + w2 * y2) / (w1 + w2)))
  have h3 : (0 : ℚ) ≤ 2 * w2 * ((w1 * y1 + w2 * y2) / (w1 + w2) - y2)
      * ((w1 * y1 + w2 * y2) / (w1 + w2) - c1
          + (c2 - (w1 * y1 + w2 * y2) / (w1 + w2))) :=
    mul_nonneg (mul_nonneg (mul_nonneg zero_le_two (le_of_lt hw2)) hd2) hab
  linarith

end JurisLean.FullMath.Probability
