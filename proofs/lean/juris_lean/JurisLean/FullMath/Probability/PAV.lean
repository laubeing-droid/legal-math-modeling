import JurisLean.FullMath.Core.Foundations

/-!
P13 — Pool-adjacent-violators: every merge conserves total weight (so a
block's value stays the weighted mean of its points), and for two points,
with fully general positive weights and a violating pair, the pooled value
is the global minimizer of the weighted squared loss over all monotone
pairs — the exchange/completing-the-square argument, not a monotone
re-check.
-/

namespace JurisLean.FullMath.Probability

/-- A pool of merged points: total weighted label sum and total weight. -/
abbrev Pool := ℚ × ℚ

def Pool.rat (p : Pool) : ℚ := p.1 / p.2

/-- Fuel-driven PAV pass: merge adjacent pools that violate monotonicity. -/
def pavGo : Nat → List Pool → List Pool
  | 0, l => l
  | fuel + 1, [] => []
  | fuel + 1, [b] => [b]
  | fuel + 1, (s1, w1) :: (s2, w2) :: rest =>
      if (s1 / w1) > (s2 / w2) then pavGo fuel ((s1 + s2, w1 + w2) :: rest)
      else (s1, w1) :: pavGo fuel ((s2, w2) :: rest)

theorem pavGo_succ_cons (n : Nat) (s1 w1 s2 w2 : ℚ) (rest : List Pool) :
    pavGo (n + 1) ((s1, w1) :: (s2, w2) :: rest)
      = if (s1 / w1) > (s2 / w2) then pavGo n ((s1 + s2, w1 + w2) :: rest)
        else (s1, w1) :: pavGo n ((s2, w2) :: rest) := rfl

/-- P13(a): every step conserves total weight — a pool's value is always
the weighted mean of the points merged into it. -/
theorem pavGo_weight_sum (fuel : Nat) (l : List Pool) :
    ((pavGo fuel l).map Prod.snd).sum = (l.map Prod.snd).sum := by
  induction fuel generalizing l with
  | zero => rfl
  | succ n ih =>
    match l with
    | [] => rfl
    | [b] => rfl
    | (s1, w1) :: (s2, w2) :: rest =>
      rw [pavGo_succ_cons]
      by_cases hcond : (s1 / w1) > (s2 / w2)
      · rw [if_pos hcond, ih]
        simp only [List.map_cons, List.sum_cons]
        ring
      · rw [if_neg hcond]
        simp only [List.map_cons, List.sum_cons]
        rw [ih ((s2, w2) :: rest)]
        simp only [List.map_cons, List.sum_cons]

/-- P13(b): for two points with general positive weights and a violating
(initially decreasing) pair, the pooled value is the global optimum of the
weighted squared loss over all monotone pairs. -/
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
    exact sub_nonneg.mpr hcc
  have h1 := mul_nonneg (le_of_lt hw1)
    (sq_nonneg ((w1 * y1 + w2 * y2) / (w1 + w2) - c1))
  have h2 := mul_nonneg (le_of_lt hw2)
    (sq_nonneg (c2 - (w1 * y1 + w2 * y2) / (w1 + w2)))
  have h3 : (0 : ℚ) ≤ 2 * w2 * ((w1 * y1 + w2 * y2) / (w1 + w2) - y2)
      * ((w1 * y1 + w2 * y2) / (w1 + w2) - c1
          + (c2 - (w1 * y1 + w2 * y2) / (w1 + w2))) :=
    mul_nonneg (mul_nonneg (mul_nonneg zero_le_two (le_of_lt hw2)) (le_of_lt hd2)) hab
  linarith

end JurisLean.FullMath.Probability
