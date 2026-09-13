import JurisLean.FullMath.Core.Foundations

/-!
C03/C04 — Scenario-set to probability/amount bridge, and the concrete
norm-probability-amount-strategy joint instance: the realized choice in
each scenario is bounded by the per-scenario worst case, and the two
payment scenarios give expectation `D − pC` with an individually
rational settlement in the same statement.
-/

namespace JurisLean.FullMath.Composition

/-- Indicator as an honest rational number. -/
def ind (b : Bool) : ℚ := if b = true then 1 else 0

/-- The worst-case indicator over a scenario set: 1 if some admissible
choice triggers the event. -/
open scoped Classical in
noncomputable def maxInd (S : Set Bool) (ev : Bool → Bool) : ℚ :=
  if (∃ y, y ∈ S ∧ ev y = true) then 1 else 0

/-- C03: the scenario bridge — for admissible choices `y₀ ∈ S₀`,
`y₁ ∈ S₁`, the realized indicator expectation is bounded by the weighted
per-scenario worst cases; nonnegative weights preserve the bound. -/
theorem scenario_bridge (p0 p1 : ℚ) (hp0 : 0 ≤ p0) (hp1 : 0 ≤ p1)
    (S0 S1 : Set Bool) (ev : Bool → Bool) (y0 y1 : Bool)
    (hy0 : y0 ∈ S0) (hy1 : y1 ∈ S1) :
    p0 * ind (ev y0) + p1 * ind (ev y1)
      ≤ p0 * maxInd S0 ev + p1 * maxInd S1 ev := by
  have h0 : ind (ev y0) ≤ maxInd S0 ev := by
    unfold ind maxInd
    by_cases h : ev y0 = true
    · have hex : ∃ y, y ∈ S0 ∧ ev y = true := ⟨y0, hy0, h⟩
      rw [if_pos h, if_pos hex]
    · rw [if_neg h]
      by_cases hex : ∃ y, y ∈ S0 ∧ ev y = true
      · rw [if_pos hex]
        norm_num
      · rw [if_neg hex]
  have h1 : ind (ev y1) ≤ maxInd S1 ev := by
    unfold ind maxInd
    by_cases h : ev y1 = true
    · have hex : ∃ y, y ∈ S1 ∧ ev y = true := ⟨y1, hy1, h⟩
      rw [if_pos h, if_pos hex]
    · rw [if_neg h]
      by_cases hex : ∃ y, y ∈ S1 ∧ ev y = true
      · rw [if_pos hex]
        norm_num
      · rw [if_neg hex]
  nlinarith [mul_le_mul_of_nonneg_right h0 hp0, mul_le_mul_of_nonneg_right h1 hp1]

/-- C04: the concrete joint instance — the complete two-scenario payment
set {lose → D − C, win → D} with lose probability p gives win probability
1 − p and expectation D − pC; settling at D is individually rational for
both sides (plaintiff expects at most D, defendant caps at D), in one
theorem. -/
theorem joint_instance (D C p : ℚ) (hC : 0 ≤ C) (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    (p * (D - C) + (1 - p) * D = D - p * C) ∧
      ((1 - p) * 1 + p * 0 = 1 - p) ∧
      (D - p * C ≤ D ∧ D ≤ D) := by
  refine ⟨by ring, by ring, ?_⟩
  constructor
  · have : p * C ≥ 0 := mul_nonneg hp hC
    linarith
  · rfl

end JurisLean.FullMath.Composition
