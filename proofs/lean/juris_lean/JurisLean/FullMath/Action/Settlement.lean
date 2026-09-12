import JurisLean.FullMath.Core.Foundations

/-!
G01/G02 — Legal-action-first settlement and gross value of information.

Legality precedes utility: admissible settlements live in `A_L ∩ [L, U]`
with reservation bounds derived from the parties' own beliefs and costs
(`L = m_P − c_P + s_P`, `U = m_D + c_D − s_D`); an empty interval is a
typed separate outcome, never a forced deal. Gross information value is
nonnegative: a weighted average of cell-wise maxima dominates the value of
any single global choice — and after subtracting the signal cost the net
value can be negative.
-/

namespace JurisLean.FullMath.Action

section Settlement

/-- Party parameters for the settlement interval. -/
structure PartyParams where
  merit : ℚ
  cost : ℚ
  shift : ℚ

/-- Plaintiff reservation bound: `L = m_P − c_P + s_P`. -/
def plaintiffL (P : PartyParams) : ℚ := P.merit - P.cost + P.shift

/-- Defendant reservation bound: `U = m_D + c_D − s_D`. -/
def defendantU (D : PartyParams) : ℚ := D.merit + D.cost - D.shift

/-- The settlement zone. -/
def zone (P D : PartyParams) : Set ℚ :=
  Set.Icc (plaintiffL P) (defendantU D)

/-- Legality filters before utility, never after. -/
def admissibleSettlements (legal : Set ℚ) (P D : PartyParams) : Set ℚ :=
  legal ∩ zone P D

/-- G01(a): an admissible settlement is legal and inside the zone. -/
theorem admissible_settlement_bounds (legal : Set ℚ) (P D : PartyParams) (s : ℚ)
    (h : s ∈ admissibleSettlements legal P D) :
    s ∈ legal ∧ plaintiffL P ≤ s ∧ s ≤ defendantU D :=
  ⟨h.1, h.2.1, h.2.2⟩

/-- G01(b): common beliefs (`m_P = m_D`) give the cost-shift bracket around
the common merit. -/
theorem common_belief_zone (m cP sP cD sD : ℚ) :
    zone (⟨m, cP, sP⟩ : PartyParams) ⟨m, cD, sD⟩ =
      Set.Icc (m - cP + sP) (m + cD - sD) := rfl

/-- G01(c): the zone can be empty — a typed separate report, never a forced
deal. -/
theorem zone_can_be_empty :
    ∃ P D : PartyParams, zone P D = ∅ := by
  refine ⟨⟨0, 0, 0⟩, ⟨0, 0, 1⟩, ?_⟩
  show Set.Icc ((0:ℚ) - 0 + 0) ((0:ℚ) + 0 - 1) = ∅
  exact Set.Icc_eq_empty (by norm_num)

end Settlement

section VOI

variable {C : Type} [Fintype C] [DecidableEq C]
variable {K : Type} [Fintype K] [DecidableEq K]

/-- G02(a): gross value of information is nonnegative — the weighted average
of cell-wise maxima dominates the value of any single global choice. -/
theorem gross_voi_nonneg (w : C → ℚ) (hw : ∀ c, 0 ≤ w c)
    (u : C → K → ℚ) (k₀ : K) :
    (∑ c, w c * u c k₀) ≤ ∑ c, w c * (Finset.univ.sup (fun k => u c k)) := by
  refine Finset.sum_le_sum ?_
  intro c _
  exact mul_le_mul_of_nonneg_left
    (Finset.le_sup (f := fun k => u c k) (Finset.mem_univ k₀)) (hw c)

/-- G02(b): after subtracting the signal cost, the net value can be
negative — a concrete instance. -/
theorem net_voi_can_be_negative :
    ∃ (gross cost : ℚ), 0 ≤ gross ∧ gross < cost ∧ gross - cost < (0:ℚ) :=
  ⟨0, 1, le_refl _, by norm_num, by norm_num⟩

end VOI

end JurisLean.FullMath.Action
