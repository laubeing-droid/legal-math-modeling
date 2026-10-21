import JurisLean.Candidates.Final20261021.Behavior
import Mathlib.Topology.MetricSpace.Contracting

namespace JurisLean.Candidates.Final20261021.Policy
open Filter Function
open scoped Topology NNReal

-- This is the finite kernel identity. Its causal interpretation still needs
-- consistency, exchangeability, measurement and mechanism stability.
theorem u12_1_finite_ipw {X A : Type} [Fintype X] [Fintype A]
    (mass : X → ℚ) (logging target outcome : X → A → ℚ)
    (support : ∀ x a, target x a ≠ 0 → logging x a ≠ 0) :
    (∑ x, (mass x * ∑ a, (logging x a * (target x a / logging x a) * outcome x a))) =
      ∑ x, (mass x * ∑ a, (target x a * outcome x a)) := by
  apply Finset.sum_congr rfl
  intro x hx
  congr 1
  apply Finset.sum_congr rfl
  intro a ha
  by_cases hz : target x a = 0
  · simp [hz]
  · have hlog := support x a hz
    field_simp [hlog] <;> ring

theorem u12_3_clipped_bias (w c y : ℝ) (hw : 0 ≤ w) (hc : 0 ≤ c)
    (hy : 0 ≤ y) (hy1 : y ≤ 1) :
    w*y - min w c*y = max (w-c) 0*y ∧
    0 ≤ w*y - min w c*y ∧ w*y - min w c*y ≤ max (w-c) 0 := by
  rcases le_total w c with h | h
  · rw [min_eq_left h, max_eq_right (sub_nonpos.mpr h)]
    constructor <;> simp
  · rw [min_eq_right h, max_eq_left (sub_nonneg.mpr h)]
    constructor
    · ring
    · constructor <;> nlinarith

theorem u12_2_contraction_sufficient {D : Type*} [MetricSpace D]
    [CompleteSpace D] [Nonempty D] (T : D → D) (q : ℝ≥0)
    (contracting : ContractingWith q T) :
    ∃ fixed : D, T fixed = fixed ∧ (∀ y, T y = y → y = fixed) ∧
      (∀ x, Tendsto (fun n => T^[n] x) atTop (𝓝 fixed)) ∧
      (∀ x n, dist (T^[n] x) fixed ≤ dist x (T x) * (q : ℝ)^n / (1-q)) := by
  refine ⟨ContractingWith.fixedPoint T contracting, contracting.fixedPoint_isFixedPt, ?_, ?_, ?_⟩
  · intro y hy
    exact contracting.fixedPoint_unique hy
  · exact contracting.tendsto_iterate_fixedPoint
  · exact contracting.apriori_dist_iterate_fixedPoint_le

theorem u12_4_signal_vs_incentive (pE pG : ℝ) :
    (pG - 1/10 < pE - 3/5 ∧ 0 < pE - 3/5) ↔
      (1/2 < pE - pG ∧ 3/5 < pE) := by
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

theorem distinguishable_signal_insufficient :
    (3/5 : ℚ) ≠ 1/2 ∧ (3/5 - 3/5 : ℚ) < 1/2 - 1/10 := by norm_num

structure PolicyRequest where
  caseId : CaseId
  targetVersion : Nat
  responseVersion : Nat
  loggingProbability : ℚ
  targetProbability : ℚ
  outcome : ℚ
  identifyingEvidence : Option SourceRef
  deriving DecidableEq, Repr

def proposed_off_policy_value (r : PolicyRequest) : Result ℚ :=
  if r.identifyingEvidence.isNone then .unknown .notIdentified
  else if r.targetProbability < 0 ∨ 1 < r.targetProbability ∨
      r.loggingProbability < 0 ∨ 1 < r.loggingProbability then .rejected .unsupported
  else if r.targetProbability = 0 then .known 0
  else if r.loggingProbability = 0 then .unknown .notIdentified
  else .known (r.targetProbability / r.loggingProbability * r.outcome)

end JurisLean.Candidates.Final20261021.Policy
