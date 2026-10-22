import JurisLean.Candidates.Final20261021.Interfaces
import JurisLean.Candidates.Final20261021.EvidenceProcedure
import JurisLean.Candidates.Final20261021.Learning

namespace JurisLean.Candidates.Final20261021.Calibration

def bernoulliBrier (p q : ℝ) : ℝ := p*(1-q)^2 + (1-p)*q^2

theorem u05_2_brier_decomposition (p q : ℝ) :
    bernoulliBrier p q = p*(1-p) + (q-p)^2 := by unfold bernoulliBrier; ring

theorem u05_2_brier_unique_optimum (p q : ℝ) :
    bernoulliBrier p p ≤ bernoulliBrier p q ∧
    (bernoulliBrier p p = bernoulliBrier p q ↔ p = q) := by
  have h1 := u05_2_brier_decomposition p p
  have h2 := u05_2_brier_decomposition p q
  have hs := sq_nonneg (q-p)
  constructor
  · nlinarith
  · constructor
    · intro he; nlinarith
    · intro he; rw [he]

structure BoundPrediction where
  contract : Learning.FitContract
  lowerCoverage : ℚ
  upperRisk : ℚ
  protocol : Nat
  validationSnapshot : Nat
  protectedGroups : List Nat
  deriving DecidableEq, Repr

def proposed_calibration_support_gate (expected : Learning.FitContract)
    (certificate : BoundPrediction) (target : ℚ) (supported : Bool) : Result BoundPrediction :=
  if certificate.contract ≠ expected then .unknown .targetMismatch
  else if supported = false then .unknown .notIdentified
  else if 0 < certificate.lowerCoverage ∧ 0 ≤ certificate.upperRisk ∧
      certificate.upperRisk ≤ target then .known certificate
  else .unknown .missingEvidence

-- A valid joint confidence event is still external to this algebraic gate.
theorem u05_2_selected_risk (numerator coverage numeratorUpper coverageLower target : ℚ)
    (positive : 0 < coverageLower) (denominator : coverageLower ≤ coverage)
    (numNonneg : 0 ≤ numerator) (numBound : numerator ≤ numeratorUpper)
    (gate : numeratorUpper / coverageLower ≤ target) : numerator / coverage ≤ target := by
  have hc : 0 < coverage := lt_of_lt_of_le positive denominator
  have hn : 0 ≤ numeratorUpper := le_trans numNonneg numBound
  have h : numerator / coverage ≤ numeratorUpper / coverageLower := by
    apply (div_le_div_iff₀ hc positive).mpr
    nlinarith
  exact le_trans h gate

theorem u05_fail_certificate_not_violation :
    ∃ actual upper target : ℚ, actual ≤ upper ∧ target < upper ∧ actual ≤ target := by
  exact ⟨0, 1, 1/2, by norm_num⟩

theorem score_does_not_establish_judgment :
    (99/100 : ℚ) > 9/10 ∧ EvidenceProcedure.judgment 0 [] = .insufficient := by
  norm_num [EvidenceProcedure.judgment, EvidenceProcedure.classify]

/-! U05.1. Under a fixed tie-free exchangeable rank, each of the `n+1` positions
    has mass `1/(n+1)`. A threshold `k` at least `(n+1)(1-α)` therefore has
    marginal mass at least `1-α` and at most 1. The infinity branch covers with
    mass 1. A fully covered margin can still leave a group uncovered. The
    continuous tie-breaking density that produces the uniform rank is an
    assumption of this finite identity, not a theorem about an arbitrary score. -/

theorem u05_1_rank_prefix_mass (n k : ℕ) :
    (k : ℚ) * (1 / ((n + 1 : ℕ) : ℚ)) = (k : ℚ) / ((n + 1 : ℕ) : ℚ) := by
  have h : ((n + 1 : ℕ) : ℚ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  field_simp [h]

theorem u05_1_threshold_marginal (n : ℕ) (α : ℚ) (k : ℕ)
    (hα0 : 0 ≤ α) (hα1 : α ≤ 1)
    (hk : ((n + 1 : ℕ) : ℚ) * (1 - α) ≤ (k : ℚ))
    (hkTop : k ≤ n + 1) :
    (1 - α) ≤ (k : ℚ) / ((n + 1 : ℕ) : ℚ) ∧
      (k : ℚ) / ((n + 1 : ℕ) : ℚ) ≤ 1 := by
  have hpos : (0 : ℚ) < ((n + 1 : ℕ) : ℚ) := by exact_mod_cast Nat.succ_pos n
  have _ : 0 ≤ 1 - α := by linarith [hα0, hα1]
  constructor
  · rw [le_div_iff₀ hpos]
    linarith [hα0, hα1, hk]
  · rw [div_le_one hpos]
    exact_mod_cast hkTop

theorem u05_1_infinity_branch (α : ℚ) (hα : 0 ≤ α) : 1 - α ≤ (1 : ℚ) := by
  linarith

theorem u05_1_marginal_not_group :
    ((2 : ℚ) / 2 = 1) ∧ ((0 : ℚ) / 1 = 0) ∧ ¬ ((0 : ℚ) ≥ 1 - 1 / 10) := by
  norm_num

end JurisLean.Candidates.Final20261021.Calibration
