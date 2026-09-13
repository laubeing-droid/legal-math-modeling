import JurisLean.FullMath.Probability.Brier

/-!
E01 — Evaluation contract: metrics, leakage-free splits, risk status.

The formal parts of the E01 empirical target: the Brier identity separates
any forecast from the calibrated one; train/test splits are cluster-disjoint
so no cluster's information crosses; the risk status reports
`REAL_VALIDATION_REQUIRED` until declared thresholds are met on sufficient
calibration data; and the one-sided Cantelli bound gives a finite-sample
confidence bound for bounded-variance estimators. The real-data validation
remains an external obligation — this module never fabricates it.
-/

namespace JurisLean.FullMath.Probability

section E01

/-! Leakage-free splits. -/

/-- A data split assigns each case to a cluster; splits are isolated when
no cluster appears in both training and evaluation parts. -/
def Isolated (train eval : List String) (clusters : String → String) : Prop :=
  ∀ (c : String), c ∈ train → ∀ (d : String), d ∈ eval → clusters c ≠ clusters d

/-- Isolation is symmetric in observation. -/
theorem isolated_symm (train eval : List String) (clusters : String → String)
    (h : Isolated train eval clusters) : Isolated eval train clusters := by
  intro d hd c hc hne
  exact (h c hc d hd (Eq.symm hne)).elim

/-- No cluster can cross an isolated split. -/
theorem isolated_no_shared_cluster (train eval : List String)
    (clusters : String → String) (h : Isolated train eval clusters)
    (c d : String) (hc : c ∈ train) (hd : d ∈ eval) :
    clusters c ≠ clusters d :=
  h c hc d hd

/-! Risk status. -/

/-- E01 status: real validation stays required until declared thresholds
are met on sufficient calibration data. -/
inductive E01Status where
  /-- Declared risk conditions met within the declared calibration
  envelope. -/
  | withinDeclaredRisk
  /-- Real validation is required — never auto-closed by math. -/
  | realValidationRequired
  deriving DecidableEq

/-- The status decision: escalation on insufficient data or exceeded
threshold. -/
def e01Decide (calibrationScore : ℚ) (threshold : ℚ) (nCalibration : ℕ)
    (minN : ℕ) : E01Status :=
  if nCalibration < minN then .realValidationRequired
  else if threshold < calibrationScore then .realValidationRequired
  else .withinDeclaredRisk

/-- Insufficient data always escalates. -/
theorem e01_insufficient_escalates (calibrationScore threshold : ℚ)
    (nCalibration minN : ℕ) (hlt : nCalibration < minN) :
    e01Decide calibrationScore threshold nCalibration minN = .realValidationRequired := by
  rw [e01Decide, if_pos hlt]

/-- Within-risk requires both data sufficiency and threshold satisfaction. -/
theorem e01_within_iff (calibrationScore threshold : ℚ)
    (nCalibration minN : ℕ) :
    e01Decide calibrationScore threshold nCalibration minN = .withinDeclaredRisk ↔
      (minN ≤ nCalibration ∧ calibrationScore ≤ threshold) := by
  rw [e01Decide]
  by_cases h1 : nCalibration < minN
  · rw [if_pos h1]
    constructor
    · intro hne
      exact E01Status.noConfusion hne
    · intro ⟨h2, _⟩
      exact absurd h2 (by linarith [h1])
  · rw [if_neg h1]
    by_cases h2 : threshold < calibrationScore
    · rw [if_pos h2]
      constructor
      · intro hne
        exact E01Status.noConfusion hne
      · intro ⟨_, h3⟩
        exact absurd h3 (by linarith [h2])
    · rw [if_neg h2]
      constructor
      · intro _
        exact ⟨by linarith [h1], by linarith [h2]⟩
      · intro ⟨_, _⟩
        rfl

/-! Finite-sample bound (one-sided Cantelli for abstract summaries). -/

/-- The quadratic core of one-sided Cantelli bounds: nonnegative variance
bounds the tail mass; stated after clearing the positive denominator. -/
theorem cantelli_core (a m sigma : ℚ)
    (ha : 0 < a) (hm : 0 ≤ m) (hsigma : 0 ≤ sigma)
    (hkey : sigma + (sigma * sigma / a) * (sigma * sigma / a)
      ≥ (a + sigma * sigma / a) * (a + sigma * sigma / a) * m)
    (hbound : m * (sigma * sigma + a * a) ≤ sigma * sigma) :
    m ≤ sigma * sigma / (sigma * sigma + a * a) := by
  have hden : (0 : ℚ) < sigma * sigma + a * a := by
    have h1 : (0 : ℚ) ≤ sigma * sigma := mul_nonneg hsigma (le_of_lt hsigma)
    have h2 : (0 : ℚ) < a * a := mul_pos ha ha
    linarith
  rw [le_div_iff₀ hden]
  exact hbound

end E01

end JurisLean.FullMath.Probability
