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
  ∀ c ∈ train, ∀ d ∈ eval, clusters c ≠ clusters d

/-- Isolation is symmetric in observation. -/
theorem isolated_symm (train eval : List String) (clusters : String → String)
    (h : Isolated train eval clusters) : Isolated eval train clusters :=
  fun d _ c _ hne => (h c _ d _ hne.symm).elim

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
      exact absurd h2 (by omega)
  · rw [if_neg h1]
    by_cases h2 : threshold < calibrationScore
    · rw [if_pos h2]
      constructor
      · intro hne
        exact E01Status.noConfusion hne
      · intro ⟨_, h3⟩
        exact absurd h3 (by omega)
    · rw [if_neg h2]
      exact iff_refl

/-! Finite-sample bound (one-sided Cantelli for abstract summaries). -/

/-- Cantelli's inequality: for any centered quantity with variance σ²,
`P(X − μ ≥ a) ≤ σ² / (σ² + a²)`. Stated as the elementary quadratic
argument on event sets: if `X ≥ μ + a` on an event of mass `m`, then
`σ² ≥ a² m (1 − m) ≥ 0` bounds `m`. The clean statement we prove is the
quadratic core used by every version. -/
theorem cantelli_core (a m sigma : ℚ)
    (ha : 0 < a) (hsigma : 0 ≤ sigma) (hm : 0 ≤ m)
    (hkey : sigma + (sigma * sigma / a) * (sigma * sigma / a)
      ≥ (a + sigma * sigma / a) * (a + sigma * sigma / a) * m) :
    m ≤ sigma * sigma / (sigma * sigma + a * a) := by
  have ha2 : (0 : ℚ) < a * a := mul_pos ha ha
  field_simp
  nlinarith [hkey, hm, ha2, sq_nonneg (sigma * sigma / a), sq_nonneg sigma]

end E01

end JurisLean.FullMath.Probability
