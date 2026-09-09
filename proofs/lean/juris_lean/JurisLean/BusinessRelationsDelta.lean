import JurisLean.BusinessRelations

/-!
Clipped-balance bridge correction. SOURCE_DRAFT_CI_NOT_RUN.
This is NOT a proof of the Python JSON parser, input origin, or root checker.
Keep the original rawBalance lemmas as algebraic facts; do not use them as
clipped-principal expectation lemmas when overpayment is possible.
-/
namespace JurisLean.BusinessRelations

/-- A CI signature check: filter requires DecidablePred, not DecidableEq W. -/
def filterSignatureProbe {W : Type} (s : Finset W) (p : W → Prop)
    [DecidablePred p] : Finset W := s.filter p

def clippedBalance (principal payment : ℚ) (recognized : Bool) : ℚ :=
  max (rawBalance principal payment recognized) 0

def overpaymentResidual (principal payment : ℚ) (recognized : Bool) : ℚ :=
  max (-rawBalance principal payment recognized) 0

theorem split_residual_identity (r : ℚ) :
    max r 0 - max (-r) 0 = r := by
  by_cases h : 0 ≤ r
  · rw [max_eq_left h, max_eq_right (neg_nonpos.mpr h)]
    ring
  · have hr : r ≤ 0 := le_of_lt (lt_of_not_ge h)
    rw [max_eq_right hr, max_eq_left (neg_nonneg.mpr hr)]
    ring

theorem clipped_balance_nonnegative (principal payment : ℚ) (recognized : Bool) :
    0 ≤ clippedBalance principal payment recognized := by
  exact le_max_right _ _

theorem clipped_agrees_raw_when_no_overpayment
    (principal payment : ℚ) (hp : 0 ≤ principal) (hpay : payment ≤ principal)
    (recognized : Bool) :
    clippedBalance principal payment recognized = rawBalance principal payment recognized := by
  cases recognized
  · exact max_eq_left hp
  · exact max_eq_left (sub_nonneg.mpr hpay)

def principalExpectation (principal payment p : ℚ) : ℚ :=
  p * clippedBalance principal payment true +
  (1-p) * clippedBalance principal payment false

def excessExpectation (principal payment p : ℚ) : ℚ :=
  p * overpaymentResidual principal payment true +
  (1-p) * overpaymentResidual principal payment false

theorem clipped_expectation_conservation (principal payment p : ℚ) :
    principalExpectation principal payment p - excessExpectation principal payment p =
      principal - p * payment := by
  have h1 := split_residual_identity (principal - payment)
  have h0 := split_residual_identity principal
  dsimp [principalExpectation, excessExpectation, clippedBalance,
    overpaymentResidual, rawBalance]
  calc
    p * max (principal-payment) 0 + (1-p) * max principal 0 -
        (p * max (-(principal-payment)) 0 + (1-p) * max (-principal) 0)
      = p * (max (principal-payment) 0 - max (-(principal-payment)) 0) +
          (1-p) * (max principal 0 - max (-principal) 0) := by ring
    _ = p * (principal-payment) + (1-p) * principal := by rw [h1, h0]
    _ = principal - p * payment := by ring

theorem principal_expectation_nonnegative (principal payment p : ℚ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    0 ≤ principalExpectation principal payment p := by
  exact add_nonneg
    (mul_nonneg hp0 (clipped_balance_nonnegative _ _ _))
    (mul_nonneg (sub_nonneg.mpr hp1) (clipped_balance_nonnegative _ _ _))

def clippedThresholdProbability (principal payment p threshold : ℚ) : ℚ :=
  p * (if threshold ≤ clippedBalance principal payment true then 1 else 0) +
  (1-p) * (if threshold ≤ clippedBalance principal payment false then 1 else 0)

theorem clipped_threshold_probability_range (principal payment p threshold : ℚ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    0 ≤ clippedThresholdProbability principal payment p threshold ∧
      clippedThresholdProbability principal payment p threshold ≤ 1 := by
  unfold clippedThresholdProbability
  split_ifs <;> constructor <;> nlinarith

theorem clipped_same_case_settlement
    (principal payment p cp cd sp sd chosen : ℚ) (legal : Finset ℚ)
    (h : chosen ∈ acceptable legal
      (principalExpectation principal payment p - cp + sp)
      (principalExpectation principal payment p + cd - sd)) :
    chosen ∈ legal ∧
      principalExpectation principal payment p - cp + sp ≤ chosen ∧
      chosen ≤ principalExpectation principal payment p + cd - sd := by
  exact (acceptable_membership legal _ _ chosen).mp h

/-- A rational witness showing why raw and clipped analytics must be distinguished. -/
theorem overpayment_bridge_counterexample :
    principalExpectation 100 300 (2/5) = 60 ∧
    excessExpectation 100 300 (2/5) = 80 ∧
    conditionalExpectation 100 300 (2/5) = -20 ∧
    clippedThresholdProbability 100 300 (2/5) 0 = 1 ∧
    thresholdProbability 100 300 (2/5) 0 = 3/5 := by
  norm_num [principalExpectation, excessExpectation, conditionalExpectation,
    clippedBalance, overpaymentResidual, rawBalance,
    clippedThresholdProbability, thresholdProbability]

end JurisLean.BusinessRelations
