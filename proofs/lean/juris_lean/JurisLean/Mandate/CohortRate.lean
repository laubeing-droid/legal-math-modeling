import Mathlib

/-!
# Mandate module A — win-rate step two: the rate computed on the retrieved cohort

P-112 demands a three-step pipeline: retrieval defines the cohort, the cohort is
counted, and only then is the case at hand compared against it. Step two is the
step that carries probability, and it had no Lean carrier at all — the
arithmetic lived only in `tools/unified_math_v2/unified/win_model.py`.

Everything here is exact. A rate is a numerator/denominator pair over `Nat`;
there is no float and no division, so `≤ₛ` is cross-multiplication and every
statement stays inside integer arithmetic.

Status: NOT imported by `JurisLean.lean`, NOT in `AxiomAudit.lean`. It must pass
a CI module build (`mode=changed-module`) before any of it may be cited as
elaborated.
-/

namespace JurisLean.Mandate.CohortRate

/-- Successes in a cohort, structural recursion so the equations are ours. -/
def successes : List Bool → Nat
  | [] => 0
  | true :: rest => successes rest + 1
  | false :: rest => successes rest

/-- A cohort rate: exact counts, denominator forced nonzero by the constructor. -/
structure Rate where
  num : Nat
  den : Nat
  denPos : 0 < den

/--
Step two. An empty cohort yields *no* rate: the pipeline may not manufacture a
probability out of nothing, which is the fail-closed rule P-113 asks for.
-/
def rateOfCohort (obs : List Bool) : Option Rate :=
  match obs with
  | [] => none
  | a :: as =>
      some {
        num := successes (a :: as)
        den := (a :: as).length
        denPos := Nat.succ_pos _
      }

/-- Comparison of rates by cross-multiplication; no division is ever formed. -/
infix:50 " ≤ₛ " => fun x y => x.num * y.den ≤ y.num * x.den

theorem successes_le_length (obs : List Bool) : successes obs ≤ obs.length := by
  induction obs with
  | nil => exact Nat.zero_le _
  | cons x xs ih =>
      cases x with
      | true => simp [successes]; omega
      | false => simp [successes]; omega

/-- Step two is total on a non-empty cohort. -/
theorem rateOfCohort_defined (obs : List Bool) (h : obs ≠ []) :
    ∃ r : Rate, rateOfCohort obs = some r := by
  cases obs with
  | nil => exact absurd rfl h
  | cons a as => exact ⟨_, rfl⟩

/--
Fail-closed characterisation: step two returns nothing *exactly when* the cohort
is empty. The one-directional `rateOfCohort [] = none` is not enough — a
downgraded pipeline that returned a rate for an empty cohort would still satisfy
it, which is how a synthetic cohort could masquerade as a retrieved one.
-/
theorem rateOfCohort_none_iff (obs : List Bool) : rateOfCohort obs = none ↔ obs = [] := by
  cases obs with
  | nil => simp [rateOfCohort]
  | cons a as =>
      simp only [rateOfCohort]
      constructor
      · intro h
        cases h
      · intro h
        cases h

/-- Every rate step two returns lies in the unit interval. -/
theorem rateOfCohort_num_le_den {obs : List Bool} {r : Rate}
    (h : rateOfCohort obs = some r) : r.num ≤ r.den := by
  cases obs with
  | nil => cases h
  | cons a as =>
      simp only [rateOfCohort] at h
      have hb : successes (a :: as) ≤ (a :: as).length := successes_le_length _
      simp only [List.length_cons] at hb
      exact hb

/--
Monotonicity, favourable direction: one more success in the same cohort cannot
lower the rate. The retrieval layer may re-extend a cohort with a later recall
pass, and the estimate only moves up.
-/
theorem rate_le_addedSuccess (r : Rate) :
    r ≤ₛ { num := r.num + r.den, den := r.den, denPos := r.denPos } := by
  show r.num * r.den ≤ (r.num + r.den) * r.den
  nlinarith

/-- Monotonicity, unfavourable direction: one more failure cannot raise the rate. -/
theorem addedFailure_le_rate (r : Rate) :
    { num := r.num, den := r.den + 1, denPos := Nat.succ_pos _ } ≤ₛ r := by
  show r.num * r.den ≤ r.num * (r.den + 1)
  nlinarith

/-- The order is reflexive, so a cohort always compares equal to itself. -/
theorem rate_le_self (r : Rate) : r ≤ₛ r := Nat.le_refl _

end JurisLean.Mandate.CohortRate
