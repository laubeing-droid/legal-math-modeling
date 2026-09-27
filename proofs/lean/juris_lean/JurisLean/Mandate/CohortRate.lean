import Mathlib
import JurisLean.Mandate.Kernel

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

-- Reuses `Kernel` for `Rate`, `successes`, `≤ₛ` and the length bound. A doc comment
-- cannot precede `namespace`: it must attach to a declaration.
namespace JurisLean.Mandate.CohortRate

open JurisLean.Mandate.Kernel

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
      have hb : successes (a :: as) ≤ (a :: as).length := successes_le_length _
      have hex : rateOfCohort (a :: as)
          = some ⟨successes (a :: as), (a :: as).length, Nat.succ_pos _⟩ := rfl
      rw [← hex] at h
      cases h
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

end JurisLean.Mandate.CohortRate
