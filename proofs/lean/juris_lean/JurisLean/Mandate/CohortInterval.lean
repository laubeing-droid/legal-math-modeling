import Mathlib
import JurisLean.Mandate.Kernel

/-!
# Mandate module — the interval step two hands to step three

The win-rate mandate is a three-step pipeline: retrieval defines the cohort, the
cohort is counted, the case is compared against it. `Mandate/CohortRate.lean`
closed step two. This module is the object step three consumes: an interval
estimate carried as an exact pair of `Kernel.Rate`s, never a float, plus the
properties the comparison layer silently relies on — the interval is ordered, its
endpoints stay inside [0,1], it moves up when a favourable observation is added,
and each endpoint moves down as the cohort grows.

All comparisons go through the kernel's cross-multiplication order `≤ₛ`, so no
division lemma and no float rounding appear anywhere. `Cohort` carries
`successes ≤ size` as a field: without it "successes out of size" is not a
counted cohort but a pair of unrelated numbers, and the unit-interval facts below
are simply false.

Status: NOT in `JurisLean.lean`, NOT in `AxiomAudit.lean`; CI_NOT_RUN.
-/

namespace JurisLean.Mandate.CohortInterval

open JurisLean.Mandate.Kernel

/-- A retrieved cohort: successes out of size, with both constraints forced. -/
structure Cohort where
  successes : Nat
  size : Nat
  sizePos : 0 < size
  succLeSize : successes ≤ size

/-- Add-one (Laplace) endpoints, as exact rates over the same denominator. -/
def low (c : Cohort) : Rate :=
  { num := c.successes + 1
    den := c.size + 2
    denPos := Nat.succ_pos _ }

def high (c : Cohort) : Rate :=
  { num := c.successes + 2
    den := c.size + 2
    denPos := Nat.succ_pos _ }

/-- The interval is ordered. -/
theorem low_le_high (c : Cohort) : low c ≤ₛ high c := by
  show (c.successes + 1) * (c.size + 2) ≤ (c.successes + 2) * (c.size + 2)
  nlinarith

/-- Both endpoints are within the unit interval: numerators bound by denominators. -/
theorem low_num_le_den (c : Cohort) : (low c).num ≤ (low c).den := by
  show c.successes + 1 ≤ c.size + 2
  have hs := c.succLeSize
  omega

theorem high_num_le_den (c : Cohort) : (high c).num ≤ (high c).den := by
  show c.successes + 2 ≤ c.size + 2
  have hs := c.succLeSize
  omega

/-- The endpoints are strictly apart: the interval is never a disguised point. -/
theorem low_num_lt_high_num (c : Cohort) : (low c).num < (high c).num := by
  show c.successes + 1 < c.successes + 2
  omega

/-- One more favourable observation: successes and size both grow, so the cohort
invariant survives. The earlier statement updated a record field with
`{ c with successes := … }`, which cannot re-justify the Prop field `succLeSize`,
so the comparison was never about a cohort at all. -/
def addFavourable (c : Cohort) : Cohort :=
  { successes := c.successes + 1
    size := c.size + 1
    sizePos := Nat.succ_pos _
    succLeSize := by
      have hs := c.succLeSize
      omega }

/-- A larger cohort at the same success count, again with the invariant proved. -/
def growSize (c : Cohort) (extra : Nat) : Cohort :=
  { successes := c.successes
    size := c.size + extra
    sizePos := by
      have hp := c.sizePos
      omega
    succLeSize := by
      have hs := c.succLeSize
      omega }

/-- Adding one favourable observation moves the lower endpoint up. -/
theorem low_le_added_success (c : Cohort) : low c ≤ₛ low (addFavourable c) := by
  show (c.successes + 1) * (c.size + 3) ≤ (c.successes + 2) * (c.size + 2)
  have hs := c.succLeSize
  nlinarith

/-- ... and moves the upper endpoint up as well, so the interval shifts, not splits. -/
theorem high_le_added_success (c : Cohort) : high c ≤ₛ high (addFavourable c) := by
  show (c.successes + 2) * (c.size + 3) ≤ (c.successes + 3) * (c.size + 2)
  have hs := c.succLeSize
  nlinarith

/--
A larger cohort lowers the lower endpoint at a fixed success count: this is the
only sense in which "more similar cases" buys precision here, and it is stated on
the exact rates rather than on a hand-waved "wider sample is better".
-/
theorem low_antitone_in_size (c : Cohort) (extra : Nat) :
    low (growSize c extra) ≤ₛ low c := by
  show (c.successes + 1) * (c.size + 2)
         ≤ (c.successes + 1) * (c.size + extra + 2)
  nlinarith

/-- Step three's fail-closed rule: no cohort, no interval, no comparison. -/
def intervalOf (c : Option Cohort) : Option (Rate × Rate) :=
  c.map fun x => (low x, high x)

theorem intervalOf_none_without_cohort : intervalOf none = none := rfl

theorem intervalOf_defined (c : Cohort) :
    ∃ p : Rate × Rate, intervalOf (some c) = some p := ⟨(low c, high c), rfl⟩

/-- A cohort with no observations still yields a legal interval, so the pipeline
degrades to prior-only instead of crashing into an undefined rate. -/
theorem interval_of_empty_successes_legal (n : Nat) (h : 0 < n) :
    (low { successes := 0, size := n, sizePos := h, succLeSize := Nat.zero_le _ }).num
      ≤ (low { successes := 0, size := n, sizePos := h, succLeSize := Nat.zero_le _ }).den :=
  low_num_le_den _

end JurisLean.Mandate.CohortInterval
