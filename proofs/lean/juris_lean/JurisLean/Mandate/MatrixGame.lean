import Mathlib
import JurisLean.Mandate.Kernel

/-!
# Mandate module — the two-player value gap (R-02, first step)

`Mandate/GameTree.lean` gave a sequential single-agent value. The audit's mandate
(攻防=博弈树, 调解=纳什讨价还价) needs an *opponent*, and
`action_decision.py:147-149` already admits the shipped "equilibrium" is a
conflict filter, not Nash. Until now that disclaimer was prose.

This module proves the classical fact for a 2×2 zero-sum position: the row
player's best guaranteed payoff never exceeds the column player's concession
bound (`lower_le_upper`). The interesting half is that the inequality can be
**strict** — for matching pennies the gap is 0 < 1, which is the theorem that no
pure-strategy value exists there; the saddle-point test evaluates to `false` by
computation rather than by comment. A coordination position is also exhibited, so
the test is not a constant.

Scope kept honest: pure strategies over a simultaneous 2×2 matrix. Mixed
strategies and Nash existence (which need a simplex plus a fixed-point or
extreme-value argument) are not here and not claimed — the strict gap is exactly
why searching over pure choices cannot deliver them.

Status: NOT in `JurisLean.lean`, NOT in `AxiomAudit.lean`; CI_NOT_RUN.
-/

namespace JurisLean.Mandate.MatrixGame

open JurisLean.Mandate.Kernel

/-- Payoff cells: the row player picks the first index, the column player the second. -/
def lower (a b c d : Nat) : Nat := max (min a b) (min c d)

/-- What the column player can hold the row player down to. -/
def upper (a b c d : Nat) : Nat := min (max a c) (max b d)

/-- Moving first guarantees no more than the opponent's concession bound. -/
theorem lower_le_upper (a b c d : Nat) : lower a b c d ≤ upper a b c d := by
  show max (min a b) (min c d) ≤ min (max a c) (max b d)
  omega

/-- A pure value exists exactly when the two bounds meet. -/
def hasPureValue (a b c d : Nat) : Bool := decide (lower a b c d = upper a b c d)

/-- The test is correct, not just executable: it says true exactly when the bounds meet. -/
theorem hasPureValue_true_iff (a b c d : Nat) :
    hasPureValue a b c d = true ↔ lower a b c d = upper a b c d := by
  exact ⟨fun h => of_decide_eq_true h, fun h => decide_eq_true h⟩

/-- Matching pennies: the two bounds differ by one, strictly. -/
theorem pennies_gap_strict : lower 1 0 0 1 < upper 1 0 0 1 := by decide

theorem pennies_no_pure_value : hasPureValue 1 0 0 1 = false := by decide

/-- A coordination position does have a pure value, so the test is not a constant. -/
theorem coordination_has_pure_value : hasPureValue 2 2 1 3 = true := by decide

/--
The bounds are the extremes they claim to be: raising the row player's best
cell in the first row cannot lower what the row player can guarantee.
-/
theorem lower_monotone_first (a b c d x : Nat) (h : a ≤ x) :
    lower a b c d ≤ lower x b c d := by
  show max (min a b) (min c d) ≤ max (min x b) (min c d)
  omega

/-- Symmetrically, conceding more to the column player cannot lower the bound. -/
theorem upper_monotone_column (a b c d y : Nat) (h : d ≤ y) :
    upper a b c d ≤ upper a b c y := by
  show min (max a c) (max b d) ≤ min (max a c) (max b y)
  have h1 : max b d ≤ max b y := by omega
  omega

/-- The gap is bounded by the matrix spread, so "almost a saddle point" is measurable. -/
theorem gap_bounded_by_spread (a b c d : Nat) :
    upper a b c d - lower a b c d ≤ max (max a b) (max c d) - min (min a b) (min c d) := by
  have h := lower_le_upper a b c d
  -- The two bounds stay opaque atoms at the end, which is what makes the last step
  -- linear arithmetic; each is unfolded only inside its own `show`.
  have hhi : upper a b c d ≤ max (max a b) (max c d) := by
    show min (max a c) (max b d) ≤ max (max a b) (max c d)
    omega
  have hlo : min (min a b) (min c d) ≤ lower a b c d := by
    show min (min a b) (min c d) ≤ max (min a b) (min c d)
    omega
  omega

end JurisLean.Mandate.MatrixGame
