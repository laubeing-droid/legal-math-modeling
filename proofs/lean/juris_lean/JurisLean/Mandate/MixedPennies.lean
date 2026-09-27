import Mathlib

/-!
# Mandate module — a mixed-strategy equilibrium, proved for one game

The audit's judgement on the game-theory mandate item (R-02a/R-02b/R-03) was that the
repository had a pure-strategy value for two-player zero-sum matrices but nothing about
mixed strategies, and the papers promised never to claim Nash existence. `MatrixGame.lean`
carries the pure side, and `pennies_no_pure_value` there proves a pure value need not
exist. What was missing is the other half of the sentence: a mixed strategy actually
being *used* somewhere, with a proof.

This module supplies one such case, for matching pennies. The mixture is a rational
probability `p` on heads for the row player and `q` for the column player; the expected
payoff `u p q` is derived from the four matrix cells, and the pair `p = q = 1/2` is
proved to be a Nash equilibrium of the mixed game -- each side held to the value `0` by
the other's mixture, for **every** alternative mixture, not for a sampled grid.

The companion fact is what makes that worth stating: `no_pure_pair_is_equilibrium` proves
no pure pair is an equilibrium of the same game. So this is a game where mixing is
strictly load-bearing, and the theorem is not dressing on a trivial case.

What is deliberately NOT claimed:
* Existence of a mixed equilibrium for some or all finite games. That is Nash's theorem
  and it needs a fixed-point or extreme-value argument over a simplex; one instance is
  not a step towards it in Lean unless the argument is written.
* That matching pennies' value being `0` says anything about play, learning or humans.
* Any statement about games with more than two players, or sequential games.
* Mixed-strategy equilibrium for a *declared* payoff matrix type -- the matrix here is
  this game's, and `u` is computed from it rather than assumed.

Status: awaiting its first CI elaboration. Local Lean is forbidden here, so nothing in
this file is attested until a round builds it.
-/

namespace JurisLean.Mandate.MixedPennies

/-! ## The game -/

/-- Matching pennies: the row player collects `+1` when the coins agree and `-1` when they
do not. Stated by constructor patterns so it computes without any decidability plumbing. -/
def payoff : Bool → Bool → ℚ
  | true, true => 1
  | true, false => -1
  | false, true => -1
  | false, false => 1

/-- The matrix is symmetric, so the same function describes either player's win/loss once
the roles are swapped. Zero-sumness is by construction: the second player collects the
negation of this value, which is why one function is enough. -/
theorem payoff_symm (a b : Bool) : payoff a b = payoff b a := by
  cases a <;> cases b <;> rfl

/-- Expected payoff to the row player when the two coins are independent with probabilities
`p` and `q`: the four cells weighted by their product probabilities. -/
def u (p q : ℚ) : ℚ :=
  p * q * payoff true true + p * (1 - q) * payoff true false
    + (1 - p) * q * payoff false true + (1 - p) * (1 - q) * payoff false false

/-- The expansion the rest of the file works with, discharged by `ring` once the four cells
have computed to numbers. -/
theorem u_eq (p q : ℚ) : u p q = 1 - 2 * p - 2 * q + 4 * p * q := by
  simp only [u, payoff]
  ring

/-- The two constant facts every bound below reduces to. -/
theorem two_half : (2 : ℚ) * (1 / 2) = 1 := by norm_num

theorem four_half : (4 : ℚ) * (1 / 2) = 2 := by norm_num

/-! ## The uniform mixture is an equilibrium -/

/-- The value of the game under the uniform mixture is `0`. -/
theorem value_at_uniform : u (1 / 2) (1 / 2) = 0 := by
  rw [u_eq]
  have h4 : (4 : ℚ) * (1 / 2) * (1 / 2) = (4 * (1 / 2)) * (1 / 2) := by ring
  rw [h4, four_half]
  norm_num

/-- **The column player's uniform mixture holds the row player to the value**, against
every mixture the row player chooses. -/
theorem row_held (p : ℚ) : u p (1 / 2) ≤ u (1 / 2) (1 / 2) := by
  have h1 : u p (1 / 2) = 1 - 2 * p - 2 * (1 / 2) + 4 * p * (1 / 2) := u_eq p (1 / 2)
  have h4 : (4 : ℚ) * p * (1 / 2) = 2 * p := by
    calc (4 : ℚ) * p * (1 / 2) = (4 * (1 / 2)) * p := by ring
      _ = 2 * p := by rw [four_half]
  rw [h1, value_at_uniform]
  linarith [two_half, h4]

/-- **The row player's uniform mixture guarantees the value against every mixture** the
column player chooses. -/
theorem col_guaranteed (q : ℚ) : u (1 / 2) q ≥ u (1 / 2) (1 / 2) := by
  have h1 : u (1 / 2) q = 1 - 2 * (1 / 2) - 2 * q + 4 * (1 / 2) * q := u_eq (1 / 2) q
  have h4 : (4 : ℚ) * (1 / 2) * q = 2 * q := by
    calc (4 : ℚ) * (1 / 2) * q = (4 * (1 / 2)) * q := by ring
      _ = 2 * q := by rw [four_half]
  rw [h1, value_at_uniform]
  linarith [two_half, h4]

/-- The two halves together: the uniform pair is a mixed-strategy Nash equilibrium of
matching pennies, with value `0`. Quantified over **all** rational mixtures of each
player, not over a grid. -/
theorem mixedNash_uniform :
    (∀ p : ℚ, u p (1 / 2) ≤ u (1 / 2) (1 / 2)) ∧
      (∀ q : ℚ, u (1 / 2) q ≥ u (1 / 2) (1 / 2)) :=
  ⟨row_held, col_guaranteed⟩

/-- Both components really are probabilities. -/
theorem uniform_is_a_mixture : 0 ≤ (1 / 2 : ℚ) ∧ (1 / 2 : ℚ) ≤ 1 := by
  norm_num

/-! ## And no pure pair is one -/

/--
Whichever pure pair is proposed, **at least one** player strictly prefers to deviate: when
the coins agree the row player is content and the column player wants to flip, and when
they differ it is the reverse. That is the shape of matching pennies, and it is why the
mixed result above is not dressing on a trivial case.

The stronger-sounding version -- that *both* players want to flip at every pair -- is
false, and `decide` proved it so in run 36347838507: at `(heads, heads)` the row player
already collects `+1` and has no profitable deviation. The disjunction below is what
"no pure pair is a Nash equilibrium" actually means.

A second named fact I added beside it -- that when the coins differ the first player can
gain -- was also wrong, and `decide` rejected it again in run 36349847602: I had written
the baseline as `payoff b b`, which is the agreeing cell worth `+1`, so no deviation can
beat it. It is removed rather than patched blind, because a hand-written instance of
exactly the asymmetry this game turns on is what the second attempt got wrong twice;
`agreed_second_moves` survives, being the direction whose baseline is genuinely the
agreeing cell.
-/
theorem no_pure_pair_is_equilibrium :
    ∀ a b : Bool, (∃ a' : Bool, payoff a' b > payoff a b) ∨
      (∃ b' : Bool, payoff a b' < payoff a b) := by decide

/-- When the coins agree, it is the second player who strictly prefers to flip. -/
theorem agreed_second_moves (a : Bool) : ∃ b' : Bool, payoff a b' < payoff a a :=
  ⟨not a, by cases a <;> decide⟩

end JurisLean.Mandate.MixedPennies
