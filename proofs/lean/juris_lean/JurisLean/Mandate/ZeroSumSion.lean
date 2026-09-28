import Mathlib

/-!
# Mandate module — the mixed-strategy carrier for the zero-sum minimax arm (R-03)

The audit's judgement on the game-theory mandate item is that the repository proved a
pure-strategy value for two-player zero-sum matrices (`MatrixGame.lean`) and one mixed
equilibrium by exhaustion (`MixedPennies.lean`, over `ℚ`), but had no route to the
general finite zero-sum statement, and the papers promise never to claim Nash existence.

This module opens that route against the carrier the pinned Mathlib actually ships. Two
premises written in the ledger earlier were wrong and are corrected here by source:

* there is no `Probability.Simplex` in this pin — `Mathlib/Probability/` has no
  `Simplex.lean`; the simplex is `stdSimplex : Set (ι → 𝕜)`
  (`Mathlib/Analysis/Convex/StdSimplex.lean:35`);
* the usable public statement is `Sion.exists_isSaddlePointOn`
  (`Mathlib/Topology/Sion.lean:539`, the `Real` section), not its primed internal
  predecessor `exists_isSaddlePointOn'` that the ledger first named.

`Sion.exists_isSaddlePointOn` is ℝ-valued, while the two attested game modules are `ℚ`
valued, so this module defines its own payoff over `ℝ`. The two scopes stay separate in
prose: `MixedPennies` is one computed game, and a Sion instance would be a statement
about every finite zero-sum game. Neither is read as general Nash existence, which has no
carrier in this pin at all.

This round lands only the carrier and its three elementary shape facts, all of them
quoted from source text rather than recalled: the non-negativity-and-total-one set is
nonempty, compact and convex. The (quasi)convexity of the payoff in the row mixture, the
(quasi)concavity in the column mixture, the semicontinuity of both slices, and the
Sion application itself are the next rounds. Nothing here is yet a minimax claim.
-/

namespace JurisLean.Mandate.ZeroSumSion

open BigOperators Finset

/-- The row player's expected payoff in an `(m+1) × (n+1)` zero-sum game with matrix `A`,
at mixed strategies `p` and `q`. Indexing by `Fin (m+1)` rather than `Fin m` keeps the
strategy set nonempty, which is a hypothesis of the minimax theorem, not a detail. -/
def payoff {m n : ℕ} (A : Fin (m+1) → Fin (n+1) → ℝ)
    (p : Fin (m+1) → ℝ) (q : Fin (n+1) → ℝ) : ℝ :=
  ∑ i, ∑ j, p i * A i j * q j

/-- A mixed row strategy exists: the uniform distribution over the `m+1` options. -/
theorem mixRight_nonempty (m : ℕ) : (stdSimplex ℝ (Fin (m+1))).Nonempty := by
  refine ⟨fun _ => ((m + 1 : ℕ) : ℝ)⁻¹, fun i => by positivity, ?_⟩
  rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Fintype.card_fin]
  push_cast
  field_simp

/-- A mixed column strategy exists; the same term one dimension over. -/
theorem mixLeft_nonempty (n : ℕ) : (stdSimplex ℝ (Fin (n+1))).Nonempty :=
  mixRight_nonempty n

/-- The mixed row strategy set is compact, which is the side the theorem puts the
hypothesis on. -/
theorem mixRight_isCompact (m : ℕ) : IsCompact (stdSimplex ℝ (Fin (m+1))) :=
  isCompact_stdSimplex ℝ (Fin (m+1))

/-- The mixed column strategy set is compact. -/
theorem mixLeft_isCompact (n : ℕ) : IsCompact (stdSimplex ℝ (Fin (n+1))) :=
  isCompact_stdSimplex ℝ (Fin (n+1))

/-- Both strategy sets are convex, so a mixture of two mixtures is a mixture. -/
theorem mixRight_convex (m : ℕ) : Convex ℝ (stdSimplex ℝ (Fin (m+1))) :=
  convex_stdSimplex ℝ (Fin (m+1))

/-- The column side is convex as well. -/
theorem mixLeft_convex (n : ℕ) : Convex ℝ (stdSimplex ℝ (Fin (n+1))) :=
  convex_stdSimplex ℝ (Fin (n+1))

/-- A convex combination of two row mixtures stays coordinatewise nonnegative. Stated
separately because the combination is the term the minimax hypotheses actually talk
about. -/
theorem combo_nonneg {m : ℕ} (p p' : Fin (m+1) → ℝ) (a b : ℝ)
    (hp : ∀ i, 0 ≤ p i) (hp' : ∀ i, 0 ≤ p' i) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    ∀ i, 0 ≤ a * p i + b * p' i := fun i => add_nonneg (mul_nonneg ha (hp i)) (mul_nonneg hb (hp' i))

end JurisLean.Mandate.ZeroSumSion
