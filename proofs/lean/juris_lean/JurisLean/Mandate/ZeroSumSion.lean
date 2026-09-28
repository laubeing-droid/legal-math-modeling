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

The carrier is attested: the shape facts below -- both strategy sets nonempty, compact and
convex, and a mixture staying coordinatewise nonnegative -- built green in run 36365128114
at subject `e9abf6a`. The linearity of the payoff in each mixture, the (quasi)convexity and
(quasi)concavity that follow from it, the semicontinuity of both slices, and the Sion
application that consumes all ten hypotheses were written after that attestation and are
attested by run 36372895460 at subject `fea48d9`, whose `lean-full-clean-build` elaborated the
fourteen targets that version of this file had -- a count of that subject, not of the text below,
which has since grown. `exists_saddlePoint` is therefore a proved statement about every
finite two-player zero-sum game -- and nothing wider: it says nothing about non-zero-sum or
multiplayer games, which still have no carrier in this pin. The module joins the release
root in `d0b3506`, and that entry is what run 36376522559 at subject `78f627f` built green:
the instance attestation and the root-entry attestation are therefore two different subjects, and
neither inherits to a later commit. The value equality `iInf iSup = iSup iInf` is NOT claimed
here: `Order/SaddlePoint.lean:102 isSaddlePointOn_value` would give it, but it demands
`CompleteLinearOrder beta`, and this pin has no such instance for the reals.
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

/-! ## The payoff is linear in each mixture separately -/

/-- Mixing two row mixtures before computing the expected payoff equals mixing the two
numbers afterwards. This is the exact content the minimax hypotheses need as (quasi)convexity. -/
theorem payoff_comb_left {m n : ℕ} (A : Fin (m+1) → Fin (n+1) → ℝ) (q : Fin (n+1) → ℝ)
    (p p' : Fin (m+1) → ℝ) (a b : ℝ) :
    payoff A (a • p + b • p') q = a * payoff A p q + b * payoff A p' q := by
  simp only [payoff, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have h1 : (∑ i : Fin (m+1), ∑ j : Fin (n+1), (a * p i + b * p' i) * A i j * q j)
      = ∑ i : Fin (m+1), ∑ j : Fin (n+1),
        (a * (p i * A i j * q j) + b * (p' i * A i j * q j)) := by
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  have h2 : (∑ i : Fin (m+1), ∑ j : Fin (n+1),
      (a * (p i * A i j * q j) + b * (p' i * A i j * q j)))
      = a * ∑ i : Fin (m+1), ∑ j : Fin (n+1), p i * A i j * q j
        + b * ∑ i : Fin (m+1), ∑ j : Fin (n+1), p' i * A i j * q j := by
    simp_rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [h1, h2]

/-- The same statement on the other side: the column mixture enters linearly as well. -/
theorem payoff_comb_right {m n : ℕ} (A : Fin (m+1) → Fin (n+1) → ℝ) (p : Fin (m+1) → ℝ)
    (q q' : Fin (n+1) → ℝ) (a b : ℝ) :
    payoff A p (a • q + b • q') = a * payoff A p q + b * payoff A p q' := by
  simp only [payoff, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have h1 : (∑ i : Fin (m+1), ∑ j : Fin (n+1), p i * A i j * (a * q j + b * q' j))
      = ∑ i : Fin (m+1), ∑ j : Fin (n+1),
        (a * (p i * A i j * q j) + b * (p i * A i j * q' j)) := by
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  have h2 : (∑ i : Fin (m+1), ∑ j : Fin (n+1),
      (a * (p i * A i j * q j) + b * (p i * A i j * q' j)))
      = a * ∑ i : Fin (m+1), ∑ j : Fin (n+1), p i * A i j * q j
        + b * ∑ i : Fin (m+1), ∑ j : Fin (n+1), p i * A i j * q' j := by
    simp_rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [h1, h2]

/-! ## The four hypotheses Sion asks for, discharged -/

/-- Held to any column mixture, the row player's payoff is quasiconvex on the row simplex: a
mixture of two rows is no worse than the worse of them. -/
theorem quasiconvexOn_payoff_left {m n : ℕ} (A : Fin (m+1) → Fin (n+1) → ℝ)
    (q : Fin (n+1) → ℝ) :
    QuasiconvexOn ℝ (stdSimplex ℝ (Fin (m+1))) fun p => payoff A p q := by
  refine quasiconvexOn_iff_le_max.mpr ⟨convex_stdSimplex ℝ (Fin (m+1)), ?_⟩
  intro p _ p' _ a b ha hb hab
  have h1 := payoff_comb_left A q p p' a b
  rw [h1]
  have hX : payoff A p q ≤ max (payoff A p q) (payoff A p' q) := le_max_left _ _
  have hY : payoff A p' q ≤ max (payoff A p q) (payoff A p' q) := le_max_right _ _
  calc a * payoff A p q + b * payoff A p' q
      ≤ a * max (payoff A p q) (payoff A p' q) + b * max (payoff A p q) (payoff A p' q) :=
        add_le_add (mul_le_mul_of_nonneg_left hX ha) (mul_le_mul_of_nonneg_left hY hb)
    _ = (a + b) * max (payoff A p q) (payoff A p' q) := (add_mul a b _).symm
    _ = max (payoff A p q) (payoff A p' q) := by rw [hab, one_mul]

/-- Held to any row mixture, the payoff is quasiconcave on the column simplex. -/
theorem quasiconcaveOn_payoff_right {m n : ℕ} (A : Fin (m+1) → Fin (n+1) → ℝ)
    (p : Fin (m+1) → ℝ) :
    QuasiconcaveOn ℝ (stdSimplex ℝ (Fin (n+1))) fun q => payoff A p q := by
  refine quasiconcaveOn_iff_min_le.mpr ⟨convex_stdSimplex ℝ (Fin (n+1)), ?_⟩
  intro q _ q' _ a b ha hb hab
  have h1 := payoff_comb_right A p q q' a b
  rw [h1]
  have hX : min (payoff A p q) (payoff A p q') ≤ payoff A p q := min_le_left _ _
  have hY : min (payoff A p q) (payoff A p q') ≤ payoff A p q' := min_le_right _ _
  have h : (a + b) * min (payoff A p q) (payoff A p q')
      ≤ a * payoff A p q + b * payoff A p q' := by
    rw [add_mul]
    exact add_le_add (mul_le_mul_of_nonneg_left hX ha) (mul_le_mul_of_nonneg_left hY hb)
  rwa [hab, one_mul] at h

/-- Every column slice of the payoff is continuous, hence lower semicontinuous on the row
simplex. -/
theorem lsc_payoff_left {m n : ℕ} (A : Fin (m+1) → Fin (n+1) → ℝ) (q : Fin (n+1) → ℝ) :
    LowerSemicontinuousOn (fun p : Fin (m+1) → ℝ => payoff A p q)
      (stdSimplex ℝ (Fin (m+1))) :=
  by
    have hc : Continuous (fun p : Fin (m+1) → ℝ => payoff A p q) := by
      show Continuous (fun p : Fin (m+1) → ℝ =>
        ∑ i ∈ Finset.univ, ∑ j ∈ Finset.univ, p i * A i j * q j)
      refine continuous_finsetSum Finset.univ fun i _ => ?_
      refine continuous_finsetSum Finset.univ fun j _ => ?_
      exact ((continuous_apply i).mul continuous_const).mul continuous_const
    exact (hc.lowerSemicontinuous).lowerSemicontinuousOn _

/-- Every row slice is continuous, hence upper semicontinuous on the column simplex. -/
theorem usc_payoff_right {m n : ℕ} (A : Fin (m+1) → Fin (n+1) → ℝ) (p : Fin (m+1) → ℝ) :
    UpperSemicontinuousOn (fun q : Fin (n+1) → ℝ => payoff A p q)
      (stdSimplex ℝ (Fin (n+1))) :=
  by
    have hc : Continuous (fun q : Fin (n+1) → ℝ => payoff A p q) := by
      show Continuous (fun q : Fin (n+1) → ℝ =>
        ∑ i ∈ Finset.univ, ∑ j ∈ Finset.univ, p i * A i j * q j)
      refine continuous_finsetSum Finset.univ fun i _ => ?_
      refine continuous_finsetSum Finset.univ fun j _ => ?_
      exact (continuous_const.mul continuous_const).mul (continuous_apply j)
    exact (hc.upperSemicontinuous).upperSemicontinuousOn _

/-- **Every finite two-player zero-sum game has a saddle point in mixed strategies.** Ten
hypotheses, all of them discharged above or from the pinned library: the two strategy sets
are nonempty, compact and convex, each slice of the payoff is semicontinuous on the set the
theorem puts the compactness on, and the payoff is quasiconvex in the row mixture and
quasiconcave in the column mixture. -/
theorem exists_saddlePoint (m n : ℕ) (A : Fin (m+1) → Fin (n+1) → ℝ) :
    ∃ a ∈ stdSimplex ℝ (Fin (m+1)), ∃ b ∈ stdSimplex ℝ (Fin (n+1)),
      IsSaddlePointOn (stdSimplex ℝ (Fin (m+1))) (stdSimplex ℝ (Fin (n+1))) (payoff A) a b :=
  Sion.exists_isSaddlePointOn (mixRight_nonempty m) (mixRight_convex m) (mixRight_isCompact m)
    (fun _ _ => lsc_payoff_left A _) (fun _ _ => quasiconvexOn_payoff_left A _)
    (mixLeft_convex n) (mixLeft_nonempty n) (mixLeft_isCompact n)
    (fun _ _ => usc_payoff_right A _) (fun _ _ => quasiconcaveOn_payoff_right A _)

/-! ## A component of Nash existence that does NOT need a fixed point -/

/-- Held to any column mixture, some row mixture is a best response: the row player's payoff
attains its minimum loss over the compact row simplex. This is one of the two halves of a
Nash equilibrium, and it needs only compactness plus semicontinuity -- the argument the
library itself uses inside Sion (`LowerSemicontinuousOn.exists_isMinOn`). -/
theorem exists_bestResponse_left {m n : ℕ} (A : Fin (m+1) → Fin (n+1) → ℝ)
    (q : Fin (n+1) → ℝ) :
    ∃ a ∈ stdSimplex ℝ (Fin (m+1)),
      IsMinOn (fun p => payoff A p q) (stdSimplex ℝ (Fin (m+1))) a :=
  (lsc_payoff_left A q).exists_isMinOn (mixRight_nonempty m) (mixRight_isCompact m)

/-- The same fact in the quantified form a reader of a game theory text expects. -/
theorem bestResponse_left_forall {m n : ℕ} (A : Fin (m+1) → Fin (n+1) → ℝ)
    (q : Fin (n+1) → ℝ) :
    ∃ a ∈ stdSimplex ℝ (Fin (m+1)), ∀ x ∈ stdSimplex ℝ (Fin (m+1)),
      payoff A a q ≤ payoff A x q := by
  obtain ⟨a, ha, h⟩ := exists_bestResponse_left A q
  exact ⟨a, ha, isMinOn_iff.mp h⟩

/-- Dually, held to any row mixture, some column mixture is a best response for the column
player, who minimises the row player's payoff. -/
theorem exists_bestResponse_right {m n : ℕ} (A : Fin (m+1) → Fin (n+1) → ℝ)
    (p : Fin (m+1) → ℝ) :
    ∃ b ∈ stdSimplex ℝ (Fin (n+1)),
      IsMaxOn (fun q => payoff A p q) (stdSimplex ℝ (Fin (n+1))) b :=
  (usc_payoff_right A p).exists_isMaxOn (mixLeft_nonempty n) (mixLeft_isCompact n)

/-- The quantified form on the column side. -/
theorem bestResponse_right_forall {m n : ℕ} (A : Fin (m+1) → Fin (n+1) → ℝ)
    (p : Fin (m+1) → ℝ) :
    ∃ b ∈ stdSimplex ℝ (Fin (n+1)), ∀ y ∈ stdSimplex ℝ (Fin (n+1)),
      payoff A p b ≥ payoff A p y := by
  obtain ⟨b, hb, h⟩ := exists_bestResponse_right A p
  exact ⟨b, hb, isMaxOn_iff.mp h⟩

/-!
**What the four facts above do not buy.** A best response exists for each player separately;
a Nash equilibrium asks for a fixed point of the joint best-response map, and this pin has no
carrier for that step. Checked against the pinned source rather than recalled: there is no
Brouwer fixed-point theorem (grep for `Brouwer` hits only Boolean-algebra and order files),
and the Knaster--Tarski machinery (`Mathlib/Order/FixedPoints.lean:75`, `isFixedPt_lfp`)
applies to monotone self-maps of a complete lattice, which the probability simplex under the
pointwise order is not -- the join of two distributions need not be a distribution. So this
module narrows the gap by one honest step and stops: the repository claims no Nash existence
beyond the zero-sum saddle point above and the single computed game in `MixedPennies.lean`.
-/

end JurisLean.Mandate.ZeroSumSion
