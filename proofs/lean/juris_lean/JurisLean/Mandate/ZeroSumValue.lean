import Mathlib
import JurisLean.Mandate.ZeroSumSion

/-!
# Mandate module — the minimax VALUE equality for finite zero-sum matrix games (R-03, value step)

`JurisLean.Mandate.ZeroSumSion` proves `exists_saddlePoint`: every `(m+1) × (n+1)` real matrix `A`
has a saddle point `(a, b)` in mixed strategies. A saddle point is not yet a value. This module
supplies the missing step: the two iterated values

    ⨅ p : X, ⨆ q : Y, payoff A p q        (upper value)
    ⨆ q : Y, ⨅ p : X, payoff A p q        (lower value)

exist as conditionally complete infimum and supremum, both equal the saddle payoff `payoff A a b`
(`upperValue_eq_payoff`, `lowerValue_eq_payoff`), and therefore coincide (`value_eq`, with the
common value made explicit in `exists_value`). Separately, `weakDuality` proves
`lower value ≤ upper value` for an arbitrary payoff on bounded sets, using no Sion and no fixed
point, so a reader can see which half of the equality is the theorem and which half is order
theory.

**Why not `isSaddlePointOn_value`.** The library result
`Mathlib/Order/SaddlePoint.lean:102 isSaddlePointOn_value` states exactly this content, but over a
`CompleteLinearOrder β`. This pin gives `ℝ` only `ConditionallyCompleteLinearOrder`
(`Mathlib/Data/Real/Archimedean.lean:140`), and no complete-lattice instance for the reals, so
neither that lemma nor the complete-lattice `iSup₂`/`iInf₂` API
(`Mathlib/Order/SaddlePoint.lean:35 iSup₂_iInf₂_le_iInf₂_iSup₂` has the same hypothesis) can be
used at `β := ℝ`.

**Why the binder is `p : X` and not `p ∈ X`.** `⨅ p ∈ X, f p` is the iterated infimum
`⨅ p, ⨅ (hp : p ∈ X), f p`: `p` ranges over the whole ambient type, and a
`p ∉ X` contributes an infimum over an empty index type. For `ℝ` those junk cases are *defined* to
be `0` — `Mathlib/Data/Real/Archimedean.lean:195 Real.sInf_empty`, `:171 Real.sSup_empty`, giving
`:197 Real.iInf_of_isEmpty` and `:177 Real.iSup_of_isEmpty`. Neither simplex is the whole function
type, so `⨆ q ∈ Y, payoff A p q` reads `max (row supremum) 0` and the enclosing `⨅ p ∈ X` then
takes a minimum with `0`: for *every* matrix both sides come out `0`, and the requested equation
would state nothing at all. Mathlib's conditionally complete API indexes over the subtype for the
same reason (`Mathlib/Order/ConditionallyCompleteLattice/Indexed.lean:95 isLUB_ciSup_set`,
`:116 ciSup_set_le_iff`, `:179 le_ciSup_set`, `:225 ciInf_set_le`). `⨅ p : X, ⨆ q : Y, payoff A p q`
is therefore written here as an infimum over a nonempty compact set of a bounded image, which is
the upper value a game theory text means. This is a change of notation to keep the content, not a
weakening of the claim.

**Status.** No verdict is claimed for this file. It was written and booked in
`PENDING_CI_MODULES` unelaborated, and run 36401817896 then printed
`Built JurisLean.Mandate.ZeroSumValue` on its first attempt at a compiler. That line is the
kernel's own output and it is not a verdict: the round ended `failure` on two other mandate
modules, and a red round publishes no certificate and no acceptance, so this module stays
booked and out of the release root until a green round. It is named by the generated audit
surface, which is where that first build happened. Nothing in this file is an attestation, and
local text pre-checks are not Lean evidence. What
*is* attested is the carrier consumed here: the four shape facts imported from `ZeroSumSion`
(`mixRight_nonempty`, `mixLeft_nonempty`, `mixRight_isCompact`, `mixLeft_isCompact`) ran green in
run 36365128114, whose recorded commit is `e9abf6a`, and `exists_saddlePoint` in run 36372895460
(recorded commit `fea48d9`). Those two verdicts belong to `ZeroSumSion` and to the versions of it
those commits carried. A verdict does not travel to a file that did not exist where it was
recorded, which is also why the `Built` line above is tied to this file's own commit. `value_eq` is an existence statement
about two iterated values of the payoff: it computes no value, it says nothing about pure
strategies, and it is silent on non-zero-sum and multiplayer games, which still have no carrier in
this pin.
-/

namespace JurisLean.Mandate.ZeroSumValue

open BigOperators Finset
open JurisLean.Mandate.ZeroSumSion

/-! ## 1. The two payoff slices are continuous

`ZeroSumSion` exposes only the semicontinuity of each slice (`lsc_payoff_left`,
`usc_payoff_right`). Boundedness of a payoff on a simplex needs plain continuity, so the two
slice arguments are repeated here, using the same terms the Sion module already runs inside
those two semicontinuity proofs. -/

/-- Held to any column mixture, the row player's payoff is continuous in the row mixture. -/
theorem continuous_payoff_left {m n : ℕ} (A : Fin (m+1) → Fin (n+1) → ℝ) (q : Fin (n+1) → ℝ) :
    Continuous (fun p : Fin (m+1) → ℝ => payoff A p q) := by
  show Continuous (fun p : Fin (m+1) → ℝ =>
    ∑ i ∈ Finset.univ, ∑ j ∈ Finset.univ, p i * A i j * q j)
  refine continuous_finsetSum Finset.univ fun i _ => ?_
  refine continuous_finsetSum Finset.univ fun j _ => ?_
  exact ((continuous_apply i).mul continuous_const).mul continuous_const

/-- Held to any row mixture, the payoff is continuous in the column mixture. -/
theorem continuous_payoff_right {m n : ℕ} (A : Fin (m+1) → Fin (n+1) → ℝ) (p : Fin (m+1) → ℝ) :
    Continuous (fun q : Fin (n+1) → ℝ => payoff A p q) := by
  show Continuous (fun q : Fin (n+1) → ℝ =>
    ∑ i ∈ Finset.univ, ∑ j ∈ Finset.univ, p i * A i j * q j)
  refine continuous_finsetSum Finset.univ fun i _ => ?_
  refine continuous_finsetSum Finset.univ fun j _ => ?_
  exact (continuous_const.mul continuous_const).mul (continuous_apply j)

/-! ## 2. Boundedness: a payoff on a compact simplex has bounded image

Each of the four facts is one compactness statement plus one continuity statement. They are what
turns the conditionally complete `⨅`/`⨆` into a value rather than a junk number. -/

/-- At a fixed row mixture the payoff is bounded above on the compact column simplex. -/
theorem bddAbove_payoff_right {m n : ℕ} (A : Fin (m+1) → Fin (n+1) → ℝ)
    (p : Fin (m+1) → ℝ) :
    BddAbove ((fun q => payoff A p q) '' stdSimplex ℝ (Fin (n+1))) :=
  (mixLeft_isCompact n).bddAbove_image (continuous_payoff_right A p).continuousOn

/-- At a fixed row mixture the payoff is bounded below on the compact column simplex. -/
theorem bddBelow_payoff_right {m n : ℕ} (A : Fin (m+1) → Fin (n+1) → ℝ)
    (p : Fin (m+1) → ℝ) :
    BddBelow ((fun q => payoff A p q) '' stdSimplex ℝ (Fin (n+1))) :=
  (mixLeft_isCompact n).bddBelow_image (continuous_payoff_right A p).continuousOn

/-- At a fixed column mixture the payoff is bounded below on the compact row simplex. -/
theorem bddBelow_payoff_left {m n : ℕ} (A : Fin (m+1) → Fin (n+1) → ℝ) (q : Fin (n+1) → ℝ) :
    BddBelow ((fun p => payoff A p q) '' stdSimplex ℝ (Fin (m+1))) :=
  (mixRight_isCompact m).bddBelow_image (continuous_payoff_left A q).continuousOn

/-- At a fixed column mixture the payoff is bounded above on the compact row simplex. -/
theorem bddAbove_payoff_left {m n : ℕ} (A : Fin (m+1) → Fin (n+1) → ℝ) (q : Fin (n+1) → ℝ) :
    BddAbove ((fun p => payoff A p q) '' stdSimplex ℝ (Fin (m+1))) :=
  (mixRight_isCompact m).bddAbove_image (continuous_payoff_left A q).continuousOn

/-! ## 3. Weak duality, with no minimax input -/

/-- **Weak duality.** For any payoff `f` on any two sets `X` and `Y`, provided each row image is
bounded above and each column image is bounded below, the lower value never exceeds the upper
value. The proof is order theory only: two points of the two sets, the bounds they carry, and the
conditionally complete `ciSup_set_le_iff` / `le_ciInf_set_iff` / `ciInf_set_le` / `le_ciSup_set`.
No saddle point, no Sion, no fixed point. -/
theorem weakDuality {E F : Type*} {X : Set E} {Y : Set F} (f : E → F → ℝ)
    (a : E) (ha : a ∈ X) (b : F) (hb : b ∈ Y)
    (hrow : ∀ p ∈ X, BddAbove ((fun q => f p q) '' Y))
    (hcol : ∀ q ∈ Y, BddBelow ((fun p => f p q) '' X)) :
    ⨆ q : Y, ⨅ p : X, f p q ≤ ⨅ p : X, ⨆ q : Y, f p q := by
  have hX : X.Nonempty := ⟨a, ha⟩
  have hY : Y.Nonempty := ⟨b, hb⟩
  -- The column infima are bounded above *uniformly*, because each one sits under row `a`, whose
  -- own image is bounded.
  have hC : BddAbove ((fun q => ⨅ p : X, f p q) '' Y) := by
    obtain ⟨M, hM⟩ := bddAbove_def.mp (hrow a ha)
    refine bddAbove_def.mpr ⟨M, ?_⟩
    rintro _ ⟨q, hq, rfl⟩
    exact le_trans (ciInf_set_le (hcol q hq) ha)
      (hM _ (Set.mem_image_of_mem (fun q => f a q) hq))
  -- Dually the row suprema are bounded below uniformly, through column `b`.
  have hG : BddBelow ((fun p => ⨆ q : Y, f p q) '' X) := by
    obtain ⟨m, hm⟩ := bddBelow_def.mp (hcol b hb)
    refine bddBelow_def.mpr ⟨m, ?_⟩
    rintro _ ⟨p, hp, rfl⟩
    exact le_trans (hm _ (Set.mem_image_of_mem (fun p => f p b) hp))
      (le_ciSup_set (hrow p hp) hb)
  refine (ciSup_set_le_iff hY hC).mpr ?_
  intro q hq
  refine (le_ciInf_set_iff hX hG).mpr ?_
  intro p hp
  exact (ciInf_set_le (hcol q hq) hp).trans (le_ciSup_set (hrow p hp) hq)

/-- Weak duality for the matrix game. Both boundedness hypotheses are the compact-simplex images of
section 2, so this corollary needs neither `exists_saddlePoint` nor any choice of matrix. -/
theorem lowerValue_le_upperValue (m n : ℕ) (A : Fin (m+1) → Fin (n+1) → ℝ) :
    ⨆ q : (stdSimplex ℝ (Fin (n+1))), ⨅ p : (stdSimplex ℝ (Fin (m+1))), payoff A p q
      ≤ ⨅ p : (stdSimplex ℝ (Fin (m+1))), ⨆ q : (stdSimplex ℝ (Fin (n+1))), payoff A p q := by
  obtain ⟨a, ha⟩ := mixRight_nonempty m
  obtain ⟨b, hb⟩ := mixLeft_nonempty n
  refine weakDuality (payoff A) a ha b hb ?_ ?_
  · intro p hp
    exact bddAbove_payoff_right A p
  · intro q hq
    exact bddBelow_payoff_left A q

/-! ## 4. The saddle point identifies both iterated values -/

/-- At a saddle point, holding the row at `a`, the column player's best reply attains the supremum:
`⨆ q : Y, payoff A a q = payoff A a b`. The inequality one way is the saddle property; the other
way is `le_ciSup_set` at the column `b`, which is where boundedness of the column simplex enters. -/
theorem ciSup_payoff_row_eq {m n : ℕ} (A : Fin (m+1) → Fin (n+1) → ℝ)
    (a : Fin (m+1) → ℝ) (b : Fin (n+1) → ℝ)
    (ha : a ∈ stdSimplex ℝ (Fin (m+1))) (hb : b ∈ stdSimplex ℝ (Fin (n+1)))
    (h : IsSaddlePointOn (stdSimplex ℝ (Fin (m+1))) (stdSimplex ℝ (Fin (n+1))) (payoff A) a b) :
    ⨆ q : (stdSimplex ℝ (Fin (n+1))), payoff A a q = payoff A a b := by
  refine le_antisymm
    ((ciSup_set_le_iff (mixLeft_nonempty n) (bddAbove_payoff_right A a)).mpr fun q hq => ?_)
    (le_ciSup_set (bddAbove_payoff_right A a) hb)
  exact h a ha q hq

/-- Dually, holding the column at `b`, the row player's best reply attains the infimum:
`⨅ p : X, payoff A p b = payoff A a b`. -/
theorem ciInf_payoff_col_eq {m n : ℕ} (A : Fin (m+1) → Fin (n+1) → ℝ)
    (a : Fin (m+1) → ℝ) (b : Fin (n+1) → ℝ)
    (ha : a ∈ stdSimplex ℝ (Fin (m+1))) (hb : b ∈ stdSimplex ℝ (Fin (n+1)))
    (h : IsSaddlePointOn (stdSimplex ℝ (Fin (m+1))) (stdSimplex ℝ (Fin (n+1))) (payoff A) a b) :
    ⨅ p : (stdSimplex ℝ (Fin (m+1))), payoff A p b = payoff A a b := by
  refine le_antisymm (ciInf_set_le (bddBelow_payoff_left A b) ha)
    ((le_ciInf_set_iff (mixRight_nonempty m) (bddBelow_payoff_left A b)).mpr fun p hp => ?_)
  exact h p hp b hb

/-- **The upper value is the saddle payoff.** `⨅ p : X, ⨆ q : Y, payoff A p q = payoff A a b`. -/
theorem upperValue_eq_payoff {m n : ℕ} (A : Fin (m+1) → Fin (n+1) → ℝ)
    (a : Fin (m+1) → ℝ) (b : Fin (n+1) → ℝ)
    (ha : a ∈ stdSimplex ℝ (Fin (m+1))) (hb : b ∈ stdSimplex ℝ (Fin (n+1)))
    (h : IsSaddlePointOn (stdSimplex ℝ (Fin (m+1))) (stdSimplex ℝ (Fin (n+1))) (payoff A) a b) :
    ⨅ p : (stdSimplex ℝ (Fin (m+1))), ⨆ q : (stdSimplex ℝ (Fin (n+1))), payoff A p q
      = payoff A a b := by
  -- The saddle payoff bounds the row-supremum function below: at every row `p`, the column `b`
  -- already gives `payoff A a b ≤ payoff A p b`, and `b` is a column, so its value is under the
  -- supremum over the column simplex.
  have hbd : BddBelow ((fun p => ⨆ q : (stdSimplex ℝ (Fin (n+1))), payoff A p q)
      '' stdSimplex ℝ (Fin (m+1))) := by
    refine bddBelow_def.mpr ⟨payoff A a b, ?_⟩
    rintro _ ⟨p, hp, rfl⟩
    exact le_trans (h p hp b hb) (le_ciSup_set (bddAbove_payoff_right A p) hb)
  refine le_antisymm ?_ ((le_ciInf_set_iff (mixRight_nonempty m) hbd).mpr fun p hp => ?_)
  · -- `ciInf_set_le` stops at the row supremum of `a`; `ciSup_payoff_row_eq` turns that into
    -- the saddle payoff.
    exact (ciInf_set_le hbd ha).trans (le_of_eq (ciSup_payoff_row_eq A a b ha hb h))
  · exact le_trans (h p hp b hb) (le_ciSup_set (bddAbove_payoff_right A p) hb)

/-- **The lower value is the saddle payoff.**
`⨆ q : Y, ⨅ p : X, payoff A p q = payoff A a b`. -/
theorem lowerValue_eq_payoff {m n : ℕ} (A : Fin (m+1) → Fin (n+1) → ℝ)
    (a : Fin (m+1) → ℝ) (b : Fin (n+1) → ℝ)
    (ha : a ∈ stdSimplex ℝ (Fin (m+1))) (hb : b ∈ stdSimplex ℝ (Fin (n+1)))
    (h : IsSaddlePointOn (stdSimplex ℝ (Fin (m+1))) (stdSimplex ℝ (Fin (n+1))) (payoff A) a b) :
    ⨆ q : (stdSimplex ℝ (Fin (n+1))), ⨅ p : (stdSimplex ℝ (Fin (m+1))), payoff A p q
      = payoff A a b := by
  -- The saddle payoff bounds the column-infimum function above, because at every column `q` the
  -- row `a` already gives `payoff A a q ≤ payoff A a b`.
  have hbd : BddAbove ((fun q => ⨅ p : (stdSimplex ℝ (Fin (m+1))), payoff A p q)
      '' stdSimplex ℝ (Fin (n+1))) := by
    refine bddAbove_def.mpr ⟨payoff A a b, ?_⟩
    rintro _ ⟨q, hq, rfl⟩
    exact le_trans (ciInf_set_le (bddBelow_payoff_left A q) ha) (h a ha q hq)
  have hle : payoff A a b ≤ ⨅ p : (stdSimplex ℝ (Fin (m+1))), payoff A p b :=
    (le_ciInf_set_iff (mixRight_nonempty m) (bddBelow_payoff_left A b)).mpr fun p hp =>
      h p hp b hb
  have hge : payoff A a b ≤ ⨆ q : (stdSimplex ℝ (Fin (n+1))),
      ⨅ p : (stdSimplex ℝ (Fin (m+1))), payoff A p q := le_trans hle (le_ciSup_set hbd hb)
  refine le_antisymm
    ((ciSup_set_le_iff (mixLeft_nonempty n) hbd).mpr fun q hq =>
      le_trans (ciInf_set_le (bddBelow_payoff_left A q) ha) (h a ha q hq))
    hge

/-! ## 5. The value equality -/

/-- The non-trivial half: the upper value is at most the lower value. Every step consumes the
saddle point that `exists_saddlePoint` supplies; the reverse inequality is `weakDuality`
(`lowerValue_le_upperValue`), which needs no such point. -/
theorem upperValue_le_lowerValue (m n : ℕ) (A : Fin (m+1) → Fin (n+1) → ℝ) :
    ⨅ p : (stdSimplex ℝ (Fin (m+1))), ⨆ q : (stdSimplex ℝ (Fin (n+1))), payoff A p q
      ≤ ⨆ q : (stdSimplex ℝ (Fin (n+1))), ⨅ p : (stdSimplex ℝ (Fin (m+1))), payoff A p q := by
  obtain ⟨a, ha, b, hb, h⟩ := exists_saddlePoint m n A
  exact le_of_eq ((upperValue_eq_payoff A a b ha hb h).trans
    (lowerValue_eq_payoff A a b ha hb h).symm)

/-- **Minimax value equality for finite zero-sum matrix games over `ℝ`.** The upper and the lower
value coincide. This is the statement `exists_saddlePoint` did not give, and the statement
`Mathlib/Order/SaddlePoint.lean:102 isSaddlePointOn_value` cannot give here because it demands
`CompleteLinearOrder β`, which `ℝ` does not have. -/
theorem value_eq (m n : ℕ) (A : Fin (m+1) → Fin (n+1) → ℝ) :
    (⨅ p : (stdSimplex ℝ (Fin (m+1))), ⨆ q : (stdSimplex ℝ (Fin (n+1))), payoff A p q)
      = (⨆ q : (stdSimplex ℝ (Fin (n+1))), ⨅ p : (stdSimplex ℝ (Fin (m+1))), payoff A p q) :=
  le_antisymm (upperValue_le_lowerValue m n A) (lowerValue_le_upperValue m n A)

/-- The game has a value, and it is the payoff at any saddle point: both iterated values equal
`payoff A a b`. -/
theorem exists_value (m n : ℕ) (A : Fin (m+1) → Fin (n+1) → ℝ) :
    ∃ v : ℝ,
      (⨅ p : (stdSimplex ℝ (Fin (m+1))), ⨆ q : (stdSimplex ℝ (Fin (n+1))), payoff A p q = v) ∧
        (⨆ q : (stdSimplex ℝ (Fin (n+1))), ⨅ p : (stdSimplex ℝ (Fin (m+1))), payoff A p q = v) := by
  obtain ⟨a, ha, b, hb, h⟩ := exists_saddlePoint m n A
  exact ⟨payoff A a b, upperValue_eq_payoff A a b ha hb h, lowerValue_eq_payoff A a b ha hb h⟩

/-!
**What this module does not claim.** `value_eq` names no number: it says the two iterated values
of `payoff A` over the two mixed-strategy simplices are equal, and `exists_value` identifies them
with the payoff at a saddle point whose existence came from Sion. It is not a computation, not an
algorithm, and not a value for a particular game — the single computed `ℚ`-valued game in
`MixedPennies.lean` stays a separate carrier with a separate scope. Nothing here touches Nash
existence for non-zero-sum or multiplayer games, for which this pin still has no carrier, and no
claim in this file is an attestation: `Mandate/ZeroSumValue.lean` has been elaborated once, inside
a round that failed for other reasons, and no green round has certified it.
-/

end JurisLean.Mandate.ZeroSumValue
