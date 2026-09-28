import Mathlib

/-!
# Mandate module — the first general-game equilibrium object, and a decision procedure for it

The game-theory mandate item (R-02b/R-03) now reads: a pure-strategy value for two-player
zero-sum matrices (`MatrixGame.lean`), one *computed* mixed equilibrium for matching pennies
(`MixedPennies.lean`, over `ℚ`), and a general zero-sum mixed saddle point (`ZeroSumSion.lean`,
over `ℝ`). What was missing is any equilibrium object for a game that is **not** zero-sum: a
bimatrix game with two independent payoff matrices. This module supplies that object at the
one level that is honestly decidable here -- a **pure-strategy** Nash equilibrium -- together
with a decision procedure for its existence, so the repository can answer the question
"does this game have a pure equilibrium?" instead of only asserting it for one hand-picked
pair.

What is new is not the definition but the *procedure*:

* `Game m n` is a bimatrix game with `ℚ` payoffs, so every cell comparison is decidable;
* `isBestResponseRow` / `isBestResponseCol` / `isNashPure` state the equilibrium condition
  over the finite action sets `Fin m` and `Fin n`;
* `decidableNashPure` exhibits a *computable* `Decidable` structure on the search, and
  `nashPureExists` computes the verdict as a `Bool`;
* `nashPureExists_true_iff` / `nashPureExists_false_iff` prove the label correct in both
  directions, so a `true` is a witness and a `false` is a proof of absence -- never a timeout.

Two computed certificates, produced by the same procedure on two fully written-out matrices,
give opposite labels: `coordination_label_true` (a coordination game that has a pure
equilibrium, on both diagonals) and `pennies_label_false` (matching pennies, which has none).
The pair is the evidence that the procedure discriminates rather than returning a constant.
The pennies matrix is the same game whose mixed equilibrium `MixedPennies.lean` proves, so
`matchingPennies_no_pure_equilibrium` is the general-form counterpart of that module's
`no_pure_pair_is_equilibrium`: mixing is load-bearing there, and nothing here replaces it.

The carrier facts this rests on were read out of the pinned source, not recalled. Invoked by
name here: `Fintype.decidableExistsFintype` (`Mathlib/Data/Fintype/Defs.lean:213`), which is
the body of `decidableNashPure`, and `Fintype.decidableForallFintype` (`:209`), which instance
resolution reaches for each best-response quantifier. Those two definitions turn a quantifier
over a `Fintype` into a search over `Finset.univ` and walk it with `Finset.mem_univ` (`:96`),
so the whole procedure is a finite sweep of `Fin m × Fin n` with `ℚ` comparisons at the leaves.
`of_decide_eq_true` and `decide_eq_true` are Lean core, and this repository already uses them
on a `decide`-shaped definition at `MatrixGame.lean:51`. The label lemmas
`Bool.decide_false` / `Bool.of_decide_false` (`Mathlib/Data/Bool/Basic.lean:87` / `:90`) were
deliberately NOT used: their implicit `Decidable` instance would have to come out structurally
equal to the one stored inside `nashPureExists`, and the `iff` plus a `cases` on the `Bool`
needs no such coincidence. The `decide` style follows this repository's own built modules:
`MatrixGame.lean:54`, `FullMath/Action/IncentiveEnumeration.lean:20` and `:42` (which decide
`∀ t ∈ Finset.univ` inequalities between `ℚ` payoffs), and `MixedPennies.lean:138`.

**The boundary, stated as narrowly as possible.**
* Pure strategies only. `isNashPure` quantifies over chosen actions, never over mixtures.
* The existence claim is **per game and decidable**: `nashPureExists m n G` answers for the
  `G` you give it. This module does NOT state, and does not imply, "every finite game has a
  Nash equilibrium". That is Nash's theorem, it needs a fixed-point or extreme-value argument
  over a simplex, and its pure-strategy form is simply false (matching pennies, above).
* Mixed-strategy Nash existence for a non-zero-sum (bimatrix) game stays **open in this
  repository and unclaimed here**. Checked against the pinned tree: there is no Brouwer
  fixed-point theorem (grepping `Brouwer` hits only `Order/CompleteBooleanAlgebra.lean`,
  `Order/Heyting/Basic.lean`, `Order/PrimeSeparator.lean`), there is no `Mathlib/GameTheory`
  directory, there is no Kakutani fixed-point theorem, and Knaster--Tarski
  (`Mathlib/Order/FixedPoints.lean:75`, `isFixedPt_lfp`) applies to monotone self-maps of a
  complete lattice, which a set of mixtures under the pointwise order is not.
* Three calibers coexist and must not be merged into "Nash existence proved": this module's
  pure `ℚ` decision, `MixedPennies.lean`'s single computed mixed game over `ℚ`, and
  `ZeroSumSion.lean`'s `ℝ` Sion instance for zero-sum games.
* Two players, simultaneous move, no chance nodes; `GameTree.lean` and `SequentialGames.lean`
  cover other shapes and claim no equilibrium existence.

Status: **no CI verdict.** Nothing in this file has been elaborated by Lean: local work is
text only, and GitHub Actions is the sole Lean authority (`CI_NOT_RUN`, fail-closed). This
module is not imported by `JurisLean.lean`, is not named by `AxiomAudit.lean`, and is not in
any release certificate. Registering it -- a quarantined entry in the `PENDING_CI_MODULES`
table, the audit-surface listing that gives it its first compile, then root entry only after
that build is green -- is a separate step owned outside this file, and until it happens the
local reachability gate reports this module as neither promoted nor quarantined. Nothing here
is an attestation, and no count or build status in this header may be inherited by a later
commit.
-/

namespace JurisLean.Mandate.PureNash

variable {m n : ℕ}

/-! ## Bimatrix games over the rationals -/

/-- A two-player game in normal form: the row player's `m × n` payoff matrix and the column
player's, independently. `G.1` is the row player's matrix and `G.2` the column player's, so a
zero-sum game is one where `G.2 = -G.1`, which this module never assumes. Payoffs are in `ℚ`
because that is what makes the equilibrium test below *executable*: the order on `ℚ` is
decidable, so a best-response check on a fixed profile computes to `true` or `false`. -/
def Game (m n : ℕ) : Type := (Fin m → Fin n → ℚ) × (Fin m → Fin n → ℚ)

/-- The row player, holding the column player's action `j` fixed, best-responds with `i` when
no other row action pays more. -/
def isBestResponseRow (G : Game m n) (j : Fin n) (i : Fin m) : Prop :=
  ∀ i' : Fin m, G.1 i' j ≤ G.1 i j

/-- Symmetrically for the column player, holding the row action `i` fixed. -/
def isBestResponseCol (G : Game m n) (i : Fin m) (j : Fin n) : Prop :=
  ∀ j' : Fin n, G.2 i j' ≤ G.2 i j

/-- A pure profile is a Nash equilibrium when each player's chosen action is a best response
to the other's. A profile is a *pair of actions*, not a function. -/
def isNashPure (G : Game m n) (p : Fin m × Fin n) : Prop :=
  isBestResponseRow G p.2 p.1 ∧ isBestResponseCol G p.1 p.2

/-! ## The decision procedure -/

/-- The equilibrium condition written out, so that neither the decision below nor its
correctness proof depends on unfolding `isNashPure` while instances are being resolved. -/
def nashPureBody (m n : ℕ) (G : Game m n) : Prop :=
  ∃ p : Fin m × Fin n,
    (∀ i' : Fin m, G.1 i' p.2 ≤ G.1 p.1 p.2) ∧ (∀ j' : Fin n, G.2 p.1 j' ≤ G.2 p.1 p.2)

/-- `nashPureBody m n G` is decidable, and decidable *computably*: the search runs over the
`Fintype` `Fin m × Fin n` through `Fintype.decidableExistsFintype`, which walks `Finset.univ`,
and every leaf is a `ℚ` comparison. Declared with `def` rather than `theorem` because a
`Decidable` value is data, not a proposition. The proposition it decides is the same statement
as `∃ p, isNashPure G p`, since `nashPureBody` is that conjunction written out. -/
def decidableNashPure (m n : ℕ) (G : Game m n) : Decidable (nashPureBody m n G) :=
  Fintype.decidableExistsFintype

/-- The verdict as a `Bool`: `true` when some profile is a pure Nash equilibrium of `G`. -/
def nashPureExists (m n : ℕ) (G : Game m n) : Bool := decide (nashPureBody m n G)

/-- A `true` label is sound: it reflects into an equilibrium profile. -/
theorem nashPureExists_true_iff (m n : ℕ) (G : Game m n) :
    nashPureExists m n G = true ↔ ∃ p : Fin m × Fin n, isNashPure G p := by
  constructor
  · intro h
    obtain ⟨p, hrow, hcol⟩ := of_decide_eq_true h
    exact ⟨p, hrow, hcol⟩
  · intro h
    obtain ⟨p, hrow, hcol⟩ := h
    exact decide_eq_true ⟨p, hrow, hcol⟩

/-- A `false` label is complete: it means the game provably has no pure equilibrium. The
procedure cannot shrug -- the only other outcome is not running it. -/
theorem nashPureExists_false_iff (m n : ℕ) (G : Game m n) :
    nashPureExists m n G = false ↔ ¬ ∃ p : Fin m × Fin n, isNashPure G p := by
  constructor
  · intro h hexists
    obtain ⟨p, hrow, hcol⟩ := hexists
    have htrue := (nashPureExists_true_iff m n G).mpr ⟨p, hrow, hcol⟩
    rw [htrue] at h
    exact absurd h (by decide)
  · intro hnone
    cases h : nashPureExists m n G with
    | true => exact absurd ((nashPureExists_true_iff m n G).mp h) hnone
    | false => exact rfl

/-! ## Structural facts, not only computations -/

/-- The row component of a pure equilibrium really is a best response. -/
theorem isNashPure_fst (G : Game m n) (p : Fin m × Fin n) (h : isNashPure G p) :
    isBestResponseRow G p.2 p.1 := h.1

/-- The column component likewise. -/
theorem isNashPure_snd (G : Game m n) (p : Fin m × Fin n) (h : isNashPure G p) :
    isBestResponseCol G p.1 p.2 := h.2

/-- And the two halves make the profile: the definition has no hidden content. -/
theorem isNashPure_of_bestResponses (G : Game m n) (p : Fin m × Fin n)
    (hr : isBestResponseRow G p.2 p.1) (hc : isBestResponseCol G p.1 p.2) :
    isNashPure G p := ⟨hr, hc⟩

/-- Swapping the players means swapping the two matrices and swapping the argument order in
each: `swap G : Game n m` has the original column player as its row player. -/
def swap (G : Game m n) : Game n m := (fun j i => G.2 i j, fun j i => G.1 i j)

/-- Equilibrium is invariant under that relabelling: the same play, described from the other
side. This is the statement that the notion does not smuggle in a first-mover assumption. -/
theorem isNashPure_swap (G : Game m n) (p : Fin m × Fin n) (h : isNashPure G p) :
    isNashPure (swap G) (p.2, p.1) := ⟨h.2, h.1⟩

/-- Swapping twice is the identity, on profiles and on equilibrium status. -/
theorem isNashPure_swap_swap (G : Game m n) (p : Fin m × Fin n) :
    isNashPure (swap (swap G)) p ↔ isNashPure G p := Iff.rfl

/-- So the decision procedure agrees with the relabelling: a game and its swapped version get
the same label. Both directions are the same argument -- carry the witness across
`isNashPure_swap`, then read the label back through `nashPureExists_true_iff`. No evaluation
of `nashPureExists` happens here. -/
theorem nashPureExists_swap (m n : ℕ) (G : Game m n) :
    nashPureExists m n G = true ↔ nashPureExists n m (swap G) = true := by
  constructor
  · intro h
    obtain ⟨p, hp⟩ := of_decide_eq_true h
    exact (nashPureExists_true_iff n m (swap G)).mpr ⟨(p.2, p.1), isNashPure_swap G p hp⟩
  · intro h
    obtain ⟨p, hp⟩ := of_decide_eq_true h
    exact (nashPureExists_true_iff m n G).mpr ⟨(p.2, p.1), isNashPure_swap (swap G) p hp⟩

/-- An action is dominant for the row player when it best-responds to *every* column action. -/
def isDominantRow (G : Game m n) (i : Fin m) : Prop := ∀ j : Fin n, isBestResponseRow G j i

/-- The column version. -/
def isDominantCol (G : Game m n) (j : Fin n) : Prop := ∀ i : Fin m, isBestResponseCol G i j

/-- Dominance implies equilibrium: if neither player can do better against anything, then in
particular neither can do better against each other. The only structural existence route here
-- it produces a profile from hypotheses about single players, with no search. -/
theorem nashPure_of_dominant (G : Game m n) (i : Fin m) (j : Fin n)
    (hi : isDominantRow G i) (hj : isDominantCol G j) : isNashPure G (i, j) := ⟨hi j, hj i⟩

/-- A profile at which the row player can strictly gain is not an equilibrium. -/
theorem not_isNashPure_of_row_deviation (G : Game m n) (p : Fin m × Fin n)
    (hdev : ∃ i' : Fin m, G.1 p.1 p.2 < G.1 i' p.2) : ¬ isNashPure G p := by
  obtain ⟨i', hi⟩ := hdev
  intro hn
  linarith [hn.1 i']

/-- The column version. -/
theorem not_isNashPure_of_col_deviation (G : Game m n) (p : Fin m × Fin n)
    (hdev : ∃ j' : Fin n, G.2 p.1 p.2 < G.2 p.1 j') : ¬ isNashPure G p := by
  obtain ⟨j', hj⟩ := hdev
  intro hn
  linarith [hn.2 j']

/-! ## Computed certificate 1 -- a coordination game, which HAS a pure equilibrium -/

/-- Both cells of the main diagonal pay `2`, the off-diagonal cells pay `1`, to *both*
players. Written as a total function on `Fin 2`, so that the labels below compute. -/
def coordPay : Fin 2 → Fin 2 → ℚ := fun i j =>
  if i = 0 then (if j = 0 then (2 : ℚ) else (1 : ℚ)) else (if j = 0 then (1 : ℚ) else (2 : ℚ))

/-- The coordination game: the two matrices are equal, so it is emphatically not zero-sum --
this is the shape `ZeroSumSion.lean` cannot reach and `MatrixGame.lean` never claimed. -/
def coordGame : Game 2 2 := (coordPay, coordPay)

/-- The matrix, cell by cell, computed. -/
theorem coordPay_table :
    coordPay 0 0 = (2 : ℚ) ∧ coordPay 0 1 = (1 : ℚ) ∧ coordPay 1 0 = (1 : ℚ) ∧
      coordPay 1 1 = (2 : ℚ) := by decide

/-- Both diagonal profiles are pure equilibria; each best-response test is two inequalities
over `Fin 2`, and `decide` evaluates them. -/
theorem coordination_diagonal_is_nash :
    isNashPure coordGame (0, 0) ∧ isNashPure coordGame (1, 1) := by decide

/-- Neither off-diagonal profile is one, because the row player gains by moving to the
matching diagonal. -/
theorem coordination_offdiag_not_nash :
    ¬ isNashPure coordGame (0, 1) ∧ ¬ isNashPure coordGame (1, 0) :=
  ⟨not_isNashPure_of_row_deviation coordGame (0, 1) ⟨1, by decide⟩,
   not_isNashPure_of_row_deviation coordGame (1, 0) ⟨0, by decide⟩⟩

/-- **Certificate 1, computed by the procedure**: the label says `true`. -/
theorem coordination_label_true : nashPureExists 2 2 coordGame = true :=
  (nashPureExists_true_iff 2 2 coordGame).mpr ⟨(0, 0), coordination_diagonal_is_nash.1⟩

/-! ## Computed certificate 2 -- matching pennies, which has NO pure equilibrium -/

/-- The row player's table, with index `0` standing for heads and `1` for tails: `+1` when the
coins agree, `-1` when they differ. This is `Mandate.MixedPennies.payoff` cell for cell,
re-indexed from `Bool` to `Fin 2`. -/
def penniesRow : Fin 2 → Fin 2 → ℚ := fun i j => if i = j then (1 : ℚ) else (-1 : ℚ)

/-- The column player's table is the negation, so this game *is* zero-sum -- the point of the
certificate is not the sum but the absence of a pure profile. -/
def penniesCol : Fin 2 → Fin 2 → ℚ := fun i j => if i = j then (-1 : ℚ) else (1 : ℚ)

/-- Matching pennies as a `Game 2 2`, the same position whose mixed equilibrium
`MixedPennies.mixedNash_uniform` proves. -/
def penniesGame : Game 2 2 := (penniesRow, penniesCol)

/-- The row table, computed: it agrees with the attested `Bool`-indexed grid. -/
theorem penniesRow_table :
    penniesRow 0 0 = (1 : ℚ) ∧ penniesRow 0 1 = (-1 : ℚ) ∧ penniesRow 1 0 = (-1 : ℚ) ∧
      penniesRow 1 1 = (1 : ℚ) := by decide

/-- On the diagonal the column player gains by flipping. -/
theorem pennies_col_dev_00 : penniesCol 0 0 < penniesCol 0 1 := by decide

theorem pennies_col_dev_11 : penniesCol 1 1 < penniesCol 1 0 := by decide

/-- Off the diagonal the row player gains by flipping. Same asymmetry
`MixedPennies.agreed_second_moves` records: exactly one player moves at each profile. -/
theorem pennies_row_dev_01 : penniesRow 0 1 < penniesRow 1 1 := by decide

theorem pennies_row_dev_10 : penniesRow 1 0 < penniesRow 0 0 := by decide

/-- Each of the four profiles fails, by hand, from the deviation it names. -/
theorem pennies_not_nash_00 : ¬ isNashPure penniesGame (0, 0) :=
  not_isNashPure_of_col_deviation penniesGame (0, 0) ⟨1, pennies_col_dev_00⟩

theorem pennies_not_nash_11 : ¬ isNashPure penniesGame (1, 1) :=
  not_isNashPure_of_col_deviation penniesGame (1, 1) ⟨0, pennies_col_dev_11⟩

theorem pennies_not_nash_01 : ¬ isNashPure penniesGame (0, 1) :=
  not_isNashPure_of_row_deviation penniesGame (0, 1) ⟨1, pennies_row_dev_01⟩

theorem pennies_not_nash_10 : ¬ isNashPure penniesGame (1, 0) :=
  not_isNashPure_of_row_deviation penniesGame (1, 0) ⟨0, pennies_row_dev_10⟩

/-- **Certificate 2, computed by the procedure**: non-existence over all four profiles of
`Fin 2 × Fin 2`, evaluated rather than argued. Together with the hand-checks above this is
cross-validation, not duplication: the same verdict by two independent routes. -/
theorem matchingPennies_no_pure_equilibrium :
    ¬ ∃ p : Fin 2 × Fin 2, isNashPure penniesGame p := by decide

/-- **Certificate 2's label**: `false`. By `nashPureExists_false_iff` this is a proof that no
pure profile is an equilibrium, which is also the general-form reading of
`MixedPennies.no_pure_pair_is_equilibrium`. -/
theorem pennies_label_false : nashPureExists 2 2 penniesGame = false :=
  (nashPureExists_false_iff 2 2 penniesGame).mpr matchingPennies_no_pure_equilibrium

/-- The two labels disagree, so `nashPureExists` is not a constant on `Game 2 2`. -/
theorem pure_labels_discriminate :
    nashPureExists 2 2 coordGame ≠ nashPureExists 2 2 penniesGame := by
  intro h
  rw [coordination_label_true, pennies_label_false] at h
  exact absurd h (by decide)

/-! ## What the two certificates do not buy

`nashPureExists` decides pure-strategy existence for the game handed to it, and it returned
opposite labels on the two matrices above. What it cannot say is the sentence the mandate
actually asks about: that every finite game has an equilibrium. For pure strategies that
sentence is false, and `pennies_label_false` is the counterexample. For mixed strategies the
sentence is Nash's theorem, and this pin offers no carrier for it -- no Brouwer, no Kakutani,
no `Mathlib/GameTheory`, and Knaster--Tarski (`Mathlib/Order/FixedPoints.lean:75`) needs a
complete lattice that a simplex is not. So general mixed Nash existence for a bimatrix game
stays open here, exactly as `ZeroSumSion.lean` records for the four best-response facts it
proves: separate best responses exist, a joint fixed point is a different claim.
-/

end JurisLean.Mandate.PureNash
