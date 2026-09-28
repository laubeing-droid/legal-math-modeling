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

**Carriers, read out of the pinned source rather than recalled.** Every file:line below was
opened and checked under `proofs/lean/juris_lean/.lake/packages/mathlib/Mathlib/`.

* `Fintype.decidableExistsFintype` (`Data/Fintype/Defs.lean:213`) and
  `Fintype.decidableForallFintype` (`:209`) are both registered `instance`s, not merely defs.
  Each is `decidable_of_iff` over the `Finset` form: `∃ a ∈ Finset.univ, p a` and
  `∀ a ∈ Finset.univ, p a`, whose decidability is `Finset.decidableDExistsFinset`
  (`Data/Finset/Defs.lean:361`) and `Finset.decidableDforallFinset` (`:345`), and that pair
  descends to `Multiset.decidableDforallMultiset` (`Data/Multiset/Defs.lean:309`) over
  `m.attach`, built from `Multiset.decidableForallMultiset` (`:305`). So every quantifier below
  becomes a walk of `Finset.univ`, which is the finite sweep the procedure is.
* The index types carry the `Fintype` instances that walk needs: `Fin.fintype`
  (`Data/Fintype/Basic.lean:36`) and `instFintypeProd` (`Data/Fintype/Prod.lean:45`).
* Conjunction decidability is the instance the pinned source itself names as a term,
  `instDecidableAnd` (used at `Data/Finset/Defs.lean:353`).
* `ℚ` is Lean core `Rat` (`Data/Rat/Init.lean:21`, `notation "ℚ" => Rat`), so the leaf order
  instances for `≤` and `<` -- and their reduction to `true`/`false` -- are core's, not
  Mathlib's, and are therefore cited here by in-repo evidence instead of a file:line: this
  repository already decides `ℚ` comparisons to completion in modules that built green, at
  `MatrixGame.lean:54`, `MixedPennies.lean:138` and `:142`, and
  `FullMath/Action/IncentiveEnumeration.lean:20` and `:42` (the last two decide `≥`/`≤`
  between `ℚ` payoffs under `∀ t ∈ Finset.univ`). `native_decide` is banned in this repository
  and is not used.
* `of_decide_eq_true` and `decide_eq_true` are Lean core; this repository uses exactly that
  pair, positionally, against a `decide`-shaped definition at `MatrixGame.lean:51`, which is
  the shape copied here.
* `Bool.decide_false` / `Bool.of_decide_false` remain deliberately unused, for a reason this
  round made concrete: both take an implicit `Decidable` that must come out *structurally
  equal* to the instance baked into `nashPureExists`'s stored value, because `decide p` is
  `Decidable.decide` applied to that instance and nothing makes two different instances of
  the same proposition definitionally equal. The label proofs below are therefore anchored at
  `nashPureBody`, whose instance is fixed and named, and the `iff` plus a `cases` on the
  `Bool` needs no such coincidence. No decidability here comes from a classical fallback.

**What the ten errors of run `36401817896` were, and what changed.** `lean-full-clean-build`
printed ten messages in this file, at these positions *in that superseded text*: `123:54`,
`130:48`, `130:11`, `134:25`, `187:40`, `187:11`, `190:40`, `190:11`, `238:68`, `299:58`. One
cause explains all of them. Type class resolution
matches a target against candidate instance *types* without delta-unfolding ordinary `def`s, so
`decide` was asked for `Decidable (nashPureBody m n G)`, `Decidable (isNashPure coordGame (0, 0)
∧ ...)`, and `Decidable (¬ ∃ p, isNashPure penniesGame p)` and could not see through
`nashPureBody` / `isNashPure` / `isBestResponseRow` to the `Fintype` quantifier instances --
even though the same `Fintype.decidableExistsFintype` term elaborated one line earlier, at the
`def decidableNashPure` of that text (`:119-120`, no error printed), where its expected type was
*given* rather than searched for. Hence:

* every proposition this file defines over a finite search now has a `Decidable` instance whose
  stated target has that proposition's own constant at its head -- `decBestResponseRow`,
  `decBestResponseCol`, `decIsNashPure`, and `decNashPureBody`, which is a thin wrapper around
  the untouched `def decidableNashPure` -- so resolution is a direct hit and never needs to
  unfold; each body is itself elaborated against a declared expected type, which is the path
  that already worked;
* the decision stays computable and stays in one place: `decidableNashPure` keeps its `def`, its
  name, its signature and its body `Fintype.decidableExistsFintype`, and the instance points at
  it, so every `decide` in this file resolves to the very same term and the equations between
  them hold by reflexivity. No `Decidable` here is discharged by the classical fallback
  `Classical.propDecidable` -- that would have made the "decision procedure" claim false, and
  `decide` would not have reduced on either certificate;
* the two label lemmas no longer let `of_decide_eq_true` guess its proposition from an equation
  whose left side names `nashPureExists`. They fix the expected type first (`have
  hbody : nashPureBody m n G := of_decide_eq_true h`, `show decide (nashPureBody m n G) =
  true`), which is what removes the `?m.12 is not an inductive datatype` and the untypeable
  `⟨...⟩` messages -- those were downstream of the unresolved metavariable, not separate bugs;
  `nashPureExists_swap` no longer touches `decide` at all: it rewrites both sides through the
  label lemmas and moves a witness across `isNashPure_swap`;
* `nashPureBody` and `isNashPure` are still two spellings of one proposition, and the label
  lemmas use that equation directly (`exact hbody` against the existential), so the procedure
  and the definition cannot drift apart and no bridge lemma is needed.

All 27 theorems keep their names *and* their statements -- the same 27 that `AxiomAudit.lean`
prints axioms for, in its generated target block -- and nothing was weakened. Both certificates
are still evaluated by the kernel rather than argued (`coordination_diagonal_is_nash` and
`matchingPennies_no_pure_equilibrium` are `by decide`, and the labels follow from them). The
counted shape of this module does not move either: still 27 `theorem`/`lemma` declarations and
still the same number of `def` carriers, because the four additions above are `instance`
declarations and `decidableNashPure` remains a `def`. The generated accounts therefore name
exactly what this file declares; promotion out of quarantine is the only step this repair leaves
open, and it belongs outside this file.

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

Status: **no CI verdict for this text.** The repair above has never been elaborated: local work
is text only, and GitHub Actions is the sole Lean authority (`CI_NOT_RUN`, fail-closed). Run
`36401817896` is a verdict on the *superseded* text, and that verdict was ten errors; it says
nothing about this one. The registration facts were read off the tree, not asserted, and are
quoted by content rather than by line number because the audit listing is generated and its
line numbers move when other modules are booked: this module is NOT imported by the release root
`JurisLean.lean`; it IS imported by `JurisLean/AxiomAudit.lean` (`import
JurisLean.Mandate.PureNash`) and named there by exactly 27 `#print axioms` entries inside that
file's generated target block -- that listing is where the previous text met its first
compiler; and it is booked quarantined in the `PENDING_CI_MODULES` table of
`scripts/ci/check_import_reachability.py` under the key `JurisLean.Mandate.PureNash`, which is
what keeps the reachability generator from importing it into the root before a green build of
its own. Because no theorem name or statement changed, that booking needs no regeneration for
this repair; promotion out of quarantine and root entry stay owned outside this file, and both
wait on a green run whose subject actually contains this text. Nothing here is an attestation,
and no count or build status in this header may be inherited by a later commit.

Verdict, and its two limits. Run 36409348921 at subject `649d0fd` finished with every job
green, and its axiom audit -- the kernel's own words, filed in this repository at `docs/formal-release/ci-evidence/36409348921/axiom-audit/axiom-audit.raw.txt` --
names all 27 of this module's declarations and reports no `sorryAx`. So the
27 theorems are attested at that subject. What that does not give: (i) it attests those
declarations, not these sentences, which were written after the build; (ii) it is not a release-root
entry -- `Mandate/PureNash.lean` stays in `PENDING_CI_MODULES`, because joining the root changes the
closure and needs a build of its own, and a verdict is only ever the one belonging to the subject
that was built.

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

/-- Best-responding is decidable, and computably so: the search is the `Fintype` sweep
`Fintype.decidableForallFintype` (`Mathlib/Data/Fintype/Defs.lean:209`) over `Fin m`, whose
leaves are `ℚ` comparisons. Declared as an `instance` rather than left to resolution because
type class matching does not unfold `isBestResponseRow` while matching; on the line below the
proposition is given, not searched for, and that path does unfold. -/
instance (priority := 100) decBestResponseRow (G : Game m n) (j : Fin n) (i : Fin m) :
    Decidable (isBestResponseRow G j i) := Fintype.decidableForallFintype

/-- The column version, over `Fin n`. -/
instance (priority := 100) decBestResponseCol (G : Game m n) (i : Fin m) (j : Fin n) :
    Decidable (isBestResponseCol G i j) := Fintype.decidableForallFintype

/-- A pure profile is a Nash equilibrium when each player's chosen action is a best response
to the other's. A profile is a *pair of actions*, not a function. -/
def isNashPure (G : Game m n) (p : Fin m × Fin n) : Prop :=
  isBestResponseRow G p.2 p.1 ∧ isBestResponseCol G p.1 p.2

/-- A profile's equilibrium status is decidable by deciding its two halves: the body asks for
`instDecidableAnd` over the two instances just declared, so no resolution here has to see
through a definition. -/
instance (priority := 100) decIsNashPure (G : Game m n) (p : Fin m × Fin n) :
    Decidable (isNashPure G p) :=
  show Decidable (isBestResponseRow G p.2 p.1 ∧ isBestResponseCol G p.1 p.2) from inferInstance

/-! ## The decision procedure -/

/-- The equilibrium condition written out, so that neither the decision below nor its
correctness proof depends on unfolding `isNashPure` while instances are being resolved. -/
def nashPureBody (m n : ℕ) (G : Game m n) : Prop :=
  ∃ p : Fin m × Fin n,
    (∀ i' : Fin m, G.1 i' p.2 ≤ G.1 p.1 p.2) ∧ (∀ j' : Fin n, G.2 p.1 j' ≤ G.2 p.1 p.2)

/-- `nashPureBody m n G` is decidable, and decidable *computably*: the search runs over the
`Fintype` `Fin m × Fin n` through `Fintype.decidableExistsFintype`
(`Mathlib/Data/Fintype/Defs.lean:213`), which walks `Finset.univ`, and every leaf is a `ℚ`
comparison. Declared with `def` rather than `theorem` because a `Decidable` value is data, not a
proposition. The proposition it decides is the same statement as `∃ p, isNashPure G p`, since
`nashPureBody` is that conjunction written out. -/
def decidableNashPure (m n : ℕ) (G : Game m n) : Decidable (nashPureBody m n G) :=
  Fintype.decidableExistsFintype

/-- The `instance` half of the same value. `decide (nashPureBody m n G)` cannot reach
`Fintype.decidableExistsFintype` on its own, because type class matching will not delta-unfold
`nashPureBody` to see the `∃` under the name; pointing an instance at the `def` above gives
resolution an exact syntactic hit, and leaves the computable content where it was. Nothing here
is classical: had it been, neither certificate below could have reduced. -/
instance (priority := 100) decNashPureBody (m n : ℕ) (G : Game m n) :
    Decidable (nashPureBody m n G) := decidableNashPure m n G

/-- The verdict as a `Bool`: `true` when some profile is a pure Nash equilibrium of `G`. -/
def nashPureExists (m n : ℕ) (G : Game m n) : Bool := decide (nashPureBody m n G)

/-- A `true` label is sound: it reflects into an equilibrium profile. The proposition
`of_decide_eq_true` is asked about is fixed by the expected type of the `have`, so the
`Decidable` it uses is the very one `nashPureExists` stores -- and the converse reads the
witness back through `decide_eq_true` against a `show`n goal, which likewise leaves no
metavariable for resolution to guess. -/
theorem nashPureExists_true_iff (m n : ℕ) (G : Game m n) :
    nashPureExists m n G = true ↔ ∃ p : Fin m × Fin n, isNashPure G p := by
  constructor
  · intro h
    have hbody : nashPureBody m n G := of_decide_eq_true h
    exact hbody
  · intro h
    show decide (nashPureBody m n G) = true
    exact decide_eq_true h

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
    cases hb : nashPureExists m n G with
    | true => exact absurd ((nashPureExists_true_iff m n G).mp hb) hnone
    | false => simp [hb]

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
the same label. Both sides are read through `nashPureExists_true_iff` first, so the argument
never asks `decide` to unfold a definition and never evaluates `nashPureExists`; each direction
then carries one profile across `isNashPure_swap`, and the reverse works because `swap (swap G)`
is definitionally the original game -- the fact `isNashPure_swap_swap` records. -/
theorem nashPureExists_swap (m n : ℕ) (G : Game m n) :
    nashPureExists m n G = true ↔ nashPureExists n m (swap G) = true := by
  rw [nashPureExists_true_iff, nashPureExists_true_iff]
  constructor
  · intro h
    obtain ⟨p, hp⟩ := h
    exact ⟨(p.2, p.1), isNashPure_swap G p hp⟩
  · intro h
    obtain ⟨p, hp⟩ := h
    exact ⟨(p.2, p.1), isNashPure_swap (swap G) p hp⟩

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

One further limit is now documented rather than hidden: the four `Decidable` instances above
make the procedure *executable*, and the two certificates above make it *evaluated* on two
concrete games, but this module proves no statement of the form "for every `G`,
`nashPureExists m n G` terminates". Termination is built into the shape of the search -- each
quantifier is a `Finset.univ` walk over a `Fintype`, so there is no recursion to run forever --
and that argument is made here in prose about `Fintype.decidableForallFintype` and
`Fintype.decidableExistsFintype`, not in a theorem.
-/

end JurisLean.Mandate.PureNash
