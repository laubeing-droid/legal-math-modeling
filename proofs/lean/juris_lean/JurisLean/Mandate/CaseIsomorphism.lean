import Mathlib

/-!
# Mandate module — case isomorphism as a relation, with an obstruction

The audit's judgement on P-109 (类案数学结构对比) was that both sides of the bridge
compare tuples or sets for equality and no isomorphism or bijection theorem exists
anywhere in the repository. `StructureInvariants.lean` supplied invariants that
separate structures; separation is only half of what "isomorphic" means, and without
the relation itself one cannot even state which half is missing.

This module supplies the relation and its elementary theory: `iso` is an equivalence
relation on finite case structures, proved from a bijection of slots that carries
relatedness across, and `allSelfRelated` is a property that any isomorphism must
preserve — which is what makes "these two are not isomorphic" a theorem rather than an
impression.

What is deliberately NOT claimed: that agreeing invariants imply isomorphism, nor that a
decision procedure exists for an arbitrary number of slots. What is decided here is
three-slot only: `isoRel3_iff` states that the executable test answers `true` exactly when
two `Rel3` structures are isomorphic, and that needs both the enumeration
(`triedRenames_complete`, six values, by `decide`) and one `Bool` bridge
(`bool_beq_true`, four closed cases). Neither step generalises to `Fin n` by the same
argument, and no claim is made that it does. The five newest declarations
(`bool_beq_true`, `pairs3_all_mem`, `preservesR_iff`, `isoRel3_iff`,
`not_Rel3Iso_allLoops_noRelation`) were written this round and await their CI round: until
that round is green, read `isoRel3_iff` as a claim in flight rather than an attested
result. The residual is booked as R-09 in
`docs/master-plan/03_证明战役台账.md`.

Status: imported by the release root and named by `AxiomAudit.lean`; built green
in CI run 36307416556 (subject cf3214d62), whose audit output names these nine
theorems. Commits after that subject do not inherit the verdict.
-/

namespace JurisLean.Mandate.CaseIsomorphism

/-- A case structure: a number of slots plus which pairs of slots are related. -/
structure CaseStruct where
  n : Nat
  related : Fin n → Fin n → Bool

/--
Two structures are isomorphic when a bijection of slots carries relatedness from one
to the other. Because the map is a bijection and relatedness is stated as an equality
of `Bool`, preservation and reflection are the same fact.
-/
def iso (A B : CaseStruct) : Prop :=
  ∃ f : Fin A.n → Fin B.n,
    Function.Bijective f ∧ ∀ i j, A.related i j = B.related (f i) (f j)

/-- A structure is isomorphic to itself, via the identity. -/
theorem iso_refl (A : CaseStruct) : iso A A :=
  ⟨fun i => i, ⟨⟨fun _ _ h => h, fun y => ⟨y, rfl⟩⟩, fun _ _ => rfl⟩⟩

/--
A bijection has a bijection going back. Deliberately built from the witnesses inside
`Function.Surjective` rather than from `Function.invFun`: the `invFun` fallback branch
asks for a `Nonempty α` instance, which a zero-slot structure does not supply, and an
isomorphism statement may not acquire that hypothesis. CI run 36304261436 reported
exactly that synthesis failure here.
-/
theorem exists_bijective_inverse {α β : Sort _} {f : α → β} (hf : Function.Bijective f) :
    ∃ g : β → α, Function.Bijective g ∧ ∀ b, f (g b) = b := by
  refine ⟨fun b => Classical.choose (hf.2 b), ⟨?_, ?_⟩,
    fun b => Classical.choose_spec (hf.2 b)⟩
  · intro a b h
    have ea : f (Classical.choose (hf.2 a)) = a := Classical.choose_spec (hf.2 a)
    have eb : f (Classical.choose (hf.2 b)) = b := Classical.choose_spec (hf.2 b)
    rw [← ea, ← eb]
    exact congr_arg f h
  · intro x
    exact ⟨f x, hf.1 (Classical.choose_spec (hf.2 (f x)))⟩

/-- Isomorphism can be reversed. -/
theorem iso_symm {A B : CaseStruct} (h : iso A B) : iso B A := by
  obtain ⟨f, hf, hrel⟩ := h
  obtain ⟨g, hg, gspec⟩ := exists_bijective_inverse hf
  refine ⟨g, hg, ?_⟩
  intro i j
  have hrel' := hrel (g i) (g j)
  rw [gspec i, gspec j] at hrel'
  exact hrel'.symm

/-- Isomorphism composes: matching slots twice is a matching of slots. -/
theorem iso_trans {A B C : CaseStruct} (hab : iso A B) (hbc : iso B C) : iso A C := by
  obtain ⟨f, hf, hfrel⟩ := hab
  obtain ⟨g, hg, hgrel⟩ := hbc
  refine ⟨fun i => g (f i), hg.comp hf, ?_⟩
  intro i j
  rw [← hgrel, ← hfrel]

/-- Every slot is self-related. -/
def allSelfRelated (A : CaseStruct) : Prop :=
  ∀ i : Fin A.n, A.related i i = true

/-- An isomorphism transports `allSelfRelated` in the target direction. -/
theorem allSelfRelated_of_iso {A B : CaseStruct} (h : iso A B)
    (hA : allSelfRelated A) : allSelfRelated B := by
  obtain ⟨f, hf, hrel⟩ := h
  intro j
  obtain ⟨i, hi⟩ := hf.2 j
  rw [← hi, ← hrel]
  exact hA i

/-- A structure whose every slot lacks a self-loop. -/
def edgeless : CaseStruct := ⟨3, fun _ _ => false⟩

/-- A structure whose every slot carries a self-loop. -/
def looped : CaseStruct := ⟨3, fun _ _ => true⟩

/--
The two structures are not isomorphic, as a theorem: an isomorphism would carry the
self-loops of `looped` onto `edgeless`, which has none. This is the shape of claim the
bridge lacked — a negative structural comparison, not a tuple inequality.
-/
theorem not_iso_looped_edgeless : ¬ iso looped edgeless := by
  intro h
  have htarget : allSelfRelated edgeless := allSelfRelated_of_iso h (fun _ => rfl)
  have hzero : ¬ (edgeless.related (0 : Fin 3) (0 : Fin 3) = true) := by decide
  exact hzero (htarget (0 : Fin 3))

/-- Two slots with no relations at all; the slot swap is a bijection between them. -/
def twoEmpty : CaseStruct := ⟨2, fun _ _ => false⟩

/-- The slot swap is bijective: it is its own inverse on both sides. -/
theorem swap2_bijective :
    Function.Bijective (fun i : Fin 2 => (⟨1 - i.val, by
      have h := i.isLt; omega⟩ : Fin 2)) := by
  constructor
  · intro a b h
    apply Fin.eq_of_val_eq
    have ha : (a.val : Nat) < 2 := a.isLt
    have hb : (b.val : Nat) < 2 := b.isLt
    have key := congr_arg Fin.val h
    simp only [Fin.val_mk] at key
    omega
  · intro y
    refine ⟨⟨1 - y.val, by have := y.isLt; omega⟩, ?_⟩
    apply Fin.eq_of_val_eq
    have hy : (y.val : Nat) < 2 := y.isLt
    simp only [Fin.val_mk]
    omega

/--
`twoEmpty` is isomorphic to itself by a bijection that is not the identity. The point is
not the example but the quantifier: `iso` is witnessed by *any* structure-preserving
bijection, so a relabelling of slots cannot separate two structures that differ only in
which slot is called 0. The same witness with a non-constant `related` would need a
case split over the values of `Fin 2`; this repository has no green precedent for the
decidable-equality form that would carry it, so it is left out rather than guessed.
-/
theorem iso_twoEmpty_swap : iso twoEmpty twoEmpty := by
  refine ⟨fun i => (⟨1 - i.val, by have h := i.isLt; omega⟩ : Fin 2), swap2_bijective, ?_⟩
  intro i j
  rfl

/-- The swap really moves a slot, so the witness above is not the identity in disguise. -/
theorem swap2_moves_a_slot :
    ((⟨1 - (0 : Nat), by decide⟩ : Fin 2) : Fin 2) = 1 := rfl

/-! ## A computable three-slot test, and the boundary of what it proves -/

/-- A relation on three named slots: the shape the 类案对比 mandate item compares. -/
def Rel3 := Fin 3 → Fin 3 → Bool

/-- All loops on three slots. -/
def allLoops : Rel3 := fun _ _ => true

/-- The same slots with no relation at all. -/
def noRelation : Rel3 := fun _ _ => false

/-- A renaming carries one relation onto the other, stated as a Prop. -/
def preservesRel (R S : Rel3) (e : Equiv.Perm (Fin 3)) : Prop :=
  ∀ i j, R i j = S (e i) (e j)

/-- Isomorphism of three-slot relations: a bijection of slots carrying relatedness. -/
def Rel3Iso (R S : Rel3) : Prop :=
  ∃ f : Fin 3 → Fin 3, Function.Bijective f ∧ ∀ i j, R i j = S (f i) (f j)

/-- An `Equiv` is a bijection, so any renaming that preserves relation witnesses isomorphism. -/
theorem rel3Iso_of_preserves (R S : Rel3) (e : Equiv.Perm (Fin 3))
    (h : preservesRel R S e) : Rel3Iso R S :=
  ⟨e, e.bijective, h⟩

/-- The nine ordered slot pairs, used by the computable test below. -/
def pairs3 : List (Fin 3 × Fin 3) :=
  [(0, 0), (0, 1), (0, 2), (1, 0), (1, 1), (1, 2), (2, 0), (2, 1), (2, 2)]

/-- Six renamings of three slots, each an `Equiv`, so bijectivity is never assumed. -/
def triedRenames : List (Equiv.Perm (Fin 3)) :=
  [1,
   Equiv.swap 0 1,
   Equiv.swap 1 2,
   Equiv.swap 0 2,
   (Equiv.swap 0 1).trans (Equiv.swap 1 2),
   (Equiv.swap 1 2).trans (Equiv.swap 0 1)]

/-- Does this renaming carry one relation onto the other, pair by pair? -/
def preservesR (R S : Rel3) (e : Equiv.Perm (Fin 3)) : Bool :=
  pairs3.all fun p => R p.1 p.2 == S (e p.1) (e p.2)

/--
The computable test over the six renamings. Its status is fixed by `isoRel3_iff` below:
`true` exactly when the two relations are isomorphic, which is the enumeration
`triedRenames_complete` plus the `Bool` bridge `preservesR_iff`. The `decide` facts that
follow show both answers are computed, not asserted.
-/
def isoRel3 (R S : Rel3) : Bool := triedRenames.any fun e => preservesR R S e

/-- Computed: a structure is isomorphic to itself by this test. -/
theorem isoRel3_allLoops_self : isoRel3 allLoops allLoops = true := by decide

/-- Computed: the test finds no renaming among the six that carries loops onto none. -/
theorem isoRel3_allLoops_noRelation : isoRel3 allLoops noRelation = false := by decide

/-- And the negative is a real one: no bijection at all can carry loops onto a loopless relation. -/
theorem noRelation_ne_allLoops : ¬ Rel3Iso noRelation allLoops := by
  intro h
  obtain ⟨f, _hf, hrel⟩ := h
  exact absurd (hrel 0 0) (by simp [noRelation, allLoops])

/-! ## The enumeration step: the six are all the bijections of three slots

The comment at the top of this file refused the counting lemma for years of this
repository's ledger. It is refused no longer, and the reason it is approachable is
structural: the enumeration is stated at `Prop` level over `triedRenames`
(`Rel3Iso_by_list`), so nothing here has to convert a `Bool` equality into a
proposition — the step that made the earlier attempt unmanageable. -/

/-- Isomorphism witnessed by one of the six renamings. -/
def Rel3Iso_by_list (R S : Rel3) : Prop :=
  ∃ e ∈ triedRenames, preservesRel R S e

/--
Every bijection of three slots is one of the six the test tries. This is computation, not
an axiom: `Equiv.Perm (Fin 3)` is a `Fintype` and has decidable equality
(`Fintype.decidableForallFintype` and `Fintype.decidableEqEquivFintype`,
`Mathlib/Data/Fintype/Defs.lean`), so the quantifier reduces to a check over six values.
-/
theorem triedRenames_complete : ∀ e : Equiv.Perm (Fin 3), e ∈ triedRenames := by decide

/--
The list form is neither weaker nor stronger than the definition: the forward direction is
the enumeration above applied to `Equiv.ofBijective`, the reverse is
`rel3Iso_of_preserves`. This is the half of R-09 that was missing — a `false` from the test
now *means* non-isomorphism, given the six are exhaustive.
-/
theorem rel3Iso_iff_by_list (R S : Rel3) : Rel3Iso R S ↔ Rel3Iso_by_list R S := by
  constructor
  · rintro ⟨f, hf, hpres⟩
    exact ⟨Equiv.ofBijective f hf, triedRenames_complete _, hpres⟩
  · rintro ⟨e, _, hpres⟩
    exact rel3Iso_of_preserves R S e hpres

/-- A relation on three slots is isomorphic to itself through the exhaustive list: the
positive side of the same coin, computed rather than assumed. -/
theorem rel3Iso_allLoops_symm_self : Rel3Iso_by_list allLoops allLoops :=
  ⟨1, by decide, fun _ _ => rfl⟩

/-! ## Carrying the `Bool` pair check into the proposition, which was the last inch -/

/-- For `Bool`, `a == b` is `decide (a = b)`, so the boolean test and the proposition
agree. Stated and proved by four closed cases rather than through a simp set, so it does
not depend on which normalisation lemmas the pinned toolchain happens to carry. -/
theorem bool_beq_true {a b : Bool} : (a == b) = true ↔ a = b := by
  cases a <;> cases b <;> decide

/-- The literal nine slots pairs are all the pairs of three slots. Decidable because
`Fin 3 × Fin 3` is a `Fintype` and the list is a literal. -/
theorem pairs3_all_mem : ∀ p : Fin 3 × Fin 3, p ∈ pairs3 := by decide

/-- The pair-by-pair `Bool` check IS the Prop-level preservation statement: forward, the
quantifier over `pairs3` supplies any slot pair; backward, membership gives only pairs the
assumption already covers. -/
theorem preservesR_iff (R S : Rel3) (e : Equiv.Perm (Fin 3)) :
    preservesR R S e = true ↔ preservesRel R S e := by
  rw [preservesRel, preservesR]
  constructor
  · intro h i j
    exact bool_beq_true.mp (List.all_eq_true.mp h ⟨i, j⟩ (pairs3_all_mem ⟨i, j⟩))
  · intro h
    rw [List.all_eq_true]
    intro p _
    cases p with
    | mk a b => exact bool_beq_true.mpr (h a b)

/-- **The three-slot test decides isomorphism.** `true` exactly when the two relations
are isomorphic: soundness is `rel3Iso_of_preserves`, completeness is the exhaustive
`triedRenames_complete` reaching an arbitrary bijection through `rel3Iso_iff_by_list`,
and `preservesR_iff` is what lets the `Bool` computation answer the `Prop` question.
This is the statement R-09 was held open for. -/
theorem isoRel3_iff (R S : Rel3) : isoRel3 R S = true ↔ Rel3Iso R S := by
  constructor
  · intro h
    rw [isoRel3, List.any_eq_true] at h
    obtain ⟨e, _, he⟩ := h
    exact rel3Iso_of_preserves R S e ((preservesR_iff R S e).mp he)
  · intro h
    rw [rel3Iso_iff_by_list] at h
    obtain ⟨e, hem, hpres⟩ := h
    rw [isoRel3, List.any_eq_true]
    exact ⟨e, hem, (preservesR_iff R S e).mpr hpres⟩

/-- A computed `false`, read as a theorem: no bijection of three slots carries total
self-relatedness onto a loopless relation. Before `isoRel3_iff` this pair of statements
existed only separately — one by `decide` about a `Bool`, one by hand about a `Prop`. -/
theorem not_Rel3Iso_allLoops_noRelation : ¬ Rel3Iso allLoops noRelation := by
  intro h
  have h2 : isoRel3 allLoops noRelation = true := (isoRel3_iff allLoops noRelation).mpr h
  rw [isoRel3_allLoops_noRelation] at h2
  exact absurd h2 (by decide)

end JurisLean.Mandate.CaseIsomorphism
