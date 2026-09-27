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

What is deliberately NOT claimed: that a decision procedure exists here, nor that
agreeing invariants imply isomorphism. Enumerating the bijections of an n-slot
structure needs a reindexing or counting lemma over `Fin`; the pinned Mathlib commit
has the lemmas but this repository has no green precedent for their exact forms, and
guessing them is the failure mode this audit was written to catch. The residual is
recorded as R-09 in `docs/master-plan/03_证明战役台账.md`.

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

end JurisLean.Mandate.CaseIsomorphism
