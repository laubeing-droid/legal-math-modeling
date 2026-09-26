import Mathlib

/-!
# Mandate module B — structural invariants for case comparison

P-109 asks for a *mathematical-structure* comparison of similar cases. The audit
found none on either side: Python compared tuples of label lists
(`retrieval_v4.py:110-115`), and the Lean carrier was a self-equality of a hash
(`Batch3.lean:219 signature_deterministic … = bucketKey … := rfl`).

What this module supplies instead is the property a comparison must have to be
mathematics at all: an invariant that is **label-independent** (renaming the
issue and element codes does not touch it), **additive over structural sum**
(so a merged case has a computable signature), and **discriminating** — there
are concrete cases whose label sets are identical, i.e. which any recall layer
scores as the same case, yet which the invariant separates.

Status: NOT imported by `JurisLean.lean`, NOT in `AxiomAudit.lean`; needs a CI
module build before it may be cited.
-/

namespace JurisLean.Mandate.StructureInvariants

/-- A case as structure, not as text: issue codes, element codes, and the
requirement-element incidences actually asserted between them. -/
structure CaseStructure where
  issues : List Nat
  elements : List Nat
  incidences : List (Nat × Nat)

/-- The coarse invariant: how many issues, how many elements, how many edges. -/
def sig3 (s : CaseStructure) : Nat × Nat × Nat :=
  (s.issues.length, s.elements.length, s.incidences.length)

/-- Structural sum: disjoint union of two cases' material. -/
def sum (s t : CaseStructure) : CaseStructure :=
  { issues := s.issues ++ t.issues
    elements := s.elements ++ t.elements
    incidences := s.incidences ++ t.incidences }

/--
Renaming labels leaves the invariant untouched. This is the difference between a
structural comparison and a vocabulary comparison: the theorem is about the
counts surviving an *arbitrary* relabelling function.
-/
theorem sig3_relabel_fst (s : CaseStructure) (f : Nat → Nat) :
    (sig3 { s with issues := s.issues.map f }).1 = (sig3 s).1 := by
  simp [sig3]

theorem sig3_relabel_snd (s : CaseStructure) (f : Nat → Nat) :
    (sig3 { s with elements := s.elements.map f }).2.1 = (sig3 s).2.1 := by
  simp [sig3]

theorem sig3_relabel_edges (s : CaseStructure) (f g : Nat → Nat) :
    (sig3 { s with incidences := s.incidences.map (fun p => (f p.1, g p.2)) }).2.2
      = (sig3 s).2.2 := by
  simp [sig3]

/-- The invariant of a merged case is the componentwise sum of the invariants. -/
theorem sig3_sum (s t : CaseStructure) :
    sig3 (sum s t) =
      ((sig3 s).1 + (sig3 t).1, (sig3 s).2.1 + (sig3 t).2.1, (sig3 s).2.2 + (sig3 t).2.2) := by
  simp [sig3, sum, List.length_append]

/-- Each part survives into the merged signature: a sub-case never contributes
negative structure. -/
theorem sig3_fst_le_sum (s t : CaseStructure) : (sig3 s).1 ≤ (sig3 (sum s t)).1 := by
  simp [sig3, sum]
  omega

theorem sig3_edges_le_sum (s t : CaseStructure) : (sig3 s).2.2 ≤ (sig3 (sum s t)).2.2 := by
  simp [sig3, sum]
  omega

/--
The discriminating pair. Both cases carry exactly the same issue codes and the
same element codes — so a retrieval layer that scores label overlap, a vector of
term frequencies, or a bucket key over these lists sees one and the same case —
yet one asserts three incidences and the other only one.
-/
def anchored : CaseStructure :=
  { issues := [1, 2]
    elements := [10, 11]
    incidences := [(1, 10), (1, 11), (2, 11)] }

def unanchored : CaseStructure :=
  { issues := [1, 2]
    elements := [10, 11]
    incidences := [(1, 10)] }

/-- Identical label material on both sides. -/
theorem same_labels : anchored.issues = unanchored.issues ∧ anchored.elements = unanchored.elements :=
  ⟨rfl, rfl⟩

/-- Different structure, proved by computation, not asserted. -/
theorem signatures_differ : sig3 anchored ≠ sig3 unanchored := by
  intro h
  have he : (sig3 anchored).2.2 = (sig3 unanchored).2.2 := congrArg (fun p => p.2.2) h
  simp only [sig3, anchored, unanchored] at he
  exact absurd he (by decide)

end JurisLean.Mandate.StructureInvariants
