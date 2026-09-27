import Mathlib
import JurisLean.Mandate.Kernel

/-!
# Mandate module B — structural invariants for case comparison

P-109 asks for a *mathematical-structure* comparison of similar cases. The audit
found none on either side: Python compared tuples of label lists
(`retrieval_v4.py:110-115`), and the Lean carrier was a self-equality of a hash
(`Batch3.lean:219 signature_deterministic … = bucketKey … := rfl`).

This module is deliberately thin. The case structure, its signature, and the
relabelling/additivity laws live once in `JurisLean.Mandate.Kernel` and are
reused here — that reuse is the point. Audit judgement 1 found the old "unified"
line re-declaring a model per theorem (295 carriers for 300 theorems), so what
this file proves is meaningful precisely because it is proved about the *shared*
signature. What is added here is the property that makes the comparison
mathematical rather than cosmetic: the invariant separates two cases that every
vocabulary-based retrieval layer must score as identical, and the separation
survives both merging further material into both sides and renaming every label.

Status: NOT imported by `JurisLean.lean`, NOT in `AxiomAudit.lean`; needs a CI
module build before it may be cited.
-/

namespace JurisLean.Mandate.StructureInvariants

open JurisLean.Mandate.Kernel

/-- Two cases with exactly the same issue codes and the same element codes — so a
retrieval layer scoring label overlap, a term-frequency vector, or a bucket key
over these lists sees one and the same case — yet one asserts three incidences
and the other only one. -/
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

/-- Different structure, proved by computation rather than asserted. -/
theorem signatures_differ : sig3 anchored ≠ sig3 unanchored := by
  intro h
  have he : (sig3 anchored).2.2 = (sig3 unanchored).2.2 := congrArg (fun p => p.2.2) h
  simp only [sig3, anchored, unanchored] at he
  exact absurd he (by decide)

/-- The edge count of a merge is the sum of the edge counts. -/
theorem sum_signature_third (t : CaseStructure) :
    (sig3 (sum anchored t)).2.2 = 3 + (sig3 t).2.2 := by
  simp only [sig3, sum, anchored, List.length_append, List.length_cons, List.length_nil]
  omega

/--
The separation is stable under merging arbitrary further material into both
cases. Without additivity this would be a fact about two literals; with it, the
signature is a discriminator for the whole comparison layer, which is what the
"结构比对精确核对" half of P-109 requires.
-/
theorem discrimination_survives_sum (t : CaseStructure) :
    sig3 (sum anchored t) ≠ sig3 (sum unanchored t) := by
  intro h
  have h1 := sum_signature_third t
  have h2 := sig3_sum unanchored t
  simp only [sig3, anchored, unanchored, sum, List.length_append, List.length_cons,
    List.length_nil] at h h1 h2 ⊢
  omega

/-- Relabelling the incidences of any case leaves its signature untouched, so no
vocabulary trick can turn `anchored` into `unanchored`. -/
theorem relabel_cannot_bridge (f g : Nat → Nat) :
    (sig3 { anchored with
        incidences := anchored.incidences.map (fun p => (f p.1, g p.2)) }).2.2
      ≠ (sig3 { unanchored with
        incidences := unanchored.incidences.map (fun p => (f p.1, g p.2)) }).2.2 := by
  rw [sig3_relabel_edges, sig3_relabel_edges]
  simp only [sig3, anchored, unanchored]
  decide

/-- Merging a case with itself doubles the signature: the invariant behaves like
a measure, not like a hash. -/
theorem sig3_double (s : CaseStructure) : (sig3 (sum s s)).1 = 2 * (sig3 s).1 := by
  simp only [sig3, sum, List.length_append]
  omega

/-- A merge never loses material from either side. -/
theorem sig3_le_sum_any (s t : CaseStructure) :
    (sig3 s).1 ≤ (sig3 (sum s t)).1 ∧ (sig3 t).2.2 ≤ (sig3 (sum s t)).2.2 :=
  ⟨sig3_fst_le_sum s t, by simp only [sig3, sum]; omega⟩

end JurisLean.Mandate.StructureInvariants
