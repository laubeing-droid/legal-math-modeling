import Mathlib
import JurisLean.Genealogy.Part1

/-!
# Mandate upgrade — what the source-of-law ladder actually decides

`Genealogy/Part1.lean:32` carries `source_grade_total`, whose conclusion is
`admissionGrade k = admissionGrade k`: true for any function whatsoever, already
flagged in place with a 强度注. The frozen genealogy's proof target for the
hierarchy is a grade with a *decided extension*, and Chapter 2 of the paper
asserts exactly that.

These theorems state the extension: for each admission grade, precisely which
source kinds fall under it; that no grade class is empty; and that grading is
single-valued. They reuse the released `Part1` definitions instead of
re-declaring them, which is the kernel rule for this line.

Status: imported by the release root and named by `AxiomAudit.lean`; built green
in CI run 36298572193 (subject 0574e2ae4), the first round whose root itself
elaborates this module. Commits after that subject do not inherit the verdict.
-/

namespace JurisLean.Mandate.SourceRank

open JurisLean.Genealogy.Part1.P014

/-- A source is binding exactly when it is a statute or a judicial interpretation. -/
theorem grade_binding_iff (k : SourceKind) :
    admissionGrade k = .binding ↔ k = .statute ∨ k = .judicialInterpretation := by
  cases k <;> decide

/-- “应当参照” is inhabited by the guiding case and by nothing else. -/
theorem grade_shallRefer_iff (k : SourceKind) :
    admissionGrade k = .shallRefer ↔ k = .guidingCase := by
  cases k <;> decide

/-- The reference-only class is the four remaining kinds, exhaustively. -/
theorem grade_referenceOnly_iff (k : SourceKind) :
    admissionGrade k = .referenceOnly ↔
      k = .gazetteCase ∨ k = .custom ∨ k = .doctrine ∨ k = .softLaw := by
  cases k <;> decide

/-- No grade class is empty: the classification is not a colouring of nothing. -/
theorem grade_classes_inhabited :
    (∃ k, admissionGrade k = .binding) ∧ (∃ k, admissionGrade k = .shallRefer) ∧
      (∃ k, admissionGrade k = .referenceOnly) :=
  ⟨⟨.statute, rfl⟩, ⟨.guidingCase, rfl⟩, ⟨.gazetteCase, rfl⟩⟩

/-- Grading is a function: one kind never receives two grades. -/
theorem grade_single_valued (k : SourceKind) (g₁ g₂ : AdmissionGrade)
    (h₁ : admissionGrade k = g₁) (h₂ : admissionGrade k = g₂) : g₁ = g₂ := by
  rw [← h₁, ← h₂]

/-- Every kind receives some grade — the totality the old name only gestured at. -/
theorem grade_exhaustive (k : SourceKind) :
    admissionGrade k = .binding ∨ admissionGrade k = .shallRefer ∨
      admissionGrade k = .referenceOnly := by
  cases k <;> decide

/--
Chapter 2's operative claim as a theorem: soft law and doctrine can never be
cited as binding, whatever a downstream layer prefers.
-/
theorem soft_law_never_binding :
    admissionGrade .softLaw ≠ .binding ∧ admissionGrade .doctrine ≠ .binding :=
  ⟨by decide, by decide⟩

end JurisLean.Mandate.SourceRank
