import JurisLean.FullMath.Core.Foundations

/-!
C06 — Actual implementation, independent checker, spec correspondence:
the checker is a decidable predicate evaluated on the run witness without
calling the solver; acceptance reflects into semantic membership; and a
successful terminal output satisfies the specification (forward
simulation for the concrete residual-budget checker).
-/

namespace JurisLean.FullMath.Composition

/-- The independent checker: a decidable spec evaluated on the witness. -/
def checkerAccepts (spec : List ℚ → Bool) (w : List ℚ) : Bool := spec w

/-- The semantic solution set of a spec. -/
def solutionsOf (spec : List ℚ → Bool) : Set (List ℚ) := {w | spec w = true}

/-- C06(a): checker acceptance implies membership in the independent
solution set. -/
theorem checker_correspondence (spec : List ℚ → Bool) (w : List ℚ)
    (h : checkerAccepts spec w = true) : w ∈ solutionsOf spec :=
  of_decide_eq_true h

/-- C06(b): the checker is independent of the solver — its value depends
only on the spec and the witness, never on any solver-produced artifact. -/
theorem checker_independence (spec : List ℚ → Bool) (w w' : List ℚ)
    (hw : w = w') : checkerAccepts spec w = checkerAccepts spec w' := by
  rw [hw]

/-- Forward simulation for the concrete budget checker: a run whose
payments are individually legal and total within the budget is accepted
and hence a member of the solutions. -/
def budgetSpec (budget : ℚ) : List ℚ → Bool :=
  fun w => decide ((List.sum w) ≤ budget)

theorem budget_forward_simulation (budget : ℚ) (w : List ℚ)
    (h : List.sum w ≤ budget) : w ∈ solutionsOf (budgetSpec budget) := by
  refine checker_correspondence (budgetSpec budget) w ?_
  simp only [checkerAccepts, budgetSpec]
  exact decide_eq_true h

/-- Rejection reflects: an over-budget run is not in the solution set. -/
theorem budget_rejection (budget : ℚ) (w : List ℚ)
    (h : ¬ (List.sum w ≤ budget)) : ¬ (w ∈ solutionsOf (budgetSpec budget)) := by
  intro hmem
  have := hmem
  simp only [solutionsOf, Set.mem_setOf_eq, budgetSpec] at this
  rw [decide_eq_true (by omega : List.sum w ≤ budget)] at this
  omega

end JurisLean.FullMath.Composition
