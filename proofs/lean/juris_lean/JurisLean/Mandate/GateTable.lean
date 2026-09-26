import Mathlib
import JurisLean.Genealogy.Part6

/-!
# Mandate upgrade — the human-gate table, tested against the table itself

`Genealogy/Part6.lean:375` proves `listed_action_requires_its_gate`, which
unfolds to `decide (requiredGate a = requiredGate a)`: true for any function
whatsoever, hence silent about the table whose name it carries. The audit's P-132
complaint was that "列名动作必经其闸" never inspects the assignment.

Here the guard is proved equivalent to table lookup, the assignment is proved
total and single-valued, and the three actions are proved to require *distinct*
gates — which is the degenerate case (a constant table) the old theorem could not
exclude.

Status: NOT in `JurisLean.lean`, NOT in `AxiomAudit.lean`; CI_NOT_RUN.
-/

namespace JurisLean.Mandate.GateTable

open JurisLean.Genealogy.Part6.P132

/-- The guard answers true exactly for the gate the table assigns. -/
theorem gate_iff_table (a : GatedAction) (g : HumanGate) :
    actionRequiresGate a g = true ↔ g = requiredGate a := by
  cases a <;> cases g <;> decide

/-- Existence and uniqueness: each action has one and only one required gate. -/
theorem gate_exists_unique (a : GatedAction) : ∃! g, actionRequiresGate a g = true := by
  refine ⟨requiredGate a, ?_, ?_⟩
  · cases a <;> decide
  · intro g hg
    rw [gate_iff_table] at hg
    exact hg

/-- The table is not a constant: three actions, three distinct gates. -/
theorem gates_pairwise_distinct :
    requiredGate .fileDocument ≠ requiredGate .issueOpinion ∧
      requiredGate .fileDocument ≠ requiredGate .submitOutput ∧
      requiredGate .issueOpinion ≠ requiredGate .submitOutput :=
  ⟨by decide, by decide, by decide⟩

/-- A wrong gate is refused, for every combination that is not the tabled one. -/
theorem gate_ne_true_of_ne (a : GatedAction) (g : HumanGate) (h : g ≠ requiredGate a) :
    actionRequiresGate a g = false := by
  rw [gate_iff_table]
  intro h'
  exact h h'.symm

/-- Nothing escapes a gate: every listed action's required gate exists. -/
theorem gate_coverage_total :
    ∀ a : GatedAction, ∃ g : HumanGate, actionRequiresGate a g = true :=
  fun a => ⟨requiredGate a, by cases a <;> decide⟩

/-- A signature is never the gate for filing an output: cross-checking the table. -/
theorem gate_table_no_duplicates :
    Function.Injective (requiredGate : GatedAction → HumanGate) := by
  intro a b hab
  cases a <;> cases b <;> simp_all

end JurisLean.Mandate.GateTable
