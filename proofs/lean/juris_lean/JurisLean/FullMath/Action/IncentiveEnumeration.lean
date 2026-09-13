import JurisLean.FullMath.Core.Foundations

/-!
G04 — Finite DSIC over the FULL type-report grid: the mechanism label is
granted only when the enumerated inequality holds for every report
combination; individual rationality and budget balance are separate
checks composed afterwards.
-/

namespace JurisLean.FullMath.Action

variable {T : Type} [Fintype T] [DecidableEq T]

/-- Utility of a true type `t` under report `t'` (single direct
mechanism; other agents folded into the outcome map). -/
def dsicProp (u : T → T → ℚ) : Prop := ∀ t t', u t t ≥ u t t'

/-- The label check: enumerate all report combinations. -/
def dsicCheck (u : T → T → ℚ) : Bool :=
  decide (∀ t ∈ Finset.univ, ∀ t' ∈ Finset.univ, u t t ≥ u t t')

/-- G04(a): a granted label reflects to the DSIC property everywhere. -/
theorem dsic_of_label (u : T → T → ℚ) (h : dsicCheck u = true) : dsicProp u := by
  have hall : ∀ t ∈ Finset.univ, ∀ t' ∈ Finset.univ, u t t ≥ u t t' :=
    of_decide_eq_true h
  intro t t'
  exact hall t (Finset.mem_univ t) t' (Finset.mem_univ t')

/-- G04(b): one violating report combination falsifies the label. -/
theorem label_false_on_violation (u : T → T → ℚ) (t t' : T)
    (hviol : u t t < u t t') : dsicCheck u = false := by
  by_contra hc
  cases h : dsicCheck u with
  | false => rw [h] at hc; simp at hc
  | true =>
    have hall := dsic_of_label u h
    have hge := hall t t'
    linarith

/-- Individual rationality and budget balance are separate checks. -/
def irCheck (u0 : T → ℚ) (u : T → T → ℚ) : Bool :=
  decide (∀ t ∈ Finset.univ, u0 t ≤ u t t)

def budgetCheck (payments : T → ℚ) (revenue : ℚ) : Bool :=
  decide (revenue = Finset.sum Finset.univ (fun t => payments t))

/-- The full label is the conjunction of separately checked properties. -/
def fullLabel (u0 : T → ℚ) (u : T → T → ℚ) (payments : T → ℚ) (revenue : ℚ) : Bool :=
  dsicCheck u && irCheck u0 u && budgetCheck payments revenue

theorem full_label_decomposes (u0 : T → ℚ) (u : T → T → ℚ) (payments : T → ℚ)
    (revenue : ℚ) (h : fullLabel u0 u payments revenue = true) :
    dsicProp u ∧ (∀ t, u0 t ≤ u t t)
      ∧ revenue = Finset.sum Finset.univ (fun t => payments t) := by
  obtain ⟨⟨hdsic, hir⟩, hbudget⟩ := by
    simpa [fullLabel, Bool.and_eq_true] using h
  refine ⟨dsic_of_label u hdsic, ?_, of_decide_eq_true hbudget⟩
  · intro t
    have hall := of_decide_eq_true hir
    first
    | exact hall t (Finset.mem_univ t)
    | exact hall t

end JurisLean.FullMath.Action
