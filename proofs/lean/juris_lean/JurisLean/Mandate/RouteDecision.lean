import Mathlib

/-!
# Mandate upgrade — route tables that are searched, not restated

`Genealogy/TSpectrum/Batch1.lean:1331` proves `route_and_exclusion_sound` as
`⟨rfl, ⟨certificate.rowInTable, ⟨certificate.conditionHolds,
certificate.exclusionClear⟩⟩⟩`: every conjunct is a field of the certificate the
hypothesis carries, so the theorem cannot fail for any table, any condition, or
any exclusion rule. The audit logged it under P2-13 and under R-05 of the closeout
list.

Here the routing decision is computed by walking the table: `usable` is condition
and not-excluded, `firstUsable` returns the first usable row in priority order,
and the soundness theorem is real — *if* a row is returned, then that row is
usable, proved by induction over the table rather than read out of a record. The
append law says the search is compositional across concatenated blocks, which is
what makes a priority-ordered table a table and not an opaque lookup.

The concrete case at the bottom is the Chapter 2 claim in executable form: a row
whose condition fails is skipped, and a table with nothing usable returns `none`
rather than inventing an answer. The law "新的一般不覆盖旧的特别" is then a
property of the *table contents*, so a wrong table would produce a wrong result
instead of a vacuous theorem.

Status: imported by the release root and named by `AxiomAudit.lean`; built green
in CI run 36297146468 (subject 304194cc5). Commits after that subject do not
inherit the verdict.
-/

namespace JurisLean.Mandate.RouteDecision

/-- One row of a route table: does it apply, and is it excluded. -/
structure RouteRow where
  condition : Bool
  exclusion : Bool
  routeCode : Nat
 deriving DecidableEq, Repr

/-- A row is usable when its condition holds and it is not excluded. -/
def usable (r : RouteRow) : Bool := r.condition && !r.exclusion

/-- First usable row in list (priority) order. -/
def firstUsable : List RouteRow → Option RouteRow
  | [] => none
  | r :: rs => match usable r with
    | true => some r
    | false => firstUsable rs

/-- Does the table contain any usable row at all. -/
def anyUsable : List RouteRow → Bool
  | [] => false
  | r :: rs => usable r || anyUsable rs

theorem firstUsable_nil : firstUsable [] = none := rfl

/-- The head of the table wins when it is usable: priority order is respected. -/
theorem firstUsable_cons_usable (r : RouteRow) (rs : List RouteRow)
    (h : usable r = true) : firstUsable (r :: rs) = some r := by
  simp [firstUsable, h]

/-- A skipped row is skipped because it is not usable, not because it vanished. -/
theorem firstUsable_cons_notUsable (r : RouteRow) (rs : List RouteRow)
    (h : usable r = false) : firstUsable (r :: rs) = firstUsable rs := by
  simp [firstUsable, h]

/--
Soundness, by induction over the table: whatever is returned is usable. The
released version could not fail; this one fails if `usable` is written wrong.
-/
theorem usable_of_firstUsable_some :
    ∀ rows : List RouteRow, ∀ x : RouteRow, firstUsable rows = some x → usable x = true := by
  intro rows
  induction rows with
  | nil =>
      intro x h
      cases h
  | cons r rs ih =>
      intro x h
      cases hu : usable r with
      | true =>
          simp only [firstUsable, hu] at h
          cases h
          exact hu
      | false =>
          simp only [firstUsable, hu] at h
          exact ih x h

/-- The search over a concatenated table is the search over its blocks. -/
theorem anyUsable_append :
    ∀ a b : List RouteRow, anyUsable (a ++ b) = (anyUsable a || anyUsable b) := by
  intro a
  induction a with
  | nil => intro b; simp [anyUsable]
  | cons r as ih =>
      intro b
      rw [List.cons_append]
      simp only [anyUsable, ih b]
      cases h : usable r <;> simp [h]

/-- If anything is usable, something is returned: the search never swallows a hit. -/
theorem some_of_anyUsable_true :
    ∀ rows : List RouteRow, anyUsable rows = true → ∃ x : RouteRow, ∃ o : Option RouteRow,
      o = some x ∧ firstUsable rows = o := by
  intro rows
  induction rows with
  | nil =>
      intro h
      simp [anyUsable] at h
  | cons r rs ih =>
      intro h
      cases hu : usable r with
      | true =>
          exact ⟨r, some r, rfl, firstUsable_cons_usable r rs hu⟩
      | false =>
          simp only [anyUsable, hu, false_or] at h
          obtain ⟨x, o, ho, hfirst⟩ := ih h
          exact ⟨x, o, ho, by rw [firstUsable_cons_notUsable r rs hu]; exact hfirst⟩

/--
Chapter 2's refusal, as a computation over table contents: a row whose condition
does not hold contributes nothing, and a table with no usable row returns `none`
instead of adjudicating.
-/
def excludedRow : RouteRow := { condition := true, exclusion := true, routeCode := 7 }

def inactiveRow : RouteRow := { condition := false, exclusion := false, routeCode := 3 }

def usableRowA : RouteRow := { condition := true, exclusion := false, routeCode := 1 }
def usableRowB : RouteRow := { condition := true, exclusion := false, routeCode := 2 }

theorem inactive_is_skipped : firstUsable [inactiveRow] = none := by decide

theorem excluded_is_skipped : firstUsable [excludedRow] = none := by decide

/-- A usable row is found, and its code survives the search unchanged. -/
def probeRow : RouteRow := { condition := true, exclusion := false, routeCode := 11 }

theorem usable_is_found : firstUsable [inactiveRow, excludedRow, probeRow] = some probeRow := by
  decide

/-- The table's ordering, not its content, decides which of two usable rows wins. -/
theorem priority_order_decides :
    firstUsable [usableRowA, usableRowB] = some usableRowA ∧
      firstUsable [usableRowB, usableRowA] = some usableRowB := by
  exact ⟨by decide, by decide⟩

end JurisLean.Mandate.RouteDecision
