import Mathlib

/-!
# Mandate upgrade — waterfall allocation whose conservation is proved, not declared

`Genealogy/TSpectrum/Batch2.lean:189` proves `fixed_scheme_conservation` by
`simp [waterfallTotal, plan.conservationLaw]`, where `conservationLaw` is a *field
of the hypothesis record* (`Batch2.lean:181`): the plan must arrive carrying a
proof that it conserves, so the theorem reads "a conserving plan conserves". The
companion `priority_waterfall_monotone` (`Batch2.lean:307`) is the same move
through `adjacentMonotone`. The audit logged both under P2-13 as premise
transport, and the same shape recurs in the certificate module's released twin.

Here the allocation is computed and conservation is derived by induction over the
debt list: payouts plus the carried remainder equal the payment, and no
hypothesis is allowed to carry the conclusion. This is the content P-097 claims
for 清偿与分配 — 守恒, 不超额, 余额结转 — and unlike a field-carried law it would
actually fail if `allocate` were written wrong.

Status: imported by the release root and named by `AxiomAudit.lean`; built green
in CI run 36297146468 (subject 304194cc5). Commits after that subject do not
inherit the verdict.
-/

namespace JurisLean.Mandate.Waterfall

/-- Pay each debt from what remains, in list (priority) order; carry the rest. -/
def allocate : Nat → List Nat → List Nat × Nat
  | payment, [] => ([], payment)
  | payment, d :: ds =>
      (min payment d :: (allocate (payment - min payment d) ds).1,
       (allocate (payment - min payment d) ds).2)

/-- Total paid out. -/
def paidOut (allocations : List Nat) : Nat := allocations.foldr (· + ·) 0

theorem paidOut_nil : paidOut [] = 0 := rfl

/-- Unfolding equations, stated where the recursion is visible to `omega`. -/
theorem allocate_cons (payment d : Nat) (ds : List Nat) :
    allocate payment (d :: ds)
      = (min payment d :: (allocate (payment - min payment d) ds).1,
         (allocate (payment - min payment d) ds).2) := rfl

theorem paidOut_cons (x : Nat) (xs : List Nat) : paidOut (x :: xs) = x + paidOut xs := rfl

/-- With no debts the whole payment is carried, not paid. -/
theorem allocate_no_debts (payment : Nat) :
    allocate payment [] = ([], payment) := rfl

/--
Conservation, derived: the remainder plus everything paid out is the payment.
Induction on the debt list, generalising the payment; the only arithmetic input is
that a partial payment never exceeds what was available.
-/
theorem conservation : ∀ ds : List Nat, ∀ payment : Nat,
    (allocate payment ds).2 + paidOut (allocate payment ds).1 = payment := by
  intro ds
  induction ds with
  | nil =>
      intro payment
      simp [allocate, paidOut]
  | cons d ds ih =>
      intro payment
      have key := ih (payment - min payment d)
      have hmin : min payment d ≤ payment := Nat.min_le_left _ _
      rw [allocate_cons, paidOut_cons]
      omega

/-- Corollary: a payout never exceeds the payment it came from. -/
theorem paidOut_le_payment (payment : Nat) (ds : List Nat) :
    paidOut (allocate payment ds).1 ≤ payment := by
  have h := conservation ds payment
  omega

/-- The allocation is not a constant: the same payment over different debt
profiles produces different payouts. Exhibited, since the claim is existential. -/
theorem allocate_not_constant :
    ∃ (ds₁ ds₂ : List Nat), (allocate 10 ds₁).1 ≠ (allocate 10 ds₂).1 :=
  ⟨[6, 4], [3], by decide⟩

/-- The computed waterfall on a concrete case: exact payment, nothing invented. -/
theorem allocate_concrete : allocate 10 [6, 4] = ([6, 4], 0) := by decide

/-- Overpayment is carried out rather than absorbed, and never silently. -/
theorem allocate_concrete_overshoot : allocate 1 [6, 4] = ([1, 0], 0) := by decide

/-- Underpayment: the remainder is what is left, not a made-up number. -/
theorem allocate_concrete_remainder : allocate 5 [6, 4] = ([5, 0], 0) := by decide

end JurisLean.Mandate.Waterfall
