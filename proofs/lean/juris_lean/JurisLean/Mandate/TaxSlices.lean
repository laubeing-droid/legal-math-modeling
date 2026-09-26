import Mathlib

/-!
# Mandate upgrade — progressive brackets that really tax only their own slice

`Genealogy/TSpectrum/Batch1.lean:1257` proves `progressive_and_multiplier_correct`
with `⟨rfl, rfl⟩`: both conjuncts are the bodies of the definitions they name
(`:1247`, `:1252`), i.e. "a definition equals itself". The audit logged it under
P2-13 and left it as R-05b in the closeout list, next to the released
`P099_progressiveTax3` results whose non-negativity is merely the codomain being
`Nat`.

Here the bracket table is walked and the substance of 阶梯与分段 (P-093/P-099) is
proved: brackets are `(width, rate)` pairs, each step taxes `min remaining width`
of what is left, and the key law is compositional — taxing a merged table is the
first block's tax plus the second block's tax **on the leftover base**. That is
what "每档只税自己的切片" means, and it would be false if the recursion passed the
original base down instead of the remainder, which is exactly the bug the
released `P099_progressiveTax3` cannot express.

Status: NOT in `JurisLean.lean`, NOT in `AxiomAudit.lean`; CI_NOT_RUN.
-/

namespace JurisLean.Mandate.TaxSlices

/-- One bracket: how much base it absorbs, and its rate in integer units. -/
structure Bracket where
  width : Nat
  rateN : Nat
 deriving DecidableEq, Repr

/-- Tax the table: each bracket takes `min remaining width`, then the rest continues. -/
def taxOf : Nat → List Bracket → Nat
  | _, [] => 0
  | t, b :: bs => min t b.width * b.rateN + taxOf (t - min t b.width) bs

/-- Base left after the table has absorbed what it can. -/
def remainingOf : Nat → List Bracket → Nat
  | r, [] => r
  | r, b :: bs => remainingOf (r - min r b.width) bs

theorem taxOf_empty_table (t : Nat) : taxOf t [] = 0 := rfl

/-- One bracket: only the overlap of base and width is taxed. -/
theorem taxOf_single (t w r : Nat) :
    taxOf t [{ width := w, rateN := r }] = min t w * r := rfl

/-- No base, no tax, whatever the table says. -/
theorem taxOf_zero_base : ∀ bs : List Bracket, taxOf 0 bs = 0 := by
  intro bs
  induction bs with
  | nil => rfl
  | cons b rest ih =>
      show min 0 b.width * b.rateN + taxOf (0 - min 0 b.width) rest = 0
      have hmin : min 0 b.width = 0 := by omega
      rw [hmin]
      simp

/-- A table can never leave more base than it was given. -/
theorem remainingOf_le_start : ∀ bs : List Bracket, ∀ t : Nat, remainingOf t bs ≤ t := by
  intro bs
  induction bs with
  | nil => intro t; simp [remainingOf]
  | cons b rest ih =>
      intro t
      show remainingOf (t - min t b.width) rest ≤ t
      have hstep := ih (t - min t b.width)
      have hle : t - min t b.width ≤ t := Nat.sub_le _ _
      omega

/--
The compositional law: taxing a merged table is the first block's tax plus the
second block's tax on the *leftover* base. This is 每档只税自己的切片, and it is
the property a wrong recursion (one that forwards the original base) breaks.
-/
theorem taxOf_append :
    ∀ t : Nat, ∀ a b : List Bracket,
      taxOf t (a ++ b) = taxOf t a + taxOf (remainingOf t a) b := by
  intro t a
  induction a with
  | nil =>
      intro b
      simp [taxOf, remainingOf]
  | cons x as ih =>
      intro b
      show min t x.width * x.rateN + taxOf (t - min t x.width) (as ++ b)
           = (min t x.width * x.rateN + taxOf (t - min t x.width) as)
             + taxOf (remainingOf (t - min t x.width) as) b
      rw [ih b]
      omega

/-- Two brackets, one base: the split is visible and computed, not declared. -/
theorem taxOf_two_brackets :
    taxOf 5000 [{ width := 3000, rateN := 1 }, { width := 2000, rateN := 2 }] = 7000 :=
  by decide

/-- A base beyond the table stops being taxed: the top cap is respected. -/
theorem taxOf_capped :
    taxOf 9000 [{ width := 3000, rateN := 1 }, { width := 2000, rateN := 2 }] = 7000 :=
  by decide

/-- The leftover base after a fully absorbing table is zero. -/
theorem remainingOf_exhausted :
    remainingOf 5000 [{ width := 3000, rateN := 1 }, { width := 2000, rateN := 2 }] = 0 :=
  by decide

/-- Widening a table cannot lower the tax: the recursion is monotone in structure. -/
theorem taxOf_prefix_le (t : Nat) (a b : List Bracket) :
    taxOf t a ≤ taxOf t (a ++ b) := by
  rw [taxOf_append]
  omega

end JurisLean.Mandate.TaxSlices
