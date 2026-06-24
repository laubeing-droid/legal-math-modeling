import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Sups
import Mathlib.Data.Real.Basic

open Finset

/-! Lemma: If Finset.sup' of non-negative reals is 0, then all elements are 0.
   This is a finite combinatorial fact, no Analysis needed. -/

/-- If all f i >= 0 and sup' f = 0, then all f i = 0. -/
lemma sup'_eq_zero_of_nonneg {α : Type} {s : Finset α} {h : s.Nonempty} {f : α → Real}
    (hf : ∀ i ∈ s, 0 <= f i) (hsup : s.sup' h f = 0) : ∀ i ∈ s, f i = 0 := by
  intro i hi
  have h0 : 0 <= f i := hf i hi
  have hle : f i <= s.sup' h f := Finset.le_sup' f hi
  rw [hsup] at hle
  exact le_antisymm hle h0
