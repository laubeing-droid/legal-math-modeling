import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic

open Finset

/-! Lemma: If Finset.sup' of non-negative reals is 0, then all elements are 0.
   This is a finite combinatorial fact, no Analysis needed. -/

/-- If all f i >= 0 and sup' f = 0, then all f i = 0. -/
lemma sup'_eq_zero_of_nonneg {α : Type} {s : Finset α} {h : s.Nonempty} {f : α -> Real}
    (hf : forall i in s, 0 <= f i) (hsup : s.sup' h f = 0) : forall i in s, f i = 0 := by
  intro i hi
  have h0 : 0 <= f i := hf i hi
  have hle : f i <= s.sup' h f := Finset.le_sup' f hi
  rw [hsup] at hle
  exact le_antisymm hle h0

/-- If weightedSupDist = 0 then x = y (identity of indiscernibles). -/
lemma weightedSupDist_eq_zero_imp {n : Nat} {w : Fin n -> Real} {x y : Fin n -> Real}
    (hw : forall i, 0 < w i) (h : weightedSupDist w x y = 0) : x = y := by
  unfold weightedSupDist at h
  have h_nonneg : forall (i : Fin n), i in Finset.univ -> 0 <= |x i - y i| / w i := by
    intro i hi
    apply div_nonneg (abs_nonneg _) (by positivity)
  have h_all_zero := sup'_eq_zero_of_nonneg h_nonneg h
  apply funext
  intro i
  have hi_univ : i in Finset.univ := Finset.mem_univ i
  have h_zero : |x i - y i| / w i = 0 := h_all_zero i hi_univ
  have h_abs_zero : |x i - y i| = 0 := by
    -- From (a / b) = 0 and b > 0, a = 0
    have hpos : 0 < w i := hw i
    -- (a / b) = 0 iff a = 0 (since b > 0)
    -- This is: div_eq_zero_iff_eq_zero_of_pos hpos
    -- Wait, the lemma is: div_eq_zero_iff.mp
    have h_div : |x i - y i| / w i = 0 := h_zero
    -- div_eq_zero_iff: a / b = 0 iff a = 0 or b = 0
    -- div_eq_zero_iff.mp h_div gives: |x-y|=0 or w=0. Since w>0, |x-y|=0
    rcases div_eq_zero_iff.mp h_div with (h_abs | h_w)
    . exact h_abs
    . exfalso; exact ne_of_gt hpos h_w
  -- |x_i - y_i| = 0 -> x_i = y_i
  exact sub_eq_zero.mp (abs_eq_zero.mp h_abs_zero)