import JurisLean.FullMath.Core.Foundations

/-!
N09/N10 — Discounted Bellman operator and finite-horizon legal dynamic
programming.

For finite states with normalized nonnegative probability rows and discount
`β ≥ 0`, the Bellman operator satisfies a pointwise `β`-contraction in the
max-gap bound. The finite-horizon value functions, computed by backward
induction over legal actions only, dominate every legal action's
continuation value and are attained by a legal action.
-/

namespace JurisLean.FullMath.Numeric

section Bellman
variable {S A : Type} [Fintype S] [DecidableEq S] [DecidableEq A]

/-- Action value. -/
def qval (r : S → A → ℚ) (p : S → A → S → ℚ) (β : ℚ) (v : S → ℚ) (s : S) (a : A) : ℚ :=
  r s a + β * ∑ s', p s a s' * v s'

/-- Bellman operator over legal actions. -/
def bellman (legal : S → Finset A) (r : S → A → ℚ) (p : S → A → S → ℚ)
    (β : ℚ) (v : S → ℚ) (s : S) : ℚ :=
  (legal s).sup (fun a => qval r p β v s a)

/-- N09: pointwise contraction of the Bellman operator in the max-gap
bound, for any normalized nonnegative transition kernel. -/
theorem bellman_contraction (legal : S → Finset A) (r : S → A → ℚ)
    (p : S → A → S → ℚ)
    (hpn : ∀ s a s', 0 ≤ p s a s')
    (hsum : ∀ s a, ∑ s', p s a s' = 1)
    (β : ℚ) (hβ : 0 ≤ β)
    (v w : S → ℚ) (M : ℚ) (hM : ∀ t, |v t - w t| ≤ M) (s : S) :
    |bellman legal r p β v s - bellman legal r p β w s| ≤ β * M := by
  -- one-sided: sup of q_v ≤ sup of q_w + β*M, and symmetrically
  have honesided : ∀ (x y : S → ℚ), (∀ t, |x t - y t| ≤ M) →
      bellman legal r p β x s ≤ bellman legal r p β y s + β * M := by
    intro x y hxy
    refine Finset.sup_le ?_
    intro a ha
    have hsplit : ∑ s', p s a s' * (x s' - y s')
        = (∑ s', p s a s' * x s') - (∑ s', p s a s' * y s') := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl (fun s' _ => by ring)
    have hgap : (∑ s', p s a s' * x s') - (∑ s', p s a s' * y s') ≤ M := by
      have h1 : ∑ s', p s a s' * (x s' - y s') ≤ ∑ s', p s a s' * M :=
        Finset.sum_le_sum (fun s' _ =>
          mul_le_mul_of_nonneg_left (abs_le.mp (hxy s')).2 (hpn s a s'))
      rw [Finset.mul_sum, hsum s a, mul_one] at h1
      rw [← hsplit]
      exact h1
    have hle : qval r p β x s a ≤ qval r p β y s a + β * M := by
      rw [qval, qval]
      have hβle : β * ((∑ s', p s a s' * x s') - (∑ s', p s a s' * y s')) ≤ β * M :=
        mul_le_mul_of_nonneg_left hgap hβ
      nlinarith [hβle]
    exact hle.trans (add_le_add (Finset.le_sup ha) (le_refl _))
  have h1 := honesided v w hM
  have h2 := honesided w v (fun t => (abs_sub_comm (v t) (w t)) ▸ (hM t))
  rw [abs_le]
  constructor <;> linarith

/-- Finite-horizon value by backward induction, legal actions only. -/
def vf (legal : S → Finset A) (r : S → A → ℚ) (p : S → A → S → ℚ)
    (β : ℚ) : ℕ → S → ℚ
  | 0 => fun _ => 0
  | t + 1 => fun s =>
    (legal s).sup (fun a => r s a + β * ∑ s', p s a s' * vf legal r p β t s')

/-- N10(a): every legal action's total value is dominated by the horizon
value function. -/
theorem vf_dominates (legal : S → Finset A) (r : S → A → ℚ)
    (p : S → A → S → ℚ) (β : ℚ) (t : ℕ) (s : S) (a : A)
    (ha : a ∈ legal s) :
    r s a + β * ∑ s', p s a s' * vf legal r p β t s' ≤
    vf legal r p β (t + 1) s :=
  Finset.le_sup (f := fun a => r s a + β * ∑ s', p s a s' * vf legal r p β t s') ha

/-- N10(b): on nonempty legal action sets the value is attained by a legal
action — backward induction only ever chooses legal actions. -/
theorem vf_attained (legal : S → Finset A) (r : S → A → ℚ)
    (p : S → A → S → ℚ) (β : ℚ) (t : ℕ) (s : S)
    (hne : (legal s).Nonempty) :
    ∃ a ∈ legal s,
      vf legal r p β (t + 1) s =
        r s a + β * ∑ s', p s a s' * vf legal r p β t s' := by
  have hmem : ((legal s).sup (fun a =>
      r s a + β * ∑ s', p s a s' * vf legal r p β t s')) ∈
      (legal s).image (fun a => r s a + β * ∑ s', p s a s' * vf legal r p β t s') :=
    Finset.sup_mem hne
  rw [Finset.mem_image] at hmem
  obtain ⟨a, ha, heq⟩ := hmem
  exact ⟨a, ha, heq⟩

end Bellman

end JurisLean.FullMath.Numeric
