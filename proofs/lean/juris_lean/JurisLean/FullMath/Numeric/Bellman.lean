import JurisLean.FullMath.Core.Foundations

/-!
N09/N10 — Discounted Bellman operator and finite-horizon legal dynamic
programming.

For finite states with normalized nonnegative transition kernels and discount
β ≥ 0, the Bellman operator satisfies a pointwise β-contraction in the
max-gap bound (attained maxima via `Finset.max'` over the legal action
image). The finite-horizon value functions, computed by backward induction
over legal actions only, dominate every legal action's continuation value
and are attained by a legal action.
-/

namespace JurisLean.FullMath.Numeric

section Bellman
variable {S A : Type} [Fintype S] [DecidableEq S] [DecidableEq A]

/-- Action value. -/
def qval (r : S → A → ℚ) (p : S → A → S → ℚ) (β : ℚ) (v : S → ℚ)
    (s : S) (a : A) : ℚ :=
  r s a + β * ∑ s', p s a s' * v s'

/-- Bellman operator value at a state with a nonempty legal action set. -/
noncomputable def bellmanOf (legal : S → Finset A) (r : S → A → ℚ)
    (p : S → A → S → ℚ) (β : ℚ) (v : S → ℚ) (s : S)
    (hne : (legal s).Nonempty) : ℚ :=
  ((legal s).image (fun a => qval r p β v s a)).max'
    (Finset.image_nonempty.mpr hne)

/-- One-sided bound: the operator at `x` is at most the operator at `y`
plus `β * M`, when every gap `|x t - y t|` is bounded by `M`. -/
theorem bellman_onesided (legal : S → Finset A) (r : S → A → ℚ)
    (p : S → A → S → ℚ)
    (hpn : ∀ s a s', 0 ≤ p s a s')
    (hsum : ∀ s a, ∑ s', p s a s' = 1)
    (β : ℚ) (hβ : 0 ≤ β)
    (x y : S → ℚ) (M : ℚ) (hM : ∀ t, |x t - y t| ≤ M) (s : S)
    (hne : (legal s).Nonempty) (hny : (legal s).Nonempty) :
    bellmanOf legal r p β x s hne ≤ bellmanOf legal r p β y s hny + β * M := by
  -- every qval of x is dominated by (qval of y at the same action) + β*M
  have hq : ∀ a ∈ legal s,
      qval r p β x s a ≤ qval r p β y s a + β * M := by
    intro a ha
    have hgap : ∑ s', p s a s' * x s' - ∑ s', p s a s' * y s'
        = ∑ s', p s a s' * (x s' - y s') := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl (fun s' _ => by ring)
    have habs : ∀ s', p s a s' * (x s' - y s') ≤ p s a s' * M :=
      fun s' => mul_le_mul_of_nonneg_left (abs_le.mp (hM s')).2 (hpn s a s')
    have hsumle : ∑ s', p s a s' * (x s' - y s') ≤ ∑ s', p s a s' * M :=
      Finset.sum_le_sum habs
    have hMsum : ∑ s', p s a s' * M = M := by
      rw [Finset.mul_sum, hsum s a, mul_one]
    rw [qval, qval]
    have hβle : β * ((∑ s', p s a s' * x s') - (∑ s', p s a s' * y s'))
        ≤ β * M := mul_le_mul_of_nonneg_left (by
      rw [hgap] at hsumle ⊢
      rw [hMsum] at hsumle
      linarith) hβ
    nlinarith [hβle]
  -- the attained max of the dominated family is dominated
  have himg : ∀ b ∈ (legal s).image (fun a => qval r p β x s a),
      b ≤ bellmanOf legal r p β y s hny + β * M := by
    intro b hb
    obtain ⟨a, ha, hbq⟩ := Finset.mem_image.mp hb
    have hdom := hq a ha
    have hle : qval r p β y s a ≤ bellmanOf legal r p β y s hny :=
      Finset.le_max' _ _ (Finset.mem_image.mpr ⟨a, ha, rfl⟩)
    rw [← hbq]
    linarith
  exact Finset.max'_le _ _ himg

/-- N09: pointwise contraction of the Bellman operator in the max-gap
bound, for any normalized nonnegative transition kernel. -/
theorem bellman_contraction (legal : S → Finset A) (r : S → A → ℚ)
    (p : S → A → S → ℚ)
    (hpn : ∀ s a s', 0 ≤ p s a s')
    (hsum : ∀ s a, ∑ s', p s a s' = 1)
    (β : ℚ) (hβ : 0 ≤ β)
    (v w : S → ℚ) (M : ℚ) (hM : ∀ t, |v t - w t| ≤ M) (s : S)
    (hne : (legal s).Nonempty) :
    |bellmanOf legal r p β v s hne - bellmanOf legal r p β w s hne| ≤ β * M := by
  have h1 := bellman_onesided legal r p hpn hsum β hβ v w M hM s hne hne
  have h2 := bellman_onesided legal r p hpn hsum β hβ w v M
    (fun t => (abs_sub_comm (w t) (v t)) ▸ (hM t)) s hne hne
  rw [abs_le]
  constructor <;> linarith

/-- Finite-horizon value by backward induction, legal actions only. -/
noncomputable def vf (legal : S → Finset A) (hne : ∀ s, (legal s).Nonempty)
    (r : S → A → ℚ) (p : S → A → S → ℚ) (β : ℚ) : ℕ → S → ℚ
  | 0 => fun _ => 0
  | t + 1 => fun s =>
    bellmanOf legal r p β (vf legal hne r p β t) s (hne s)

/-- N10(a): every legal action's total value is dominated by the horizon
value function. -/
theorem vf_dominates (legal : S → Finset A) (hne : ∀ s, (legal s).Nonempty)
    (r : S → A → ℚ) (p : S → A → S → ℚ) (β : ℚ) (t : ℕ) (s : S) (a : A)
    (ha : a ∈ legal s) :
    qval r p β (vf legal hne r p β t) s a ≤
    vf legal hne r p β (t + 1) s :=
  Finset.le_max' _ _ (Finset.mem_image.mpr ⟨a, ha, rfl⟩)

/-- N10(b): on nonempty legal action sets the value is attained by a legal
action — backward induction only ever chooses legal actions. -/
theorem vf_attained (legal : S → Finset A) (hne : ∀ s, (legal s).Nonempty)
    (r : S → A → ℚ) (p : S → A → S → ℚ) (β : ℚ) (t : ℕ) (s : S) :
    ∃ a ∈ legal s,
      vf legal hne r p β (t + 1) s =
        qval r p β (vf legal hne r p β t) s a := by
  have hmem : ((legal s).image (fun a => qval r p β (vf legal hne r p β t) s a)).max'
      (Finset.image_nonempty.mpr (hne s)) ∈
      (legal s).image (fun a => qval r p β (vf legal hne r p β t) s a) :=
    Finset.max'_mem _ _
  obtain ⟨a, ha, heq⟩ := Finset.mem_image.mp hmem
  exact ⟨a, ha, heq⟩

end Bellman

end JurisLean.FullMath.Numeric
