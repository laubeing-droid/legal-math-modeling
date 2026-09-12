import JurisLean.FullMath.Core.Foundations

/-!
F05 — Least closure of finite positive Horn programs.

`T_R(S) = F ∪ S ∪ {h | (B,h) ∈ R, B ⊆ S}` is monotone; iterates from ∅
stabilize within `|A|` steps; the stabilized iterate is the least pre-fixed
point. `F14` reuses this closure for add-only incremental updates; deletion
recomputes from scratch.
-/

namespace JurisLean.FullMath.Logic

section Horn
variable {A : Type} [DecidableEq A] [Fintype A]

/-- One closure step: facts ∪ current ∪ heads fireable from current. -/
def step (R : Finset (Finset A × A)) (F S : Finset A) : Finset A :=
  F ∪ S ∪ (R.filter (fun r => r.1 ⊆ S)).image Prod.snd

/-- T is monotone in the current set. -/
theorem step_mono (R : Finset (Finset A × A)) (F : Finset A) {S T : Finset A}
    (h : S ⊆ T) : step R F S ⊆ step R F T := by
  intro a ha
  simp only [step, Finset.mem_union] at ha ⊢
  rcases ha with ha | ha | ha
  · exact Or.inl ha
  · exact Or.inr (Or.inl (h ha))
  · exact Or.inr (Or.inr
      (by
        simp only [Finset.mem_image] at ha ⊢
        obtain ⟨r, hr, rfl⟩ := ha
        simp only [Finset.mem_filter] at hr
        exact ⟨r, by
          simp only [Finset.mem_filter, hr.1, and_true]
          exact h hr.2, rfl⟩))

/-- Iterated closure from the empty set. -/
def cl (R : Finset (Finset A × A)) (F : Finset A) : ℕ → Finset A :=
  fun n => (step R F)^[n] ∅

theorem cl_zero (R : Finset (Finset A × A)) (F : Finset A) :
    cl R F 0 = (∅ : Finset A) := by
  show (step R F)^[0] (∅ : Finset A) = (∅ : Finset A)
  rw [Function.iterate_zero_apply]

theorem cl_succ (R : Finset (Finset A × A)) (F : Finset A) (n : ℕ) :
    cl R F (n+1) = step R F (cl R F n) := by
  show (step R F)^[n+1] (∅ : Finset A) = step R F ((step R F)^[n] ∅)
  rw [Function.iterate_succ_apply]

theorem cl_mono_step (R : Finset (Finset A × A)) (F : Finset A) (n : ℕ) :
    cl R F n ⊆ cl R F (n+1) := by
  induction n with
  | zero => exact Finset.empty_subset _
  | succ n ih => rw [cl_succ, cl_succ]; exact step_mono R F ih

/-- Iterate monotonicity in the step index. -/
theorem cl_mono (R : Finset (Finset A × A)) (F : Finset A) :
    ∀ n m, m ≤ n → cl R F m ⊆ cl R F n := by
  intro n
  induction n with
  | zero =>
    intro m hm
    have hm0 : m = 0 := Nat.le_zero.mp hm
    subst hm0
    exact Finset.Subset.rfl
  | succ n ih =>
    intro m hm
    rcases Nat.lt_or_eq_of_le hm with hlt | rfl
    · exact (ih m (Nat.lt_succ_iff.mp hlt)).trans (cl_mono_step R F n)
    · exact Finset.Subset.rfl

/-- Facts enter the closure from step one on. -/
theorem subset_cl (R : Finset (Finset A × A)) (F : Finset A) {n : ℕ} (hn : 1 ≤ n) :
    F ⊆ cl R F n := by
  have h1 : F ⊆ cl R F 1 := by
    intro a ha
    rw [cl_succ, cl_zero, step]
    exact Finset.mem_union_left _ ha
  exact h1.trans (cl_mono R F n 1 hn)

/-- Strict growth forces the iterate cardinality past the carrier bound. -/
theorem strict_growth_bound (R : Finset (Finset A × A)) (F : Finset A) (N : ℕ)
    (hstrict : ∀ k ≤ N, cl R F k ≠ cl R F (k+1)) :
    ∀ k ≤ N + 1, k ≤ (cl R F k).card := by
  intro k
  induction k with
  | zero => intro _; exact Nat.zero_le _
  | succ k ih =>
    intro hkN
    have hk : k ≤ N := by omega
    have hne := hstrict k hk
    have hsub : cl R F k ⊆ cl R F (k+1) := cl_mono_step R F k
    have hc1 : (cl R F k).card ≤ (cl R F (k+1)).card := Finset.card_le_card hsub
    have hcardne : (cl R F k).card ≠ (cl R F (k+1)).card := by
      intro heq
      have hcardle : (cl R F k).card ≤ (cl R F (k+1)).card := le_of_eq heq
      have hEq : cl R F k = cl R F (k+1) := Finset.eq_of_subset_of_card_le hsub hcardle
      exact hne hEq
    have hcard : (cl R F k).card < (cl R F (k+1)).card := lt_of_le_of_ne hc1 hcardne
    have hih : k ≤ (cl R F k).card := ih (by omega)
    omega

/-- F05(a): the iteration stabilizes within `|A|` steps. -/
theorem cl_stabilizes (R : Finset (Finset A × A)) (F : Finset A) :
    ∃ k, k ≤ (Finset.univ : Finset A).card ∧ step R F (cl R F k) = cl R F k := by
  by_contra hno
  push_neg at hno
  have hbound : (Finset.univ : Finset A).card + 1 ≤
      (Finset.univ : Finset A).card + 1 := Nat.le_refl _
  have hgrow := strict_growth_bound R F (Finset.univ : Finset A).card
    (fun j hj => by rw [cl_succ]; exact (hno j hj).symm) ((Finset.univ : Finset A).card + 1) hbound
  have huniv : (cl R F ((Finset.univ : Finset A).card + 1)).card ≤
      (Finset.univ : Finset A).card :=
    Finset.card_le_card (Finset.subset_univ _)
  omega

/-- Pre-fixed points of the step operator. -/
def PreFixed (R : Finset (Finset A × A)) (F P : Finset A) : Prop :=
  step R F P ⊆ P

/-- Every iterate is contained in every pre-fixed point. -/
theorem cl_least_iterate (R : Finset (Finset A × A)) (F P : Finset A)
    (hP : PreFixed R F P) : ∀ n, cl R F n ⊆ P := by
  intro n
  induction n with
  | zero => exact Finset.empty_subset _
  | succ n ih => rw [cl_succ]; exact (step_mono R F ih).trans hP

/-- The least closure: the stabilized iterate. -/
noncomputable def closure (R : Finset (Finset A × A)) (F : Finset A) : Finset A :=
  cl R F (cl_stabilizes R F).choose

theorem closure_stable (R : Finset (Finset A × A)) (F : Finset A) :
    step R F (closure R F) = closure R F :=
  (cl_stabilizes R F).choose_spec.2

/-- F05(b): the closure is a pre-fixed point containing the facts. -/
theorem closure_preFixed (R : Finset (Finset A × A)) (F : Finset A) :
    PreFixed R F (closure R F) := by
  show step R F (closure R F) ⊆ closure R F
  rw [closure_stable]

theorem closure_subset (R : Finset (Finset A × A)) (F : Finset A) :
    F ⊆ closure R F := by
  intro a ha
  have h1 : a ∈ step R F (closure R F) := by
    rw [step]
    exact Finset.mem_union_left _ ha
  rwa [closure_stable] at h1

/-- F05(c): leastness — every pre-fixed point contains the closure. -/
theorem closure_least (R : Finset (Finset A × A)) (F P : Finset A)
    (hP : PreFixed R F P) : closure R F ⊆ P :=
  cl_least_iterate R F P hP (cl_stabilizes R F).choose

end Horn

end JurisLean.FullMath.Logic
