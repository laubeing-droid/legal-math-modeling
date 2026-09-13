import JurisLean.FullMath.Logic.HornFixpoint

/-!
F14 — Incremental maintenance of Horn closures.

Add-only updates may reuse the parent closure: closing `F ∪ Δ` under the
grown rules equals re-closing the parent closure extended with `Δ`, provable
by leastness on both sides. Deletion and rule rewrites recompute from the new
subject; the cached parent value is provably not the new closure in general.
-/

namespace JurisLean.FullMath.Evidence

open JurisLean.FullMath.Logic (step closure PreFixed closure_least closure_subset
  closure_stable closure_preFixed step_mono)

section Incremental
variable {A : Type} [DecidableEq A] [Fintype A]

/-- More rules fire more heads: the step operator is monotone in `R`. -/
theorem step_rules_mono (R R' : Finset (Finset A × A)) (hR : R ⊆ R') (F S : Finset A) :
    step R F S ⊆ step R' F S := by
  intro a ha
  rcases Finset.mem_union.mp ha with hFS | h3
  · rcases Finset.mem_union.mp hFS with h1 | h2
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inl h1)))
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inr h2)))
  · obtain ⟨_, hmem⟩ := Finset.mem_filter.mp h3
    obtain ⟨r, hrR, hrS, hr2⟩ := hmem
    exact Finset.mem_union.mpr (Or.inr
      (Finset.mem_filter.mpr ⟨Finset.mem_univ a, ⟨r, hR hrR, hrS, hr2⟩⟩))

/-- More facts give bigger steps: the step operator is monotone in `F`. -/
theorem step_facts_mono (R : Finset (Finset A × A)) {F G S : Finset A} (h : F ⊆ G) :
    step R F S ⊆ step R G S := by
  intro a ha
  rcases Finset.mem_union.mp ha with hFS | h3
  · rcases Finset.mem_union.mp hFS with h1 | h2
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inl (h h1))))
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inr h2)))
  · exact Finset.mem_union.mpr (Or.inr h3)

/-- Heads fired from a stable set stay inside it. -/
theorem heads_subset (R : Finset (Finset A × A)) (F S : Finset A)
    (h : step R F S = S) :
    ∀ a ∈ Finset.univ.filter (fun a => ∃ r ∈ R, r.1 ⊆ S ∧ r.2 = a), a ∈ S := by
  intro a ha
  obtain ⟨_, hmem⟩ := Finset.mem_filter.mp ha
  have h1 : a ∈ step R F S :=
    Finset.mem_union.mpr (Or.inr (Finset.mem_filter.mpr ⟨Finset.mem_univ a, hmem⟩))
  rwa [h] at h1

/-- The child system's closure is already pre-fixed for the parent system. -/
theorem child_is_parent_prefixed (R R' : Finset (Finset A × A)) (hR : R ⊆ R')
    (F Δ : Finset A) : PreFixed R F (closure R' (F ∪ Δ)) := by
  show step R F (closure R' (F ∪ Δ)) ⊆ closure R' (F ∪ Δ)
  refine (step_rules_mono R R' hR F _).trans ?_
  refine (step_facts_mono R' (ssubL F Δ)).trans ?_
  rw [closure_stable]

/-- The parent closure embeds into the child closure. -/
theorem parent_closure_subset_child (R R' : Finset (Finset A × A)) (hR : R ⊆ R')
    (F Δ : Finset A) : closure R F ⊆ closure R' (F ∪ Δ) :=
  closure_least R F _ (child_is_parent_prefixed R R' hR F Δ)

/-- F14(a): add-only reuse is exact. -/
theorem add_only_reuse (R R' : Finset (Finset A × A)) (hR : R ⊆ R') (F Δ : Finset A) :
    closure R' (F ∪ Δ) = closure R' (closure R F ∪ Δ) := by
  apply Finset.Subset.antisymm
  · refine closure_least R' (F ∪ Δ) _ ?_
    show step R' (F ∪ Δ) (closure R' (closure R F ∪ Δ)) ⊆
        closure R' (closure R F ∪ Δ)
    intro a ha
    rcases Finset.mem_union.mp ha with hFS | hhead
    · rcases Finset.mem_union.mp hFS with hF | hQ
      · -- a ∈ F ∪ Δ ⊆ closure R F ∪ Δ ⊆ its closure
        have hmem1 : a ∈ closure R F ∪ Δ := by
          rcases Finset.mem_union.mp hF with hFin | hD
          · exact Finset.mem_union.mpr (Or.inl (closure_subset R F hFin))
          · exact Finset.mem_union.mpr (Or.inr hD)
        exact closure_subset R' (closure R F ∪ Δ) hmem1
      · exact hQ
    · exact closure_closed_heads R' (closure R F ∪ Δ) (F ∪ Δ)
        (closure_stable R' (closure R F ∪ Δ))
        (Finset.union_subset (fun x hx => Finset.mem_union.mpr
          (Or.inl (closure_subset R F hx))) (fun x hx => Finset.mem_union.mpr (Or.inr hx)))
        a hhead
  · refine closure_least R' (closure R F ∪ Δ) _ ?_
    show step R' (closure R F ∪ Δ) (closure R' (F ∪ Δ)) ⊆ closure R' (F ∪ Δ)
    intro a ha
    rcases Finset.mem_union.mp ha with hFS | hhead
    · rcases Finset.mem_union.mp hFS with hC | hQ
      · -- a ∈ closure R F ∪ Δ ⊆ closure R' (F ∪ Δ)
        have hmem1 : a ∈ closure R' (F ∪ Δ) := by
          rcases Finset.mem_union.mp hC with hP | hD
          · exact parent_closure_subset_child R R' hR F Δ hP
          · exact closure_subset R' (F ∪ Δ) (Finset.mem_union.mpr (Or.inr hD))
        exact hmem1
      · exact hQ
    · exact closure_closed_heads R' (F ∪ Δ) (closure R F ∪ Δ)
        (closure_stable R' (F ∪ Δ))
        (Finset.union_subset (fun x hx => parent_closure_subset_child R R' hR F Δ hx)
          (fun x hx => closure_subset R' (F ∪ Δ) (Finset.mem_union.mpr (Or.inr hx))))
        a hhead

/-- Update operations. -/
inductive UpdateOp (A : Type) where
  /-- Add-only delta: facts added, rules only grew (precondition at theorem level). -/
  | addOnly (Δ : Finset A) (R' : Finset (Finset A × A))
  /-- Deletion of a fact: full recompute on the new subject. -/
  | removeFact (x : A)
  /-- Rule rewrite: full recompute on the new subject. -/
  | rewriteRules (R₂ : Finset (Finset A × A))

/-- The maintained value: add-only reuses, everything else recomputes. -/
noncomputable def incrementalUpdate (R : Finset (Finset A × A)) (F : Finset A) :
    UpdateOp A → Finset A
  | .addOnly Δ R' => closure R' (closure R F ∪ Δ)
  | .removeFact x => closure R (F \ {x})
  | .rewriteRules R₂ => closure R₂ F

/-- F14(b): the add-only branch equals the full recompute on the new subject. -/
theorem addOnly_matches_full_recompute (R R' : Finset (Finset A × A)) (hR : R ⊆ R')
    (F Δ : Finset A) :
    incrementalUpdate R F (.addOnly Δ R') = closure R' (F ∪ Δ) :=
  (add_only_reuse R R' hR F Δ).symm

/-- Deletion recomputes on the new subject by construction. -/
theorem removeFact_recomputes (R : Finset (Finset A × A)) (F : Finset A) (x : A) :
    incrementalUpdate R F (.removeFact x) = closure R (F \ {x}) := rfl

/-- Rule rewrites recompute on the new subject by construction. -/
theorem rewriteRules_recomputes (R R₂ : Finset (Finset A × A)) (F : Finset A) :
    incrementalUpdate R F (.rewriteRules R₂) = closure R₂ F := rfl

/-! The cached parent value is not the new closure after deletion, in general. -/

/-- A two-atom instance: rule `a → b`, facts `{a}`. -/
private def twoRule : Finset (Finset (Fin 2) × Fin 2) :=
  {⟨{0}, 1⟩}

/-- F14(c): removing the fact `a` genuinely changes the closure — the cached
parent value cannot sign the new subject. -/
theorem deletion_invalidates_cache :
    closure twoRule ({0} : Finset (Fin 2)) ≠ closure twoRule (({0} : Finset (Fin 2)) \ {0}) := by
  intro heq
  have h0 : (0 : Fin 2) ∈ closure twoRule {0} :=
    closure_subset _ _ (Finset.mem_singleton_self 0)
  have hF : (({0} : Finset (Fin 2)) \ {0}) = ∅ := by
    ext a
    simp [Finset.mem_sdiff]
  have hempty : closure twoRule (({0} : Finset (Fin 2)) \ {0}) = ∅ := by
    rw [hF]
    refine closure_least _ _ ∅ ?_
    show step twoRule (∅ : Finset (Fin 2)) (∅ : Finset (Fin 2)) ⊆ (∅ : Finset (Fin 2))
    intro (a : Fin 2) ha
    rcases Finset.mem_union.mp ha with h1 | hhead
    · rcases Finset.mem_union.mp h1 with h2 | h2
      · exact absurd h2 (by simp)
      · exact absurd h2 (by simp)
    · obtain ⟨_, hmem⟩ := Finset.mem_filter.mp hhead
      obtain ⟨r, hrR, hrS, _⟩ := hmem
      have hrq : r = ⟨{0}, 1⟩ := Finset.mem_singleton.mp hrR
      have hr0 : (0 : Fin 2) ∈ r.1 := by
        rw [hrq]
        simp
      exact absurd (hrS hr0) (by simp)
  rw [hempty] at heq
  have hmem : (0 : Fin 2) ∈ (∅ : Finset (Fin 2)) := by rw [← heq]; exact h0
  exact absurd hmem (by simp)

end Incremental

end JurisLean.FullMath.Evidence
