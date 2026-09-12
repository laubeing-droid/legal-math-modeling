import JurisLean.FullMath.Logic.ArgumentConstruction

/-!
F08 — Cycles and identity boundaries (explicit counterexamples, allowed
frozen scope for this target).

A rootless cycle `a ↔ b` generates nothing at any depth. A rooted cycle
generates arguments of every height with alternating conclusions, so atomic
closure stability never pins down argument identity.
-/

namespace JurisLean.FullMath.Logic

open JurisLean.FullMath.Logic (Generate Arg Rul ruleApps ruleAppsGo)

/-- Rule applications over an empty previous list are empty. -/
private theorem ruleAppsGo_nil_cons (p : Fin 2) (qs : List (Fin 2)) :
    ruleAppsGo ([] : List (Arg (Fin 2))) (p :: qs) = [] := rfl

/-- The two-atom cycle rules: `a → b` and `b → a`. -/
def cyclicRules : List (Rul (Fin 2)) :=
  [⟨[0], 1⟩, ⟨[1], 0⟩]

/-- F08(a): a rootless cycle produces no support at any depth. -/
theorem rootless_cycle_generates_nothing :
    ∀ d, Generate [] cyclicRules d = [] := by
  intro d
  induction d with
  | zero => rfl
  | succ d ih =>
    show Generate [] cyclicRules (d + 1) = []
    rw [show Generate [] cyclicRules (d + 1) =
        Generate [] cyclicRules d ++
        cyclicRules.flatMap (fun r => (ruleApps r (Generate [] cyclicRules d)).map
          (fun ps => Arg.node r ps)) from rfl, ih]
    simp only [List.nil_append, ruleApps]
    show List.flatMap (fun r => (ruleAppsGo ([] : List (Arg (Fin 2))) r.premises).map
        (fun ps => Arg.node r ps)) cyclicRules = []
    simp [cyclicRules, ruleAppsGo]

/-- F08(b): a rooted cycle generates an argument of every depth, with
alternating conclusions. -/
theorem rooted_cycle_alternates :
    ∀ d, ∃ a ∈ Generate [0] cyclicRules d, Arg.height a = d ∧
      (Arg.concl a = (0 : Fin 2) ∧ d % 2 = 0 ∨
       Arg.concl a = (1 : Fin 2) ∧ d % 2 = 1) := by
  intro d
  induction d with
  | zero =>
    refine ⟨Arg.leaf 0, by simp [Generate], by simp [Arg.height],
      Or.inl ⟨rfl, by decide⟩⟩
  | succ d ih =>
    obtain ⟨a, ha, hheight, hcase⟩ := ih
    rcases hcase with ⟨hc, hpar⟩ | ⟨hc, hpar⟩
    · have hrule : (⟨[0], 1⟩ : Rul (Fin 2)) ∈ cyclicRules := by simp [cyclicRules]
      have hfilter : a ∈ (Generate [0] cyclicRules d).filter
          (fun x => decide (Arg.concl x = 0)) := by
        simp only [List.mem_filter]
        exact ⟨ha, by simp [hc]⟩
      have hgo : [a] ∈ ruleAppsGo (Generate [0] cyclicRules d) [0] := by
        simp only [ruleAppsGo, List.mem_flatMap]
        refine ⟨a, hfilter, ?_⟩
        simp only [List.mem_map]
        exact ⟨[], by simp [ruleAppsGo], rfl⟩
      have hnode : Arg.node (⟨[0], 1⟩ : Rul (Fin 2)) [a] ∈
          Generate [0] cyclicRules (d + 1) := by
        show Arg.node _ [a] ∈ Generate [0] cyclicRules d ++
            cyclicRules.flatMap (fun r => (ruleApps r (Generate [0] cyclicRules d)).map
              (fun ps => Arg.node r ps))
        refine List.mem_append.mpr (Or.inr ?_)
        refine List.mem_flatMap.mpr ⟨_, hrule, ?_⟩
        simp only [ruleApps, List.mem_map]
        exact ⟨[a], hgo, rfl⟩
      refine ⟨Arg.node (⟨[0], 1⟩ : Rul (Fin 2)) [a], hnode, ?_, Or.inr ⟨rfl, ?_⟩⟩
      · simp only [Arg.height]
        have h1 : (List.map Arg.height [a]).foldr max 0 = Arg.height a := by simp
        rw [h1, hheight]
      · omega
    · have hrule : (⟨[1], 0⟩ : Rul (Fin 2)) ∈ cyclicRules := by
        simp [cyclicRules]
      have hfilter : a ∈ (Generate [0] cyclicRules d).filter
          (fun x => decide (Arg.concl x = 1)) := by
        simp only [List.mem_filter]
        exact ⟨ha, by simp [hc]⟩
      have hgo : [a] ∈ ruleAppsGo (Generate [0] cyclicRules d) [1] := by
        simp only [ruleAppsGo, List.mem_flatMap]
        refine ⟨a, hfilter, ?_⟩
        simp only [List.mem_map]
        exact ⟨[], by simp [ruleAppsGo], rfl⟩
      have hnode : Arg.node (⟨[1], 0⟩ : Rul (Fin 2)) [a] ∈
          Generate [0] cyclicRules (d + 1) := by
        show Arg.node _ [a] ∈ Generate [0] cyclicRules d ++
            cyclicRules.flatMap (fun r => (ruleApps r (Generate [0] cyclicRules d)).map
              (fun ps => Arg.node r ps))
        refine List.mem_append.mpr (Or.inr ?_)
        refine List.mem_flatMap.mpr ⟨_, hrule, ?_⟩
        simp only [ruleApps, List.mem_map]
        exact ⟨[a], hgo, rfl⟩
      refine ⟨Arg.node (⟨[1], 0⟩ : Rul (Fin 2)) [a], hnode, ?_, Or.inl ⟨rfl, ?_⟩⟩
      · simp only [Arg.height]
        have h1 : (List.map Arg.height [a]).foldr max 0 = Arg.height a := by simp
        rw [h1, hheight]
      · omega

/-- F08(c): same conclusion, different structural identity. -/
theorem rooted_same_conclusion_different_identity :
    ∃ a b, a ∈ Generate [0] cyclicRules 0 ∧ b ∈ Generate [0] cyclicRules 2 ∧
      Arg.concl a = Arg.concl b ∧ Arg.height a ≠ Arg.height b := by
  obtain ⟨a, ha, hha, hd0⟩ := rooted_cycle_alternates 0
  obtain ⟨b, hb, hhb, hd2⟩ := rooted_cycle_alternates 2
  refine ⟨a, b, ha, hb, ?_, ?_⟩
  · rcases hd0 with ⟨hc0, hp0⟩ | ⟨hc0, hp0⟩
    · rcases hd2 with ⟨hc2, hp2⟩ | ⟨hc2, hp2⟩
      · exact hc0.trans hc2.symm
      · exact absurd hp2 (by decide)
    · exact absurd hp0 (by decide)
  · rw [hha, hhb]
    decide

end JurisLean.FullMath.Logic
