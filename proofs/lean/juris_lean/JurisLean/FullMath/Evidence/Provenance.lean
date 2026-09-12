import JurisLean.FullMath.Core.Foundations

/-!
F04 — Provenance dependency soundness. Derivation trees keep an explicit
origin layer; the recorded dependency set of a conclusion contains every
assumption actually used; retiring a source invalidates exactly the
derivations whose closure it hits.
-/

namespace JurisLean.FullMath.Evidence

abbrev Assume := String

/-- Derivation tree: sourced origin leaves and rule steps. -/
inductive Deriv where
  | origin (a : Assume)
  | step (rule : String) (children : List Deriv) (conc : String)

/-- All subtrees of a derivation (including itself). -/
def Deriv.subtrees : Deriv → List Deriv
  | .origin a => [.origin a]
  | .step r cs c => .step r cs c :: cs.flatMap Deriv.subtrees

/-- Recorded dependency set: union of origins in the whole tree. -/
def Deriv.deps : Deriv → List Assume
  | .origin a => [a]
  | .step _ cs _ => cs.flatMap Deriv.deps

/-- Helper: dependency completeness transfers over lists of children. -/
theorem deps_complete_list (cs : List Deriv)
    (ih : ∀ d ∈ cs, ∀ a, Deriv.origin a ∈ d.subtrees → a ∈ d.deps) :
    ∀ a, Deriv.origin a ∈ cs.flatMap Deriv.subtrees → a ∈ cs.flatMap Deriv.deps := by
  induction cs with
  | nil => intro a ha; exact absurd ha (by simp)
  | cons d cs' ihcs =>
    intro a ha
    rw [List.mem_flatMap] at ha ⊢
    obtain ⟨d', hd'cs, hsub⟩ := ha
    refine ⟨d', hd'cs, ?_⟩
    exact ih d' (by simp [hd'cs]) a hsub

/-- F04(a): every origin appearing anywhere in the tree is in its recorded
dependency set — dependencies(conclusion) ⊇ actual assumptions used. -/
theorem deps_complete (d : Deriv) :
    ∀ a, Deriv.origin a ∈ d.subtrees → a ∈ d.deps := by
  induction d with
  | origin b =>
    intro a ha
    simp only [Deriv.subtrees, List.mem_singleton] at ha
    have hab : a = b := Deriv.origin.inj ha
    subst hab
    simp [Deriv.deps]
  | @step r cs c ih =>
    intro a ha
    simp only [Deriv.subtrees, List.mem_cons] at ha
    rcases ha with heq | ha
    · exact absurd heq (by simp)
    · have hlist := deps_complete_list cs ih a ha
      simpa [Deriv.deps] using hlist

/-- A derivation is invalidated by retirement exactly when a recorded
dependency is retired. -/
def invalidated (retired : List Assume) (d : Deriv) : Bool :=
  d.deps.any (fun a => retired.contains a)

/-- F04(b): derivations with no retired dependency keep their computation. -/
theorem unaffected_of_no_retired_dep (retired : List Assume) (d : Deriv)
    (h : ∀ a ∈ d.deps, a ∉ retired) : invalidated retired d = false := by
  simp only [invalidated, List.any_eq_true, not_exists]
  intro a ha
  specialize h a ha
  simpa using h

/-- F04(c): a used, retired source does invalidate the derivation. -/
theorem invalidated_of_retired_used (retired : List Assume) (d : Deriv)
    (a : Assume) (ha : a ∈ d.deps) (hr : a ∈ retired) :
    invalidated retired d = true := by
  simp only [invalidated, List.any_eq_true]
  exact ⟨a, ha, by simpa using hr⟩

/-- F04(d): counterfactual stability — changing content that no dependency
references leaves the recorded dependency set untouched. Formally, deps only
depends on the origins present, and derivations differing only in conclusions
of rule steps (not in origins) have equal dependency sets. -/
theorem deps_conclusion_irrelevant (r : String) (cs : List Deriv) (c c' : String) :
    Deriv.deps (.step r cs c) = Deriv.deps (.step r cs c') := rfl

end JurisLean.FullMath.Evidence
