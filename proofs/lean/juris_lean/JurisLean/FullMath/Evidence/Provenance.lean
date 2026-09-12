import JurisLean.FullMath.Core.Foundations

/-!
F04 — Provenance dependency soundness. Derivation trees keep an explicit
origin layer; the recorded dependency set of a conclusion contains every
assumption actually used; retiring a source invalidates exactly the
derivations whose dependency set it hits. Rule applications are unary or
binary (longer premise lists compose through binary chains).
-/

namespace JurisLean.FullMath.Evidence

abbrev Assume := String

/-- Derivation tree: sourced origin leaves, unary and binary rule steps. -/
inductive Deriv where
  | origin (a : Assume)
  | step1 (rule : String) (child : Deriv) (conc : String)
  | step2 (rule : String) (left right : Deriv) (conc : String)

/-- All subtrees of a derivation (including itself). -/
def Deriv.subtrees : Deriv → List Deriv
  | .origin a => [.origin a]
  | .step1 r c k => .step1 r c k :: c.subtrees
  | .step2 r l r' k => .step2 r l r' k :: (l.subtrees ++ r'.subtrees)

/-- Recorded dependency set: union of origins in the whole tree. -/
def Deriv.deps : Deriv → List Assume
  | .origin a => [a]
  | .step1 _ c _ => c.deps
  | .step2 _ l r' _ => l.deps ++ r'.deps

/-- Helper: dependency completeness transfers over a child list. -/
private theorem deps_complete_list (cs : List Deriv)
    (ih : ∀ d ∈ cs, ∀ a, Deriv.origin a ∈ d.subtrees → a ∈ d.deps) :
    ∀ a, Deriv.origin a ∈ cs.flatMap Deriv.subtrees → a ∈ cs.flatMap Deriv.deps := by
  induction cs with
  | nil => intro a ha; exact absurd ha (by simp)
  | cons d cs' ihcs =>
    intro a ha
    rw [List.mem_flatMap] at ha ⊢
    obtain ⟨d', hd'cs, hsub⟩ := ha
    exact ⟨d', hd'cs, ih d' (by simp [hd'cs]) a hsub⟩

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
  | step1 r c k ih =>
    intro a ha
    simp only [Deriv.subtrees, List.mem_cons] at ha
    rcases ha with heq | ha
    · exact absurd heq (by simp)
    · simpa [Deriv.deps] using ih a ha
  | step2 r l r' k ihl ihr =>
    intro a ha
    simp only [Deriv.subtrees, List.mem_cons, List.mem_append] at ha
    rcases ha with heq | ha | ha
    · exact absurd heq (by simp)
    · have := ihl a ha
      simpa [Deriv.deps] using this
    · have := ihr a ha
      simpa [Deriv.deps] using this

/-- A derivation is invalidated by retirement exactly when a recorded
dependency is retired. -/
def invalidated (retired : List Assume) (d : Deriv) : Bool :=
  d.deps.any (fun a => decide (a ∈ retired))

/-- F04(b): derivations with no retired dependency keep their computation. -/
theorem unaffected_of_no_retired_dep (retired : List Assume) (d : Deriv)
    (h : ∀ a ∈ d.deps, a ∉ retired) : invalidated retired d = false := by
  by_contra htrue
  rw [invalidated, List.any_eq_true] at htrue
  obtain ⟨a, ha, hdec⟩ := htrue
  exact h a ha (of_decide_eq_true hdec)

/-- F04(c): a used, retired source does invalidate the derivation. -/
theorem invalidated_of_retired_used (retired : List Assume) (d : Deriv)
    (a : Assume) (ha : a ∈ d.deps) (hr : a ∈ retired) :
    invalidated retired d = true := by
  rw [invalidated, List.any_eq_true]
  exact ⟨a, ha, decide_eq_true hr⟩

/-- F04(d): counterfactual stability — the recorded dependency set does not
mention rule conclusions at all. -/
theorem deps_conclusion_irrelevant (r : String) (c : Deriv) (k k' : String) :
    Deriv.deps (.step1 r c k) = Deriv.deps (.step1 r c k') := rfl

end JurisLean.FullMath.Evidence
