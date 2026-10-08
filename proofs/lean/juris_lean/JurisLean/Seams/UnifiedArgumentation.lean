/-
Unified argumentation, layer C (plan §4.3; I.4.5).

The defeat factorization: a defeat between two full argument trees
holds exactly when the attacker's HEAD observable hits one of the
target's attackable POSITIONS — the summary-level reading
`Defeat(a, b) ↔ D(q(a), q(b))`.

This file works over the repository's four-kind `Defeat` specification
(rebut / undermine / undercut / subargument lifting, defined in
`FullMath/Logic/AttackCompilation.lean`).  The four gate kinds of §4.3
(exception / authority / scope / procedure) attack through guard slots;
their Lean factorization is the next package and follows the same
`rc`-perimeter pattern — it is NOT claimed here.

Summary representation for this fragment: the attacker contributes its
conclusion (the `h(a)` head observable of §4.2); the target contributes
`attackTargets`, the list of every attackable position in the tree
(root conclusion, direct-child conclusions for undermine, rule-license
targets for undercut, and all recursive positions consumed by
lifting).  The summary-level predicate `summaryDefeat` reads ONLY these
two finite observables — never tree shape, fuel, or identity — so the
biconditional below is the §4.3 factorization for this fragment:
tree-level defeat is decided by the finite summary, path witnesses ride
the actual positions.

STATUS: proved theorems pending their CI compile round (module check
then root then full release); no `sorry`/`admit`/custom `axiom`/
`: True :=`/`native_decide` appears here.
-/

import JurisLean.FullMath.Logic.ArgumentConstruction
import JurisLean.FullMath.Logic.AttackCompilation

namespace JurisLean.Seams.UnifiedArgumentation

open JurisLean.FullMath.Logic (Rul Arg Contrary RuleContra Defeat)

section Summary
variable {A : Type} [DecidableEq A]

/-- Every attackable position of a tree, as the finite target list the
summary level reads: root conclusion, direct-child conclusions
(undermine), the rule-license target (undercut), and all recursive
positions (subargument lifting). -/
def attackTargets (rc : RuleContra A) : Arg A → List A
  | .leaf c => [c]
  | .node r ps =>
      r.head :: ps.map Arg.concl ++ [rc r] ++ ps.bind (attackTargets rc)

/-- The summary-level defeat predicate `D(s, t)` of §4.3 for this
fragment: the attacker's head conclusion hits one of the target's
positions under the declared clash relation.  Reads only the two finite
observables — never the trees. -/
def summaryDefeat (con : Contrary A) (rc : RuleContra A)
    (s : A) (t : Arg A) : Prop :=
    ∃ x ∈ attackTargets rc t, con s x = true

/-- A position of a direct child appears in the parent's target list. -/
theorem mem_attackTargets_of_child {rc : RuleContra A} {r : Rul A}
    {ps : List (Arg A)} {p : Arg A} {x : A}
    (hp : p ∈ ps) (hx : x ∈ attackTargets rc p) :
    x ∈ attackTargets rc (.node r ps) := by
  simp only [attackTargets, List.mem_append]
  exact Or.inr (Or.inr (Or.inr (List.mem_bind_of_mem hp hx)))

/-- The root conclusion is a target. -/
theorem head_mem_attackTargets (rc : RuleContra A) (b : Arg A) :
    Arg.concl b ∈ attackTargets rc b := by
  cases b with
  | leaf c => simp [attackTargets]
  | node r ps =>
      simp only [attackTargets, List.mem_cons, Arg.concl]
      exact Or.inl rfl

/-- A direct child's conclusion is a target of the parent. -/
theorem child_concl_mem_attackTargets {rc : RuleContra A} {r : Rul A}
    {ps : List (Arg A)} {p : Arg A} (hp : p ∈ ps) :
    Arg.concl p ∈ attackTargets rc (.node r ps) := by
  simp only [attackTargets, List.mem_cons, List.mem_append]
  exact Or.inr (Or.inl (List.mem_map_of_mem (f := Arg.concl) hp))

/-- The rule-license target is a target. -/
theorem rule_target_mem_attackTargets {rc : RuleContra A} {r : Rul A}
    {ps : List (Arg A)} : rc r ∈ attackTargets rc (.node r ps) := by
  simp only [attackTargets, List.mem_cons, List.mem_append]
  exact Or.inr (Or.inr (Or.inl (List.mem_singleton _)))

end Summary

section Factorization
variable {A : Type} [DecidableEq A]

/-- §4.3 factorization, soundness direction: every tree-level defeat is
witnessed by a position in the target's summary list.  Proved by
induction on the defeat derivation; each constructor's clash hypothesis
IS the summary hit at the position that constructor attacks. -/
theorem defeat_implies_summaryDefeat {con : Contrary A} {rc : RuleContra A}
    {a b : Arg A} (h : Defeat A con rc a b) :
    summaryDefeat con rc (Arg.concl a) b := by
  induction h with
  | rebut a b hcon =>
      exact ⟨Arg.concl b, head_mem_attackTargets rc b, hcon⟩
  | undermine a r ps p hp hcon =>
      exact ⟨Arg.concl p, child_concl_mem_attackTargets hp, hcon⟩
  | undercut a r ps hcon =>
      exact ⟨rc r, rule_target_mem_attackTargets, hcon⟩
  | lift a r ps p hp h ih =>
      obtain ⟨x, hx, hcon⟩ := ih
      exact ⟨x, mem_attackTargets_of_child hp hx, hcon⟩

/-- §4.3 factorization, completeness direction: every summary-level hit
is realized by a tree-level defeat of the GIVEN attacker — the
constructors read the attacker only through its conclusion, and the
summary hit supplies exactly that clash.  Path witnesses ride the real
child positions (lift chain). -/
theorem summaryDefeat_implies_defeat {con : Contrary A} {rc : RuleContra A}
    (a : Arg A) : ∀ b : Arg A,
      summaryDefeat con rc (Arg.concl a) b → Defeat A con rc a b := by
  intro b
  induction b with
  | leaf c =>
      intro ⟨x, hx, hcon⟩
      simp only [attackTargets, List.mem_singleton] at hx
      subst hx
      exact Defeat.rebut a (.leaf c) hcon
  | node r ps ih =>
      intro ⟨x, hx, hcon⟩
      simp only [attackTargets, List.mem_cons, List.mem_append] at hx
      rcases hx with hx | hx | hx | hx
      · -- root conclusion: direct rebut
        subst hx
        exact Defeat.rebut a (.node r ps) hcon
      · -- direct child conclusion: undermine
        obtain ⟨p, hp, hpx⟩ := List.mem_map.mp hx
        subst hpx
        exact Defeat.undermine a r ps p hp hcon
      · -- rule-license target: undercut
        simp only [List.mem_singleton] at hx
        subst hx
        exact Defeat.undercut a r ps hcon
      · -- recursive position: lift the child's defeat
        obtain ⟨p, hp, hxp⟩ := List.mem_bind.mp hx
        exact Defeat.lift a r ps p hp (ih p ⟨x, hxp, hcon⟩)

/-- §4.3 factorization for this fragment — the full biconditional:
tree-level defeat between two argument trees is DECIDED by the finite
summary observables (the attacker's head conclusion and the target's
position list).  The two halves above compose directly; no tree shape,
fuel, or identity leaks into the deciding side. -/
theorem defeat_iff_summaryDefeat (con : Contrary A) (rc : RuleContra A)
    (a b : Arg A) :
    Defeat A con rc a b ↔ summaryDefeat con rc (Arg.concl a) b :=
  ⟨defeat_implies_summaryDefeat, summaryDefeat_implies_defeat a b⟩

end Factorization

end JurisLean.Seams.UnifiedArgumentation
