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

Proof skeleton: `Arg` is a NESTED inductive (recursion through List),
which the `induction` tactic does not support — all recursion is driven
through the FUEL parameter exactly as the repository's proved
`edgeFuel_iff` does, with `cases` on the tree at each fuel level.

STATUS: proved theorems pending their CI compile round (module check
then root then full release); no `sorry`/`admit`/custom `axiom`/
`: True :=`/`native_decide` appears here.
-/

import JurisLean.FullMath.Logic.ArgumentConstruction
import JurisLean.FullMath.Logic.AttackCompilation

namespace JurisLean.Seams.UnifiedArgumentation

open JurisLean.FullMath.Logic (Rul Arg Contrary RuleContra Defeat
  edgeFuel edgeFuel_iff)

section Summary
variable {A : Type} [DecidableEq A]

/-- Every attackable position of a tree, as the finite target list the
summary level reads: root conclusion, direct-child conclusions
(undermine), the rule-license target (undercut), and all recursive
positions (subargument lifting).  The cons/append nesting is explicit:
the root rides the head of the FIRST segment. -/
def attackTargets (rc : RuleContra A) : Arg A → List A
  | .leaf c => [c]
  | .node r ps =>
      (r.head :: ps.map Arg.concl) ++ ([rc r] ++ ps.flatMap (attackTargets rc))

/-- The summary-level defeat predicate `D(s, t)` of §4.3 for this
fragment: the attacker's head conclusion hits one of the target's
positions under the declared clash relation.  Reads only the two finite
observables — never the trees. -/
def summaryDefeat (con : Contrary A) (rc : RuleContra A)
    (s : A) (t : Arg A) : Prop :=
    ∃ x ∈ attackTargets rc t, con s x = true

/-- The root conclusion is a target (head of the first segment). -/
theorem head_mem_attackTargets (rc : RuleContra A) (b : Arg A) :
    Arg.concl b ∈ attackTargets rc b := by
  cases b with
  | leaf c => simp [attackTargets, Arg.concl]
  | node r ps =>
      simp only [attackTargets, Arg.concl]
      exact List.mem_append.mpr
        (Or.inl (List.mem_cons.mpr (Or.inl rfl)))

/-- A direct child's conclusion is a target of the parent. -/
theorem child_concl_mem_attackTargets {rc : RuleContra A} {r : Rul A}
    {ps : List (Arg A)} {p : Arg A} (hp : p ∈ ps) :
    Arg.concl p ∈ attackTargets rc (.node r ps) := by
  simp only [attackTargets]
  exact List.mem_append.mpr
    (Or.inl (List.mem_cons.mpr
      (Or.inr (List.mem_map_of_mem (f := Arg.concl) hp))))

/-- The rule-license target is a target. -/
theorem rule_target_mem_attackTargets {rc : RuleContra A} {r : Rul A}
    {ps : List (Arg A)} : rc r ∈ attackTargets rc (.node r ps) := by
  simp only [attackTargets]
  exact List.mem_append.mpr
    (Or.inr (List.mem_append.mpr
      (Or.inl (List.mem_singleton.mpr rfl))))

/-- A position of a direct child appears in the parent's target list. -/
theorem mem_attackTargets_of_child {rc : RuleContra A} {r : Rul A}
    {ps : List (Arg A)} {p : Arg A} {x : A}
    (hp : p ∈ ps) (hx : x ∈ attackTargets rc p) :
    x ∈ attackTargets rc (.node r ps) := by
  simp only [attackTargets]
  exact List.mem_append.mpr
    (Or.inr (List.mem_append.mpr
      (Or.inr (List.mem_flatMap_of_mem hp hx))))

/-- A child's height is below the node's (fuel descent). -/
private theorem child_height_lt (r : Rul A) (ps : List (Arg A))
    (p : Arg A) (hp : p ∈ ps) (k : ℕ)
    (hk : Arg.height (.node r ps) ≤ k + 1) : Arg.height p ≤ k := by
  have hfoldp : Arg.height p ≤ (ps.map Arg.height).foldr max 0 :=
    JurisLean.FullMath.Logic.foldr_max_le _ (Arg.height p)
      (List.mem_map_of_mem hp)
  simp only [Arg.height] at hk
  omega

end Summary

section Factorization
variable {A : Type} [DecidableEq A]

/-- The compiled checker at sufficient fuel hits exactly the summary
positions.  Recursion is driven through the fuel parameter (`Arg` is a
nested inductive; `induction` does not apply) with `cases` on the tree
— the same skeleton as the repository's proved `edgeFuel_iff`. -/
private theorem edgeFuel_iff_summaryDefeat (con : Contrary A)
    (rc : RuleContra A) (a : Arg A) :
    ∀ (k : ℕ) (b : Arg A), Arg.height b ≤ k →
      (edgeFuel con rc a b k = true ↔
        summaryDefeat con rc (Arg.concl a) b) := by
  intro k
  induction k with
  | zero =>
      intro b hb
      cases b with
      | leaf c =>
          simp only [edgeFuel, summaryDefeat, attackTargets]
          exact ⟨fun h => ⟨c, List.mem_singleton.mpr rfl, h⟩,
            fun hc => by
              obtain ⟨x, hx, h⟩ := hc
              have hxc : x = c := List.mem_singleton.mp hx
              subst hxc
              exact h⟩
      | node r ps =>
          simp only [Arg.height] at hb
          omega
  | succ k ih =>
      intro b hb
      cases b with
      | leaf c =>
          simp only [edgeFuel, summaryDefeat, attackTargets]
          exact ⟨fun h => ⟨c, List.mem_singleton.mpr rfl, h⟩,
            fun hc => by
              obtain ⟨x, hx, h⟩ := hc
              have hxc : x = c := List.mem_singleton.mp hx
              subst hxc
              exact h⟩
      | node r ps =>
          simp only [edgeFuel, Bool.or_eq_true, List.any_eq_true, or_assoc,
                     summaryDefeat, exists_or]
          constructor
          · rintro (h1 | ⟨p, hp, h2⟩ | h3 | ⟨p, hp, h4⟩)
            · exact ⟨r.head, head_mem_attackTargets rc (.node r ps), h1⟩
            · exact ⟨Arg.concl p, child_concl_mem_attackTargets hp, h2⟩
            · exact ⟨rc r, rule_target_mem_attackTargets, h3⟩
            · obtain ⟨x, hx, hcon⟩ :=
                (ih p (child_height_lt r ps p hp k hb)).mp h4
              exact ⟨x, mem_attackTargets_of_child hp hx, hcon⟩
          · rintro ⟨x, hx, hcon⟩
            simp only [attackTargets] at hx
            rcases List.mem_append.mp hx with hx | hx
            · rcases List.mem_cons.mp hx with hx | hx
              · subst hx
                exact Or.inl hcon
              · obtain ⟨p, hp, hpx⟩ := List.mem_map.mp hx
                subst hpx
                exact Or.inr (Or.inl ⟨p, hp, hcon⟩)
            · rcases List.mem_append.mp hx with hx | hx
              · have hx' : x = rc r := List.mem_singleton.mp hx
                subst hx'
                exact Or.inr (Or.inr (Or.inl hcon))
              · obtain ⟨p, hp, hxp⟩ := List.mem_flatMap.mp hx
                exact Or.inr (Or.inr (Or.inr
                  ⟨p, hp, (ih p (child_height_lt r ps p hp k hb)).mpr
                    ⟨x, hxp, hcon⟩⟩))

/-- §4.3 factorization, soundness direction: every tree-level defeat is
witnessed by a position in the target's summary list — via the
repository's proved `edgeFuel_iff` reflection at fuel = the target's
height, transferred to the summary by the bridge lemma above. -/
theorem defeat_implies_summaryDefeat {con : Contrary A} {rc : RuleContra A}
    {a b : Arg A} (h : Defeat A con rc a b) :
    summaryDefeat con rc (Arg.concl a) b :=
  (edgeFuel_iff_summaryDefeat con rc a (Arg.height b) b (le_refl _)).mp
    ((edgeFuel_iff con rc a (Arg.height b) b (le_refl _)).mpr h)

/-- §4.3 factorization, completeness direction: every summary-level hit
is realized by a tree-level defeat of the GIVEN attacker — the
constructors read the attacker only through its conclusion, and the
summary hit supplies exactly that clash.  Path witnesses ride the real
child positions (the lift chain descends with the fuel). -/
theorem summaryDefeat_implies_defeat {con : Contrary A} {rc : RuleContra A}
    (a : Arg A) : ∀ (k : ℕ) (b : Arg A), Arg.height b ≤ k →
      summaryDefeat con rc (Arg.concl a) b → Defeat A con rc a b := by
  intro k
  induction k with
  | zero =>
      intro b hb hsum
      cases b with
      | leaf c =>
          obtain ⟨x, hx, hcon⟩ := hsum
          simp only [attackTargets] at hx
          have hxc : x = c := List.mem_singleton.mp hx
          have hc : con (Arg.concl a) c = true := by rw [← hxc]; exact hcon
          exact Defeat.rebut a (.leaf c) hc
      | node r ps =>
          simp only [Arg.height] at hb
          omega
  | succ k ih =>
      intro b hb hsum
      cases b with
      | leaf c =>
          obtain ⟨x, hx, hcon⟩ := hsum
          simp only [attackTargets] at hx
          have hxc : x = c := List.mem_singleton.mp hx
          have hc : con (Arg.concl a) c = true := by rw [← hxc]; exact hcon
          exact Defeat.rebut a (.leaf c) hc
      | node r ps =>
          obtain ⟨x, hx, hcon⟩ := hsum
          simp only [attackTargets] at hx
          rcases List.mem_append.mp hx with hx | hx
          · rcases List.mem_cons.mp hx with hx | hx
            · subst hx
              exact Defeat.rebut a (.node r ps) hcon
            · obtain ⟨p, hp, hpx⟩ := List.mem_map.mp hx
              subst hpx
              exact Defeat.undermine a r ps p hp hcon
          · rcases List.mem_append.mp hx with hx | hx
            · have hx' : x = rc r := List.mem_singleton.mp hx
              subst hx'
              exact Defeat.undercut a r ps hcon
            · obtain ⟨p, hp, hxp⟩ := List.mem_flatMap.mp hx
              exact Defeat.lift a r ps p hp
                (ih p (child_height_lt r ps p hp k hb) ⟨x, hxp, hcon⟩)

/-- §4.3 factorization for this fragment — the full biconditional:
tree-level defeat between two argument trees is DECIDED by the finite
summary observables (the attacker's head conclusion and the target's
position list).  The two halves compose at fuel = the target's height;
no tree shape, fuel, or identity leaks into the deciding side. -/
theorem defeat_iff_summaryDefeat (con : Contrary A) (rc : RuleContra A)
    (a b : Arg A) :
    Defeat A con rc a b ↔ summaryDefeat con rc (Arg.concl a) b :=
  ⟨defeat_implies_summaryDefeat,
    fun h => summaryDefeat_implies_defeat a (Arg.height b) b (le_refl _) h⟩

end Factorization

section GateKinds
variable {A : Type} [DecidableEq A]

/-! ### The four gate kinds (§4.3 rows exception / authority / scope /
procedure), following the `rc`-perimeter pattern.

A gate attack does NOT clash with a conclusion: the attacker's
conclusion IS the named `GateBlocked g` atom, and the attack lands on
the target's use of the guarded rule.  The guard perimeter is
`gatePerimeter : Rul A → List A` — for each rule the (finite) list of
gate-block atoms its guarded slots license.  Reading it through
`attackTargets` would conflate gate hits with clashes, so the gate
target list is separate: `gateTargets` collects the perimeter atoms of
every rule in the tree.  No preference is consulted for any gate kind
(§4.3: only rebut/undermine read `Stronger`). -/

/-- The gate perimeter of a rule: the atoms `GateBlocked g` that block
its guarded uses.  Carried by the environment, like `rc`. -/
abbrev GatePerimeter (A : Type) := Rul A → List A

/-- Gate attack kinds (§4.3).  All four share the same clause shape:
the attacker concludes exactly the gate-block atom of a guarded slot the
target actually uses; they differ only in the guard kind, which lives
in the perimeter's tag. -/
inductive GateDefeat (A : Type) (gp : GatePerimeter A) :
    Arg A → Arg A → Prop
  /-- Gate hit on the target's own rule use. -/
  | gate (a : Arg A) (r : Rul A) (ps : List (Arg A))
      (hg : Arg.concl a ∈ gp r) :
      GateDefeat A gp a (.node r ps)
  /-- Subargument lifting of a gate hit. -/
  | lift (a : Arg A) (r : Rul A) (ps : List (Arg A)) (p : Arg A)
      (hp : p ∈ ps) (h : GateDefeat A gp a p) :
      GateDefeat A gp a (.node r ps)

/-- Every guard atom of every rule in the tree — the finite gate-target
list the summary level reads. -/
def gateTargets (gp : GatePerimeter A) : Arg A → List A
  | .leaf _ => []
  | .node r ps => gp r ++ ps.flatMap (gateTargets gp)

/-- The summary-level gate predicate: the attacker's head conclusion is
one of the tree's guard atoms.  Reads only the head observable and the
gate-target list — never the trees. -/
def summaryGateDefeat (gp : GatePerimeter A) (s : A) (t : Arg A) : Prop :=
    s ∈ gateTargets gp t

/-- The perimeter of the target's own rule is in the gate list. -/
theorem own_gate_mem_gateTargets {gp : GatePerimeter A} {r : Rul A}
    {ps : List (Arg A)} {x : A} (hx : x ∈ gp r) :
    x ∈ gateTargets gp (.node r ps) := by
  simp only [gateTargets]
  exact List.mem_append.mpr (Or.inl hx)

/-- A child's gate position is in the parent's gate list. -/
theorem mem_gateTargets_of_child {gp : GatePerimeter A} {r : Rul A}
    {ps : List (Arg A)} {p : Arg A} {x : A}
    (hp : p ∈ ps) (hx : x ∈ gateTargets gp p) :
    x ∈ gateTargets gp (.node r ps) := by
  simp only [gateTargets]
  exact List.mem_append.mpr
    (Or.inr (List.mem_flatMap_of_mem hp hx))

/-- §4.3 gate factorization, soundness: every gate defeat is witnessed
by the attacker's conclusion in the gate-target list. -/
theorem gateDefeat_implies_summary {gp : GatePerimeter A} {a b : Arg A}
    (h : GateDefeat A gp a b) : summaryGateDefeat gp (Arg.concl a) b := by
  induction h with
  | gate r ps hg => exact own_gate_mem_gateTargets hg
  | lift r ps p hp _ ih => exact mem_gateTargets_of_child hp ih

/-- §4.3 gate factorization, completeness: every summary-level gate hit
is realized by a gate defeat — fuel-driven recursion on the tree
(`induction` is unavailable on the nested `Arg`). -/
theorem summary_implies_gateDefeat (gp : GatePerimeter A) (a : Arg A) :
    ∀ (k : ℕ) (b : Arg A), Arg.height b ≤ k →
      summaryGateDefeat gp (Arg.concl a) b → GateDefeat A gp a b := by
  intro k
  induction k with
  | zero =>
      intro b _ hsum
      cases b with
      | leaf _ =>
          simp only [summaryGateDefeat, gateTargets] at hsum
          simp at hsum
      | node r ps =>
          have h1 : 1 ≤ Arg.height (.node r ps) := by
            simp only [Arg.height]; omega
          omega
  | succ k ih =>
      intro b hb hsum
      cases b with
      | leaf _ =>
          simp only [summaryGateDefeat, gateTargets] at hsum
          simp at hsum
      | node r ps =>
          simp only [summaryGateDefeat, gateTargets] at hsum
          rcases List.mem_append.mp hsum with hg | hg
          · exact GateDefeat.gate a r ps hg
          · obtain ⟨p, hp, hxp⟩ := List.mem_flatMap.mp hg
            exact GateDefeat.lift a r ps p hp
              (ih p (child_height_lt r ps p hp k hb) hxp)

/-- §4.3 gate factorization — the full biconditional for the four gate
kinds (exception / authority / scope / procedure share the clause
shape; the kind tag rides the perimeter). -/
theorem gateDefeat_iff_summaryDefeat (gp : GatePerimeter A)
    (a b : Arg A) :
    GateDefeat A gp a b ↔ summaryGateDefeat gp (Arg.concl a) b :=
  ⟨gateDefeat_implies_summary,
    fun h => summary_implies_gateDefeat gp a (Arg.height b) b (le_refl _) h⟩

end GateKinds

end JurisLean.Seams.UnifiedArgumentation
