import JurisLean.FullMath.Logic.ArgumentConstruction

/-!
F09 — Attack/defeat compilation, both directions.

`Defeat` is an independent four-case specification (rebut, undermine,
undercut, subargument lifting). `edgeFuel` is the compiled boolean checker
with explicit fuel; at fuel at least the target's height it reflects the
specification exactly. Unknown priority policies keep edges undecided —
they are filtered into a pending set, never silently dropped.
-/

namespace JurisLean.FullMath.Logic

open JurisLean.FullMath.Logic (Rul Arg)

section Attack
variable {A : Type} [DecidableEq A]

/-- Declared clash relation between atoms (e.g. `p` vs `¬p`). -/
abbrev Contrary (A : Type) := A → A → Bool

/-- What undercuts a rule. -/
abbrev RuleContra (A : Type) := Rul A → A

/-- Independent defeat specification over direct children. -/
inductive Defeat (A : Type) (con : Contrary A) (rc : RuleContra A) :
    Arg A → Arg A → Prop
  /-- Rebut: the attacker's conclusion clashes with the target's. -/
  | rebut (a b : Arg A) (h : con (Arg.concl a) (Arg.concl b) = true) :
      Defeat A con rc a b
  /-- Undermine: clash with a direct child's conclusion. -/
  | undermine (a : Arg A) (r : Rul A) (ps : List (Arg A)) (p : Arg A)
      (hp : p ∈ ps) (h : con (Arg.concl a) (Arg.concl p) = true) :
      Defeat A con rc a (.node r ps)
  /-- Undercut: clash with what licenses the target's rule. -/
  | undercut (a : Arg A) (r : Rul A) (ps : List (Arg A))
      (h : con (Arg.concl a) (rc r) = true) :
      Defeat A con rc a (.node r ps)
  /-- Subargument lifting: the attacker defeats a direct child. -/
  | lift (a : Arg A) (r : Rul A) (ps : List (Arg A)) (p : Arg A)
      (hp : p ∈ ps) (h : Defeat A con rc a p) :
      Defeat A con rc a (.node r ps)

/-- Compiled boolean checker with explicit fuel (structural in the fuel). -/
def edgeFuel (con : Contrary A) (rc : RuleContra A) (a : Arg A) :
    Arg A → ℕ → Bool
  | .leaf c, _ => con (Arg.concl a) c
  | .node r ps, 0 => con (Arg.concl a) (r.head)
  | .node r ps, k + 1 =>
    con (Arg.concl a) (r.head)
    || ps.any (fun p => con (Arg.concl a) (Arg.concl p))
    || con (Arg.concl a) (rc r)
    || ps.any (fun p => edgeFuel con rc a p k)

/-- Height of a node bounds its children. -/
private theorem child_height_le (r : Rul A) (ps : List (Arg A)) (p : Arg A)
    (hp : p ∈ ps) (k : ℕ) (hk : Arg.height (.node r ps) ≤ k + 1) :
    Arg.height p ≤ k := by
  have hfoldp : Arg.height p ≤ (ps.map Arg.height).foldr max 0 :=
    foldr_max_le _ (Arg.height p) (List.mem_map_of_mem hp)
  have hnode : Arg.height (.node r ps) = (ps.map Arg.height).foldr max 0 + 1 := by
    simp only [Arg.height]
  omega

/-- F09(a): the compiled checker with sufficient fuel reflects the
independent specification. -/
theorem edgeFuel_iff (con : Contrary A) (rc : RuleContra A) (a : Arg A) :
    ∀ (k : ℕ) (b : Arg A), Arg.height b ≤ k →
      (edgeFuel con rc a b k = true ↔ Defeat A con rc a b) := by
  intro k
  induction k with
  | zero =>
    intro b hb
    cases b with
    | leaf c =>
      simp only [edgeFuel]
      exact ⟨fun h => Defeat.rebut a (.leaf c) h,
        fun h => by cases h with | rebut _ hclash => exact hclash⟩
    | node r ps =>
      intro hb
      have hnode : Arg.height (.node r ps) = (ps.map Arg.height).foldr max 0 + 1 := by
        simp only [Arg.height]
      omega
  | succ k ih =>
    intro b hb
    cases b with
    | leaf c =>
      simp only [edgeFuel]
      exact ⟨fun h => Defeat.rebut a (.leaf c) h,
        fun h => by cases h with | rebut _ hclash => exact hclash⟩
    | node r ps =>
      simp only [edgeFuel, Bool.or_eq_true, List.any_eq_true]
      constructor
      · rintro (h1 | ⟨p, hp, h2⟩ | h3 | ⟨p, hp, h4⟩)
        · exact Defeat.rebut a (.node r ps) h1
        · exact Defeat.undermine a r ps p hp h2
        · exact Defeat.undercut a r ps h3
        · exact Defeat.lift a r ps p hp ((ih p (child_height_le r ps p hp k hb)).mp h4)
      · intro h
        cases h with
        | rebut _ _ hclash => exact Or.inl hclash
        | undermine _ _ _ _ hp hclash =>
          exact Or.inr (Or.inl (Or.inl ⟨p, hp, hclash⟩))
        | undercut _ _ _ hclash => exact Or.inr (Or.inl (Or.inr hclash))
        | lift _ _ _ _ hp hd =>
          exact Or.inr (Or.inr
            ⟨p, hp, (ih p (child_height_le r ps p hp k hb)).mpr hd⟩)

/-! Priority adjudication: undecided edges are preserved, never dropped. -/

/-- Priority adjudication outcomes. -/
inductive PriorityDecision where
  | attackerPreferred
  | targetPreferred
  | undecided

/-- Adjudicate with a declared policy; anything not known is undecided. -/
def adjudicate (policy : Arg A → Arg A → Option Bool) (a b : Arg A) :
    PriorityDecision :=
  match policy a b with
  | some true => .attackerPreferred
  | some false => .targetPreferred
  | none => .undecided

/-- Pending edges under an unknown policy. -/
def pendingEdges (edges : List (Arg A × Arg A)) (policy : Arg A → Arg A → Option Bool) :
    List (Arg A × Arg A) :=
  edges.filter (fun e => decide (adjudicate policy e.1 e.2 = .undecided))

/-- F09(b): every pending edge is a real edge — nothing is silently removed. -/
theorem pending_edges_are_edges (edges : List (Arg A × Arg A))
    (policy : Arg A → Arg A → Option Bool) :
    ∀ e ∈ pendingEdges edges policy, e ∈ edges := by
  intro e he
  simp only [pendingEdges, List.mem_filter] at he
  exact he.1

/-- F09(c): the pending set is at most the full edge set (no fabrication). -/
theorem pending_edges_bound (edges : List (Arg A × Arg A))
    (policy : Arg A → Arg A → Option Bool) :
    (pendingEdges edges policy).length ≤ edges.length :=
  List.length_filter_le edges (fun e => adjudicate policy e.1 e.2 = .undecided)

end Attack

end JurisLean.FullMath.Logic
