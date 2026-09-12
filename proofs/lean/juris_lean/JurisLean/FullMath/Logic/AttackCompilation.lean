import JurisLean.FullMath.Logic.ArgumentConstruction

/-!
F09 — Attack/defeat compilation, both directions.

`Defeat` is an independent four-case specification (rebut, undermine,
undercut, subargument lifting). `edgeImpl` is the compiled boolean checker.
We prove `edgeImpl a b = true ↔ Defeat a b` by structural induction on the
target. Unknown priority policies keep edges undecided — they are filtered
into a pending set, never silently dropped.
-/

namespace JurisLean.FullMath.Logic

section Attack
variable {A : Type} [DecidableEq A]

/-- Declared clash relation between atoms (e.g. `p` vs `¬p`). -/
abbrev Contrary (A : Type) := A → A → Bool

/-- What undercuts a rule. -/
abbrev RuleContra (A : Type) := Rul A → A

/-- Independent defeat specification over direct children. -/
inductive Defeat (A : Type) (con : Contrary A) (rc : RuleContra A) : Arg A → Arg A → Prop
  /-- Rebut: the attacker's conclusion clashes with the target's conclusion. -/
  | rebut (a b : Arg A) (h : con (Arg.concl a) (Arg.concl b) = true) :
      Defeat con rc a b
  /-- Undermine: the attacker's conclusion clashes with a direct child's
  conclusion. -/
  | undermine (a : Arg A) (r : Rul A) (ps : List (Arg A)) (p : Arg A)
      (hp : p ∈ ps) (h : con (Arg.concl a) (Arg.concl p) = true) :
      Defeat con rc a (.node r ps)
  /-- Undercut: the attacker's conclusion clashes with what licenses the
  target's rule. -/
  | undercut (a : Arg A) (r : Rul A) (ps : List (Arg A))
      (h : con (Arg.concl a) (rc r) = true) :
      Defeat con rc a (.node r ps)
  /-- Subargument lifting: the attacker already defeats a direct child. -/
  | lift (a : Arg A) (r : Rul A) (ps : List (Arg A)) (p : Arg A)
      (hp : p ∈ ps) (h : Defeat con rc a p) :
      Defeat con rc a (.node r ps)

/-- Compiled boolean checker, structural in the target. -/
def edgeImpl (con : Contrary A) (rc : RuleContra A) : Arg A → Arg A → Bool
  | a, .leaf c => con (Arg.concl a) c
  | a, .node r ps =>
    con (Arg.concl a) (Arg.concl (.node r ps))
    || ps.any (fun p => con (Arg.concl a) (Arg.concl p))
    || con (Arg.concl a) (rc r)
    || ps.any (fun p => edgeImpl con rc a p)

/-- F09(a): compiled edges reflect the independent specification. -/
theorem edge_iff_spec (con : Contrary A) (rc : RuleContra A) (a : Arg A) :
    ∀ b : Arg A, edgeImpl con rc a b = true ↔ Defeat con rc a b := by
  intro b
  induction b with
  | leaf c =>
    constructor
    · intro h
      exact Defeat.rebut a (.leaf c) h
    · intro h
      cases h with
      | rebut _ _ hclash => exact hclash
  | @node r ps ih =>
    constructor
    · intro h
      simp only [edgeImpl, Bool.or_eq_true, List.any_eq_true] at h
      rcases h with hrebut | hunder | hcut | hlift
      · exact Defeat.rebut a (.node r ps) hrebut
      · obtain ⟨p, hp, hclash⟩ := hunder
        exact Defeat.undermine a r ps p hp hclash
      · exact Defeat.undercut a r ps hcut
      · obtain ⟨p, hp, hd⟩ := hlift
        exact Defeat.lift a r ps p hp ((ih p).mp hd)
    · intro h
      simp only [edgeImpl, Bool.or_eq_true, List.any_eq_true]
      cases h with
      | rebut _ _ hclash => exact Or.inl hclash
      | undermine _ _ _ _ hp hclash =>
        exact Or.inr (Or.inl (Or.inl ⟨_, hp, hclash⟩))
      | undercut _ _ _ hclash => exact Or.inr (Or.inl (Or.inr hclash))
      | lift _ _ _ _ hp hd =>
        exact Or.inr (Or.inr ⟨_, hp, (ih _).mpr hd⟩)

/-! Priority adjudication: undecided edges are preserved, never dropped. -/

/-- Priority adjudication outcomes. -/
inductive PriorityDecision where
  | attackerPreferred
  | targetPreferred
  | undecided

/-- Adjudicate with a declared policy function; anything not known is
undecided. -/
def adjudicate (policy : Arg A → Arg A → Option Bool) (a b : Arg A) :
    PriorityDecision :=
  match policy a b with
  | some true => .attackerPreferred
  | some false => .targetPreferred
  | none => .undecided

/-- Pending edges under an unknown policy. -/
def pendingEdges (edges : List (Arg A × Arg A)) (policy : Arg A → Arg A → Option Bool) :
    List (Arg A × Arg A) :=
  edges.filter (fun e => adjudicate policy e.1 e.2 = .undecided)

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
