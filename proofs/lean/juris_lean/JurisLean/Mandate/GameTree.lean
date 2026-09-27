import Mathlib
import JurisLean.Mandate.Kernel

/-!
# Mandate module D — finite game trees and backward-induction value

The repo had no game tree at all: the audit searched `gameTree|game_tree` across
`proofs/` and found zero hits, `action_decision.py:147-149` declares itself
"NOT a Nash equilibrium solver", and the only Lean "Nash" object was
`Batch4.lean:241 T81_nash_feasible`, an identity about a record field.

What this module supplies is the object the mandate names — an explicit
extensive-form tree with a value defined by backward recursion, and the
optimality facts that make the recursion worth computing: the value of a position
dominates every payoff reachable from it, and it is itself one of those payoffs.

Read the boundary honestly: a max-node tree is *sequential maximisation under
perfect information*. It is not a Nash equilibrium claim, and nothing here
establishes existence of one. The mediation-as-Nash-bargaining mandate stays
open; this module replaces "no game structure at all" with "game structure
present, solution concept absent", which is a different and smaller gap.

Status: imported by the release root and named by `AxiomAudit.lean`; built green
in CI run 36298572193 (subject 0574e2ae4), the first round whose root itself
elaborates this module. Commits after that subject do not inherit the verdict.
-/

namespace JurisLean.Mandate.GameTree

/--
A finite position: a terminal payoff, or a choice between two positions.

Two options rather than a `List` of them is a deliberate modelling choice, and
the compiler forced it. The first version had `node (children : List Tree)` and
`value (.node cs) = cs.foldr (fun t a => max (value t) a) 0`; that recursion sits
under a lambda, so Lean did not compile it structurally, the constructor
equations were not definitional, and `value (Tree.leaf p) = p` failed as `rfl`
(CI runs 36289822066 and 36290409329 both reported it). Binary choice keeps the
recursion structural; an n-option node is written by nesting.
-/
inductive Tree where
  | leaf (payoff : Nat)
  | node (left right : Tree)

-- The `max` selection facts (`le_max_l`, `le_max_r`) come from
-- `JurisLean.Mandate.Kernel`, so selection behaviour is proved once for the whole
-- mandate layer rather than per module. A doc comment cannot precede `open`.
open JurisLean.Mandate.Kernel

/-- Backward induction: a position is worth the better of its two options. -/
def value : Tree → Nat
  | .leaf p => p
  | .node l r => max (value l) (value r)

/-- The payoffs a player can actually reach by playing down the tree. -/
def leaves : Tree → List Nat
  | .leaf p => [p]
  | .node l r => leaves l ++ leaves r

/-- Terminal positions read out their payoff unchanged. -/
theorem value_leaf (p : Nat) : value (Tree.leaf p) = p := rfl

/-- A choice is worth the better of its options, by definition and not by claim. -/
theorem value_node (l r : Tree) : value (Tree.node l r) = max (value l) (value r) := rfl

theorem leaves_leaf (p : Nat) : leaves (Tree.leaf p) = [p] := rfl

theorem leaves_node (l r : Tree) : leaves (Tree.node l r) = leaves l ++ leaves r := rfl

/-- Having an option never lowers the value of the position that has it. -/
theorem value_le_value_left (l r : Tree) : value l ≤ value (Tree.node l r) := le_max_l _ _

theorem value_le_value_right (l r : Tree) : value r ≤ value (Tree.node l r) := le_max_r _ _

/--
Optimality, full form: whatever payoff is reachable from a position, the position
is worth at least that much. This is the backward-induction inequality the
behaviour layer needs before any prediction can be called a best response.
-/
theorem value_ge_of_mem : ∀ (t : Tree) (p : Nat), p ∈ leaves t → p ≤ value t := by
  intro t
  induction t with
  | leaf q =>
      intro p h
      rw [leaves_leaf] at h
      rw [List.mem_singleton] at h
      subst h
      rw [value_leaf]
  | node l r ihl ihr =>
      intro p h
      rw [leaves_node] at h
      rw [List.mem_append] at h
      rw [value_node]
      cases h with
      | inl hl => exact Nat.le_trans (ihl p hl) (le_max_l _ _)
      | inr hr => exact Nat.le_trans (ihr p hr) (le_max_r _ _)

/--
The value is not an invented number: it is one of the payoffs the tree actually
contains. A recursion that returned a value outside `leaves` would fail here,
which is what makes the claim worth stating next to `value_ge_of_mem`.
-/
theorem value_attains (t : Tree) : ∃ p ∈ leaves t, value t = p := by
  induction t with
  | leaf p => exact ⟨p, by simp [leaves], rfl⟩
  | node l r ihl ihr =>
      cases Nat.le_total (value l) (value r) with
      | inl hle =>
          -- The `rfl` pattern substitutes the witness away, so the remaining
          -- membership proof reads `value r ∈ leaves r` (CI run 36292599075 reported
          -- `Unknown identifier` when the branch still named the vanished witness).
          obtain ⟨_, hq, rfl⟩ := ihr
          exact ⟨value r, List.mem_append.mpr (Or.inr hq), max_eq_right hle⟩
      | inr hge =>
          obtain ⟨_, hl, rfl⟩ := ihl
          exact ⟨value l, List.mem_append.mpr (Or.inl hl), max_eq_left hge⟩

/--
The boundary of this module, stated as a theorem so it cannot be oversold: a
dominated option is discarded, and nothing here speaks about an opponent,
because the structure has none. A second player needs a node label, and the
existence claims that follow from one are not present here.
-/
theorem value_ignores_payoff_renaming_when_dominated (a b : ℕ) (h : a ≤ b) :
    value (Tree.node (Tree.leaf a) (Tree.leaf b)) =
      value (Tree.node (Tree.leaf b) (Tree.leaf b)) := by
  show max a b = max b b
  rw [max_eq_right h, max_eq_right (Nat.le_refl _)]

end JurisLean.Mandate.GameTree
