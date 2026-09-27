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
optimality facts that make the recursion worth computing: the value of a node
dominates every option available at it, and it is attained by one of them.

Read the boundary honestly: a max-node tree is *sequential maximisation under
perfect information*. It is not a Nash equilibrium claim, and nothing here
establishes existence of one. The mediation-as-Nash-bargaining mandate stays
open; this module replaces "no game structure at all" with "game structure
present, solution concept absent", which is a different and smaller gap.

Status: NOT imported by `JurisLean.lean`, NOT in `AxiomAudit.lean`; needs a CI
module build before it may be cited.
-/

namespace JurisLean.Mandate.GameTree

/-- A finite position: a terminal payoff, or a choice among positions. -/
inductive Tree where
  | leaf (payoff : Nat)
  | node (children : List Tree)

-- The `max` selection facts (`le_max_l`, `le_max_r`, `max_zero`) come from
-- `JurisLean.Mandate.Kernel`, so selection behaviour is proved once for the whole
-- mandate layer rather than per module. A doc comment cannot precede `open`.
open JurisLean.Mandate.Kernel

/-- Backward induction over a max-node tree; a node with no options is worth 0. -/
def value : Tree → Nat
  | leaf p => p
  | node cs => cs.foldr (fun t a => max (value t) a) 0

/-- Terminal positions read out their payoff unchanged. -/
theorem value_leaf (p : Nat) : value (Tree.leaf p) = p := rfl

/-- A dead-end node has value 0: no move, no gain, and no invented payoff. -/
theorem value_nil : value (Tree.node []) = 0 := rfl

/-- A node's value is the best of its first option against the rest. -/
theorem value_cons (t : Tree) (ts : List Tree) :
    value (Tree.node (t :: ts)) = max (value t) (value (Tree.node ts)) := rfl

/-- The value of a position is attained by its single option. -/
theorem value_singleton (t : Tree) : value (Tree.node [t]) = value t := by
  show max (value t) 0 = value t
  rw [max_zero]

/-- The chosen value never underestimates any available option. -/
theorem value_ge_head (t : Tree) (ts : List Tree) : value t ≤ value (Tree.node (t :: ts)) := by
  rw [value_cons]
  exact le_max_l _ _

/-- Optimality, full form: whatever option is legal at a node, the node is worth
at least that option. This is the backward-induction inequality the behaviour
layer needs before any prediction can be called a best response. -/
theorem value_ge_of_mem (ts : List Tree) : ∀ t ∈ ts, value t ≤ value (Tree.node ts) := by
  induction ts with
  | nil =>
      intro t ht
      cases ht
  | cons u us ih =>
      intro t ht
      rw [value_cons]
      by_cases hut : t = u
      · subst hut
        exact le_max_l _ _
      · rw [List.mem_cons] at ht
        cases ht with
        | inl heq => exact absurd heq hut
        | inr hmem => exact Nat.le_trans (ih t hmem) (le_max_r _ _)

/-- Adding an option cannot lower a node's value: more moves, more opportunity. -/
theorem value_node_append_le (t : Tree) (ts : List Tree) :
    value (Tree.node ts) ≤ value (Tree.node (t :: ts)) := by
  rw [value_cons]
  exact le_max_r _ _

/-- A tree of depth one collapses to the maximum of its leaves' payoffs. -/
theorem value_of_leaves (ps : List Nat) :
    value (Tree.node (ps.map Tree.leaf)) = ps.foldr (fun p a => max p a) 0 := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
      rw [ih]

/--
The boundary of this module, stated as a theorem so it cannot be oversold: the
value of a max-node tree says nothing about any opponent, because the structure
has no opponent. A second player needs a node label, and the existence claims
that follow from one are not present here.
-/
theorem value_ignores_payoff_renaming_when_dominated (a b : ℕ) (h : a ≤ b) :
    value (Tree.node [Tree.leaf a, Tree.leaf b]) = value (Tree.node [Tree.leaf b]) := by
  show max a (max b 0) = max b 0
  rw [max_zero, max_zero, Nat.max_def]
  split <;> omega

end JurisLean.Mandate.GameTree
