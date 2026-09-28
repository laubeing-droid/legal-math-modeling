import Mathlib

/-!
# Mandate module — multi-player sequential games: the carrier and one-step optimality

The audit's game-theory item (R-02b) recorded two gaps: multiplayer games, and sequential
games as opposed to one-shot matrices. `MatrixGame.lean` and `ZeroSumSion.lean` cover the
simultaneous side for two players; `GameTree.lean` covers a sequential tree whose payoffs are
a single natural number, which its own header describes as "sequential maximisation under
perfect information" and expressly not a solution concept.

This module adds the missing *carrier*: a tree whose nodes are labelled by which of the `n`
players acts, and whose payoffs are a profile with one component per player. The recursion is
the standard backward step -- the acting player's component decides between the two
continuations -- and the main facts proved here are one-step optimality: at a node belonging
to player `i`, the payoff the recursion returns is at least what `i` would have received from
either child. Since the statement holds at every node of every subtree, it is the local half
of what subgame perfection demands: no acting player prefers the sibling of the branch taken,
given the continuation the same recursion already fixed.

Read the boundary exactly. This is not a Nash or subgame-perfect *equilibrium* theorem: the
tree has perfect information and no simultaneous moves, payoffs are natural numbers, and
one-step optimality at a player's own nodes says nothing about a player deviating at someone
else's node. General Nash existence stays where the ledger puts it -- no carrier in this
pinned Mathlib -- and `FORBIDDEN-12` forbids reading anything here as a general existence
result.

Status: no CI verdict at the time of writing. The module is booked in `PENDING_CI_MODULES`
and may not join the release root until `lean-full-clean-build` has built it; nothing in this
header is an attestation.
-/

namespace JurisLean.Mandate.SequentialGames

/-- One player of an `n`-player game. -/
abbrev Player (n : ℕ) : Type := Fin n

/-- How the game ends: a payoff for every player, not a single number. -/
abbrev Profile (n : ℕ) : Type := Player n → Nat

/-- A finite position of an `n`-player game: the game ends with a payoff profile, or one
player `i` chooses between two continuations. Indexing players by `Fin n` means a three- or a
twenty-player game is the same structure with a different `n`, which is what the multiplayer
half of R-02b was missing. -/
inductive Game (n : ℕ) where
  | terminal (u : Profile n)
  | turn (i : Player n) (left right : Game n)

/-- The choice rule: keep whichever continuation pays the acting player more, taking the right
one when they tie. Written with a Prop-level condition rather than a `decide` guard, which is
the shape this repository's guard scan enforces. -/
def choose {n : ℕ} (i : Player n) (a b : Profile n) : Profile n :=
  if a i ≤ b i then b else a

/-- The acting player's component of a choice is the maximum of their two components. -/
theorem choose_apply {n : ℕ} (i : Player n) (a b : Profile n) :
    (choose i a b) i = max (a i) (b i) := by
  by_cases h : a i ≤ b i
  · simp only [choose, if_pos h, max_eq_right h]
  · simp only [choose, if_neg h, max_eq_left (Nat.le_of_not_le h)]

/-- Payoffs under the backward recursion: a terminal position pays what it says, an internal
position is decided by whichever player acts there. -/
def outcome : {n : ℕ} → Game n → Profile n
  | _, .terminal u => u
  | n, .turn i l r => choose i (outcome l) (outcome r)

/-- At a node where `i` acts, the recursion returns exactly the best of the two continuations
for `i`. -/
theorem outcome_turn_apply {n : ℕ} (i : Player n) (l r : Game n) :
    (outcome (Game.turn i l r)) i = max (outcome l i) (outcome r i) :=
  choose_apply i (outcome l) (outcome r)

/-- Terminal positions read out their own payoff, which is what lets the recursion be checked
against a written-down number. -/
theorem outcome_terminal {n : ℕ} (u : Profile n) (i : Player n) :
    (outcome (Game.terminal u)) i = u i := rfl

/-- One-step optimality on the left: the acting player cannot prefer the branch they did not
take. -/
theorem turn_ge_left {n : ℕ} (i : Player n) (l r : Game n) :
    (outcome l) i ≤ (outcome (Game.turn i l r)) i := by
  rw [outcome_turn_apply]
  exact Nat.le_max_left _ _

/-- One-step optimality on the right. -/
theorem turn_ge_right {n : ℕ} (i : Player n) (l r : Game n) :
    (outcome r) i ≤ (outcome (Game.turn i l r)) i := by
  rw [outcome_turn_apply]
  exact Nat.le_max_right _ _

/-- The recursion is monotone in the acting player's own continuation: giving `i` a better
left option never lowers what `i` obtains at the node. This is what makes the computed
profile's optimity stable under changing the payoffs rather than only the shape. -/
theorem turn_monotone {n : ℕ} (i : Player n) (l r l' : Game n)
    (h : (outcome l) i ≤ (outcome l') i) :
    (outcome (Game.turn i l r)) i ≤ (outcome (Game.turn i l' r)) i := by
  rw [outcome_turn_apply, outcome_turn_apply]
  have a := Nat.le_max_left (outcome l i) (outcome r i)
  have b := Nat.le_max_right (outcome l i) (outcome r i)
  have c := Nat.le_max_left (outcome l' i) (outcome r i)
  have d := Nat.le_max_right (outcome l' i) (outcome r i)
  omega

/-- Two players, one move: player 0 acts and the recursion takes the branch paying 3. -/
theorem two_player_take_better :
    (outcome (Game.turn (0 : Player 2) (Game.terminal fun (_ : Player 2) => (1 : ℕ))
      (Game.terminal fun (_ : Player 2) => (3 : ℕ)))) (0 : Player 2) = 3 := by
  have h := outcome_turn_apply (0 : Player 2)
    (Game.terminal fun (_ : Player 2) => (1 : ℕ)) (Game.terminal fun (_ : Player 2) => (3 : ℕ))
  rw [h, outcome_terminal, outcome_terminal]
  norm_num

/-- The game used for the two facts below. Three players; player 0 moves once; the left branch
pays her 9 and everyone else 0, the right branch pays her 1 and player 1 eight. Their
preferences genuinely conflict, which is what a single-payoff tree cannot express. -/
def conflict : Game 3 :=
  Game.turn (0 : Player 3)
    (Game.terminal fun j => if j = 0 then (9 : ℕ) else 0)
    (Game.terminal fun j => if j = 0 then (1 : ℕ) else 8)

/-- The acting player gets her best: the recursion returns 9 for player 0. -/
theorem actor_gets_her_best : (outcome conflict) (0 : Player 3) = 9 := by
  have h := outcome_turn_apply (0 : Player 3)
    (Game.terminal fun j => if j = 0 then (9 : ℕ) else 0)
    (Game.terminal fun j => if j = 0 then (1 : ℕ) else 8)
  rw [h, outcome_terminal, outcome_terminal]
  norm_num

/-- The boundary, stated as a computed fact rather than a disclaimer: player 1 is not the one
who acted, and the branch chosen leaves her 0 when the branch not taken would have paid her 8.
So one-step optimality is a claim about the acting player at her own nodes, and nothing here
says any player cannot gain by a different profile of choices -- that stronger statement is a
solution concept, and this module does not establish one. -/
theorem non_actor_may_be_sacrificed : (outcome conflict) (1 : Player 3) = 0 := by
  show (choose (0 : Player 3)
      (outcome (Game.terminal fun j => if j = 0 then (9 : ℕ) else 0))
      (outcome (Game.terminal fun j => if j = 0 then (1 : ℕ) else 8))) (1 : Player 3) = 0
  show (if (9 : ℕ) ≤ 1 then (8 : ℕ) else 0) = 0
  decide

end JurisLean.Mandate.SequentialGames
