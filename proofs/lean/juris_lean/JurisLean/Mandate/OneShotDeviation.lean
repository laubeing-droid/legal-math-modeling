import Mathlib
import JurisLean.Mandate.SequentialGames

/-!
# Mandate module — the one-shot deviation principle for the recursion-driven profile

`SequentialGames.lean` supplies the carrier: an `n`-player finite tree, a payoff profile
per player, and the backward recursion `outcome` which at a node owned by `i` keeps whichever
continuation pays `i` more. Its own header states the boundary -- one-step optimality is not
an equilibrium claim -- and this module is the next honest step rather than a leap: it gives
the tree *history-based strategies*, plays the tree against a strategy profile, and proves
that the profile the recursion computes cannot be beaten by changing one decision at one node.

The three pieces, and nothing more:

* `Strat n = List Bool → Bool` and `Strats n = Player n → Strat n` -- a strategy names a
  branch as a function of the sequence of earlier choices, so a player's plan is a function
  of the history rather than a single move.
* `go` and `play` -- `play g s` runs `g` from the empty history; at a node owned by `i` it
  asks `(s i h)` for the branch, with `h` the path taken so far. `go` carries that path as the
  accumulator of the returned function, so the recursion stays structural on the game alone.
* `brute` -- the profile the recursion computes: `atPath g h` finds the node of `g` reached by
  the path `h`, and `brute g` answers there with the child `outcome` prefers. `deviate g i h b`
  is `brute g` with one flip: `i`'s answer at history `h` replaced by `b`, every other answer
  unchanged.

The two substantive results are `go_exact` (a profile that answers every node the way the
recursion does reproduces `outcome`, hence `play_brute : play g (brute g) = outcome g`) and
`go_bound`, whose instances `one_shot_deviation` and `one_shot_deviation_le_brute` are the
module's namesake: for any game, any player `i`, any history label and any branch `b`,

    (play g (deviate g i hpath b)) i <= (play g (brute g)) i,

and the same bound with the right-hand side written as `(outcome g) i`. Since
`b` is universally quantified, it covers the flipped answer as well as the unchanged one, so
one flip at one node never raises the payoff of the player who flips. The worked three-player,
depth-two tree at the end computes both sides: the actor's payoff under `brute` is 4 and under
her own single flip at the root it is 1, and `tree_deviation_strictly_worse` records the strict
loss, which is what keeps the inequality from being vacuous.

## Conventions

`false` means the left child, `true` the right child. This matches `choose`, which takes the
*right* child when the acting player's two components tie; `brute` therefore answers `true`
exactly when `(outcome l) i <= (outcome r) i`. A strategy is consulted at the concatenation of
the elapsed history and the path inside the current subtree, and `brute` reads only its own
subtree-relative path -- which is why the induction hypotheses below are stated with a prefix.

## What is NOT proved, read before citing anything here

* One flip at one node only. The profile `deviate g i hpath b` differs from `brute g` at the
  single labelled point `(i, hpath)`; `go_bound` grants `i` as much, and no more, because its
  hypothesis only requires agreement with `brute` at the other players' answers. That no
  *multi-node* deviation by the same player helps requires the one-shot deviation principle's
  induction over all of that player's histories at once (Kuhn's lemma, and with it the step
  from one-flip to best-response), and it is NOT established here. `go_exact` and `go_bound`
  are structural and stop short of it; the multi-flip version is an explicit open step.
* Consequently nothing here is a Nash or subgame-perfect equilibrium theorem, and no claim is
  made that `brute` is an equilibrium profile. `SequentialGames.non_actor_may_be_sacrificed`
  remains the standing counter-warning: a player who does not own the acting node can be left
  worse off by the branch the actor takes.
* A player deviating at someone else's node is not modelled: `deviate` flips the answer filed
  under `(i, hpath)`, and `go` consults `s k h` only at nodes owned by `k`. If no node owned by
  `i` carries the label `hpath`, the flip is inert and the inequality is still true -- the
  theorem covers that case rather than excluding it.
* There is no model of imperfect information or information sets. Histories are full choice
  sequences, every node is reached by exactly one path, and a strategy's dependence on
  `List Bool` is therefore weaker than the usual behavioural-strategy notion, which must be
  constant across an information set. No chance nodes, no simultaneous moves, no infinite
  trees, payoffs in `Nat`.
* `atPath` answers `none` for a path that leaves the tree, and `brute` answers `false` there;
  those answers are reachable only by a mislabelled history and are given no meaning.

Status: no CI verdict exists for this file at the time of writing. It is not attested by any
build, and nothing in it is an attestation -- including of the theorems of
`SequentialGames.lean` it imports. Joining the release root (`JurisLean.lean`) and being named
by `AxiomAudit.lean` are separate steps that each need their own green CI round; both are owned
by another process and neither is claimed here.
-/

namespace JurisLean.Mandate.OneShotDeviation

open JurisLean.Mandate.SequentialGames

/-! ## History-based strategies -/

/-- A positional strategy for one player: given the sequence of choices already made, name the
branch to take. `false` is the left child, `true` the right child. -/
abbrev Strat (n : ℕ) : Type := List Bool → Bool

/-- One strategy per acting player. -/
abbrev Strats (n : ℕ) : Type := Player n → Strat n

/-! ## Playing a tree against a profile -/

/-- The recursion on the game, with the elapsed history as the accumulator of the returned
function. A node owned by `i` asks `i`'s strategy about the history so far and continues into
the chosen child with that choice appended, so the history is the path from the root in the
order the choices were made. Written this way because the recursion must stay structural on the
game alone. -/
def go {n : ℕ} (g : Game n) : List Bool → Strats n → Profile n
  | .terminal u => fun _ _ => u
  | .turn i l r => fun h s =>
      if (s i h = true) then go r (h ++ [true]) s else go l (h ++ [false]) s

/-- The result of play: run the game from the empty history. -/
def play {n : ℕ} (g : Game n) (s : Strats n) : Profile n := go g ([] : List Bool) s

/-- A terminal position pays what it says, whatever the history and whatever the plans. -/
theorem go_terminal {n : ℕ} (u : Profile n) (h : List Bool) (s : Strats n) :
    go (Game.terminal u) h s = u := rfl

/-- Playing a node owned by `i` continues into the child `i`'s strategy names at this history. -/
theorem go_turn_apply {n : ℕ} (i : Player n) (l r : Game n) (h : List Bool) (s : Strats n) :
    go (Game.turn i l r) h s =
      if (s i h = true) then go r (h ++ [true]) s else go l (h ++ [false]) s := rfl

/-- Playing a terminal position yields its profile: no plan can change a payoff that is already
written down. -/
theorem play_terminal {n : ℕ} (u : Profile n) (s : Strats n) :
    play (Game.terminal u) s = u := rfl

/-- At the root, `play` equals the play of the child the acting player's strategy selects at the
empty history. The child is entered with the one-step history, not the empty one, which is
exactly why the lemmas below are stated with a history prefix. -/
theorem play_turn_follows {n : ℕ} (i : Player n) (l r : Game n) (s : Strats n) :
    play (Game.turn i l r) s =
      if (s i ([] : List Bool) = true) then go r [true] s else go l [false] s := rfl

/-! ## The strategy profile the recursion computes -/

/-- The node reached by a path, `none` if the path leaves the tree. The head of the list is the
first choice made, matching the order in which `go` appends. Recursion is on the game, with the
path as the accumulator of the returned function, so the equations below are definitional. -/
def atPath {n : ℕ} (g : Game n) : List Bool → Option (Game n)
  | .terminal u => fun h => match h with
      | [] => some (Game.terminal u)
      | _ :: _ => none
  | .turn i l r => fun h => match h with
      | [] => some (Game.turn i l r)
      | false :: rest => atPath l rest
      | true :: rest => atPath r rest

/-- The empty path stays put, at either shape of position. -/
theorem atPath_nil {n : ℕ} (g : Game n) : atPath g ([] : List Bool) = some g := by
  cases g <;> rfl

/-- Taking the left child first, then the rest of the path. -/
theorem atPath_cons_left {n : ℕ} (i : Player n) (l r : Game n) (rest : List Bool) :
    atPath (Game.turn i l r) (false :: rest) = atPath l rest := rfl

/-- Taking the right child first, then the rest of the path. -/
theorem atPath_cons_right {n : ℕ} (i : Player n) (l r : Game n) (rest : List Bool) :
    atPath (Game.turn i l r) (true :: rest) = atPath r rest := rfl

/-- A non-empty path does not stay at a terminal position. -/
theorem atPath_cons_terminal {n : ℕ} (b : Bool) (rest : List Bool) (u : Profile n) :
    atPath (Game.terminal u) (b :: rest) = none := rfl

/-- The branch the `outcome` recursion prefers at the node of `g` whose path is `h`: `true` for
the right child when `(outcome l) i <= (outcome r) i`, matching `choose`'s tie rule. The player
argument is ignored, because the preference is a property of the node and its owner, not of who
asks; only the owner is ever asked. Off-tree paths answer `false`. -/
def brute {n : ℕ} (g : Game n) : Strats n :=
  fun _ h => match atPath g h with
    | Option.some (Game.turn i l r) =>
        if (outcome l) i ≤ (outcome r) i then true else false
    | _ => false

/-- At a node the recursion answers with the very comparison `choose` uses. -/
theorem brute_at_root {n : ℕ} (i : Player n) (l r : Game n) (j : Player n) :
    brute (Game.turn i l r) j ([] : List Bool) =
      (if (outcome l) i ≤ (outcome r) i then true else false) := rfl

/-- One step into the left child: the answer for a path is the child's own answer for the rest.
This is the identity that lets the induction be stated subtree-relatively. -/
theorem brute_cons_left {n : ℕ} (k : Player n) (l r : Game n) (j : Player n) (ys : List Bool) :
    brute (Game.turn k l r) j (false :: ys) = brute l j ys := rfl

/-- One step into the right child. -/
theorem brute_cons_right {n : ℕ} (k : Player n) (l r : Game n) (j : Player n) (ys : List Bool) :
    brute (Game.turn k l r) j (true :: ys) = brute r j ys := rfl

/-- A single deviation: `i`'s answer at history `hpath` is replaced by `b`, and every other
answer -- `i`'s at every other history, and every other player's everywhere -- stays `brute`. -/
def deviate {n : ℕ} (g : Game n) (i : Player n) (hpath : List Bool) (b : Bool) : Strats n :=
  fun j h => if (j = i ∧ h = hpath) then b else brute g j h

/-- Away from `i` a deviation changes nothing, which is the whole content of "one player flips
at one node". -/
theorem deviate_agree_off {n : ℕ} (i : Player n) (g : Game n) (hpath : List Bool) (b : Bool) :
    ∀ (j : Player n) (p : List Bool), j ≠ i → deviate g i hpath b j p = brute g j p := by
  intro j p hj
  have hnb : ¬(j = i ∧ p = hpath) := fun hh => hj hh.1
  show (if (j = i ∧ p = hpath) then b else brute g j p) = brute g j p
  rw [if_neg hnb]

/-! ## The recursion's own two selection facts, at every component -/

/-- When the acting player's left continuation pays no more than the right one, the recursion
returns the right continuation's whole profile -- not merely a better component for the actor. -/
theorem outcome_eq_of_le {n : ℕ} (k : Player n) (l r : Game n)
    (h : (outcome l) k ≤ (outcome r) k) : outcome (Game.turn k l r) = outcome r := by
  show (if (outcome l) k ≤ (outcome r) k then outcome r else outcome l) = outcome r
  exact if_pos h

/-- The tie-breaking other way: a left continuation that pays strictly more is kept whole. -/
theorem outcome_eq_of_not_le {n : ℕ} (k : Player n) (l r : Game n)
    (h : ¬((outcome l) k ≤ (outcome r) k)) : outcome (Game.turn k l r) = outcome l := by
  show (if (outcome l) k ≤ (outcome r) k then outcome r else outcome l) = outcome l
  exact if_neg h

/-! ## The computed profile reproduces the recursion -/

/-- Any profile that answers every node of `g` the way the recursion prefers, under the labelling
`h` appended, plays `g` to exactly `outcome g`. The prefix `h` is what makes this inductive: one
step down, the labels grow by `h ++ [choice]` while `brute` reads the subtree-relative remainder. -/
theorem go_exact {n : ℕ} :
    ∀ (g : Game n) (h : List Bool) (s : Strats n),
      (∀ (j : Player n) (ys : List Bool), s j (h ++ ys) = brute g j ys) →
        go g h s = outcome g := by
  intro g
  induction g with
  | terminal u =>
      intro h s _
      exact go_terminal u h s
  | turn k l r ihl ihr =>
      intro h s hs
      by_cases hle : (outcome l) k ≤ (outcome r) k
      · have htrue : s k h = true := by
          rw [← List.append_nil h, hs k ([] : List Bool), brute_at_root, if_pos hle]
        have hs_r : ∀ (j : Player n) (ys : List Bool),
            s j ((h ++ [true]) ++ ys) = brute r j ys := by
          intro j ys
          rw [List.append_assoc, List.singleton_append, hs j (true :: ys), brute_cons_right]
        rw [go_turn_apply, if_pos htrue, outcome_eq_of_le k l r hle]
        exact ihr (h ++ [true]) s hs_r
      · have hne : ¬(s k h = true) := by
          intro hh
          rw [← List.append_nil h, hs k ([] : List Bool), brute_at_root, if_neg hle] at hh
          exact Bool.false_ne_true hh
        have hs_l : ∀ (j : Player n) (ys : List Bool),
            s j ((h ++ [false]) ++ ys) = brute l j ys := by
          intro j ys
          rw [List.append_assoc, List.singleton_append, hs j (false :: ys), brute_cons_left]
        rw [go_turn_apply, if_neg hne, outcome_eq_of_not_le k l r hle]
        exact ihl (h ++ [false]) s hs_l

/-- Playing the tree with the profile the recursion computes gives back the recursion's answer.
This is the hinge: it turns `outcome` from a bare number-cruncher into the payoff of an explicit
strategy profile, which is what a deviation theorem has to be about. -/
theorem play_brute {n : ℕ} (g : Game n) : play g (brute g) = outcome g :=
  go_exact g ([] : List Bool) (brute g) fun _ _ => rfl

/-! ## One-shot deviation -/

/-- The bound that carries the module: fix a player `i`. Any profile whose answers at the
histories reached *by other players* agree with `brute` cannot give `i` more than `outcome g`
does, at any node and under any history prefix. At a node `i` owns, the branch is `i`'s own
choice and the carrier's `turn_ge_left`/`turn_ge_right` bound it by the maximum the recursion
takes. At a node owned by someone else the agreed answer selects the very continuation whose
`outcome` profile is being compared. -/
theorem go_bound {n : ℕ} (i : Player n) :
    ∀ (g : Game n) (h : List Bool) (s : Strats n),
      (∀ (j : Player n) (ys : List Bool), j ≠ i → s j (h ++ ys) = brute g j ys) →
        (go g h s) i ≤ (outcome g) i := by
  intro g
  induction g with
  | terminal u =>
      intro h s _
      exact Nat.le_refl _
  | turn k l r ihl ihr =>
      intro h s hs
      by_cases hk : k = i
      · rw [go_turn_apply]
        by_cases hsb : s k h = true
        · have hs_r : ∀ (j : Player n) (ys : List Bool), j ≠ i →
              s j ((h ++ [true]) ++ ys) = brute r j ys := by
            intro j ys hj
            rw [List.append_assoc, List.singleton_append, hs j (true :: ys) hj,
              brute_cons_right]
          rw [if_pos hsb, hk]
          exact Nat.le_trans (ihr (h ++ [true]) s hs_r) (turn_ge_right i l r)
        · have hs_l : ∀ (j : Player n) (ys : List Bool), j ≠ i →
              s j ((h ++ [false]) ++ ys) = brute l j ys := by
            intro j ys hj
            rw [List.append_assoc, List.singleton_append, hs j (false :: ys) hj,
              brute_cons_left]
          rw [if_neg hsb, hk]
          exact Nat.le_trans (ihl (h ++ [false]) s hs_l) (turn_ge_left i l r)
      · have hnode : s k h = brute (Game.turn k l r) k ([] : List Bool) := by
          rw [← List.append_nil h, hs k ([] : List Bool) hk]
        by_cases hle : (outcome l) k ≤ (outcome r) k
        · have htrue : s k h = true := by rw [hnode, brute_at_root, if_pos hle]
          have hs_r : ∀ (j : Player n) (ys : List Bool), j ≠ i →
              s j ((h ++ [true]) ++ ys) = brute r j ys := by
            intro j ys hj
            rw [List.append_assoc, List.singleton_append, hs j (true :: ys) hj,
              brute_cons_right]
          rw [go_turn_apply, if_pos htrue, outcome_eq_of_le k l r hle]
          exact ihr (h ++ [true]) s hs_r
        · have hne : ¬(s k h = true) := by
            intro hh
            rw [hnode, brute_at_root, if_neg hle] at hh
            exact Bool.false_ne_true hh
          have hs_l : ∀ (j : Player n) (ys : List Bool), j ≠ i →
              s j ((h ++ [false]) ++ ys) = brute l j ys := by
            intro j ys hj
            rw [List.append_assoc, List.singleton_append, hs j (false :: ys) hj,
              brute_cons_left]
          rw [go_turn_apply, if_neg hne, outcome_eq_of_not_le k l r hle]
          exact ihl (h ++ [false]) s hs_l

/-- **One-shot deviation, for the computed profile.** Flip `i`'s answer at one history of one
game and leave every other answer as `brute` left it: `i`'s payoff cannot exceed what the
recursion already gives `i`. Both branches are covered because `b` is universally quantified, so
in particular the flipped one is. -/
theorem one_shot_deviation {n : ℕ} (i : Player n) (g : Game n) (hpath : List Bool) (b : Bool) :
    (go g ([] : List Bool) (deviate g i hpath b)) i ≤ (outcome g) i :=
  go_bound i g ([] : List Bool) (deviate g i hpath b)
    (fun j p hj => deviate_agree_off i g hpath b j p hj)

/-- The same bound with the safe side written as a play: following `brute` is at least as good
for `i` as following `brute` except for one flip at one node. -/
theorem one_shot_deviation_le_brute {n : ℕ} (i : Player n) (g : Game n) (hpath : List Bool)
    (b : Bool) : (play g (deviate g i hpath b)) i ≤ (play g (brute g)) i := by
  rw [play_brute g]
  exact one_shot_deviation i g hpath b

/-! ## A worked three-player tree of depth two -/

/-- The three acting players, written as explicit `Fin` values so the computations below reduce
by projection rather than through a numeral coercion. -/
def p0 : Player 3 := ⟨0, by decide⟩

/-- The middle actor, owner of the left continuation of the root. -/
def p1 : Player 3 := ⟨1, by decide⟩

/-- The last actor, owner of the right continuation of the root. -/
def p2 : Player 3 := ⟨2, by decide⟩

/-- Four leaves, with payoffs that depend on the slot, so the three players rank the
continuations differently and their preferences genuinely conflict. -/
def leafA : Profile 3 := fun j => j.val + 1

/-- The left continuation of player 1's node: it beats `leafA` for slots 0 and 1, so player 1
takes it and player 0 is paid 4 by it rather than 1. -/
def leafB : Profile 3 := fun j => 4 - j.val

/-- The left continuation of player 2's node: generous at slot 2 and thin at slot 0, which is
why player 2 keeps it and why player 0 loses by reaching it. -/
def leafC : Profile 3 := fun j => 3 * j.val + 1

/-- The right continuation of player 2's node: decreasing in the slot index, so it conflicts with
`leafC` for player 2 (6 against 7) and pays player 0 more than `leafC` does. -/
def leafD : Profile 3 := fun j => 10 - 2 * j.val

/-- Depth two, three actors: player 0 at the root, player 1 on the left continuation, player 2
on the right one. -/
def tree : Game 3 :=
  Game.turn p0
    (Game.turn p1 (Game.terminal leafA) (Game.terminal leafB))
    (Game.turn p2 (Game.terminal leafC) (Game.terminal leafD))

/-- The root answer is the left child: player 0 gets 4 from the left subtree's outcome and only
1 from the right, so `brute` says `false`. -/
theorem tree_brute_root_is_left : brute tree p0 ([] : List Bool) = false := by decide

/-- Computed, not claimed: the actor's payoff under the recursion-driven profile is 4. -/
theorem tree_play_brute_actor : (play tree (brute tree)) p0 = 4 := by decide

/-- The second player's component of the same play. -/
theorem tree_play_brute_second : (play tree (brute tree)) p1 = 3 := by decide

/-- The third player's component. -/
theorem tree_play_brute_third : (play tree (brute tree)) p2 = 2 := by decide

/-- Player 0 flips her own single decision at the root and drops to 1: the deviation is real,
the history bookkeeping reaches the node, and the other two players keep playing `brute`. -/
theorem tree_play_deviation_actor :
    (play tree (deviate tree p0 ([] : List Bool) true)) p0 = 1 := by decide

/-- The bound is not vacuous on this tree: the one flip costs the actor three of her four. -/
theorem tree_deviation_strictly_worse :
    (play tree (deviate tree p0 ([] : List Bool) true)) p0 < (play tree (brute tree)) p0 := by
  rw [tree_play_deviation_actor, tree_play_brute_actor]
  norm_num

end JurisLean.Mandate.OneShotDeviation
