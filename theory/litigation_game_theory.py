#!/usr/bin/env python3
"""
Litigation Game Theory (方向 1)

Models litigation as an extensive-form game with imperfect information,
bridging Dung AAF to game-theoretic strategic reasoning.

Players: Plaintiff (P), Defendant (D), Judge/Court (C)
Strategies: Each player chooses arguments to present/attack/support
Information sets: Players don't know opponent's full evidence set
Equilibrium: Grounded extension as legal Nash equilibrium analog

This module formalizes the insight from the 2026-06-01 design session:
"Kripke models the court. But it doesn't model the strategic space
where two lawyers each advocate for their side."
"""
from __future__ import annotations
from dataclasses import dataclass, field
from enum import Enum
from typing import Dict, FrozenSet, List, Optional, Set, Tuple
from itertools import product


class Player(Enum):
    PLAINTIFF = "P"
    DEFENDANT = "D"
    COURT = "C"


class ArgumentType(Enum):
    CLAIM = "claim"              # Positive assertion
    REBUTTAL = "rebuttal"        # Attacks opponent's claim
    DEFENSE = "defense"          # Defends own claim against attack
    COUNTER_REBUTTAL = "counter_rebuttal"  # Attacks the attack


@dataclass(frozen=True)
class Argument:
    id: str
    player: Player
    arg_type: ArgumentType
    claim: str
    premises: FrozenSet[str]
    strength: float = 1.0  # [0, 1] — evidentiary strength


@dataclass(frozen=True)
class Strategy:
    """A strategy is a set of arguments a player chooses to present."""
    player: Player
    arguments: FrozenSet[str]  # argument IDs


@dataclass
class LitigationGame:
    """
    Extensive-form game modeling litigation as strategic argumentation.

    The game has three players (P, D, C) who each choose subsets of
    available arguments. The Dung AF induced by the combined argument
    set determines which arguments survive (grounded extension).
    A player's payoff depends on which of their arguments survive.
    """
    arguments: Dict[str, Argument]
    attacks: FrozenSet[Tuple[str, str]]  # (attacker_id, defender_id)
    payoff_rules: Dict[str, Dict[str, float]]  # claim_id → {player_value: payoff}

    def player_arguments(self, player: Player) -> List[str]:
        """All arguments available to a player."""
        return [aid for aid, a in self.arguments.items() if a.player == player]

    def compute_ge(self, presented_args: Set[str]) -> Set[str]:
        """
        Compute grounded extension for a subset of presented arguments.
        Only arguments in presented_args are considered.
        """
        args = presented_args.copy()
        attacks = {
            (a, d) for a, d in self.attacks
            if a in args and d in args
        }

        # Kleene iteration for grounded extension
        ge = set()
        changed = True
        while changed:
            changed = False
            new_ge = set()
            for a in args:
                # a is defended if every attacker is itself attacked by ge
                attackers = {att for att, def_id in attacks if def_id == a}
                if all(any((c, b) in attacks and c in ge for c in args)
                       for b in attackers):
                    if a not in ge:
                        new_ge.add(a)
                        changed = True
            ge |= new_ge
        return ge

    def compute_payoff(self, player: Player, ge: Set[str]) -> float:
        """Player's payoff = sum of player-specific payoffs for claims in GE."""
        total = 0.0
        for aid in ge:
            arg = self.arguments.get(aid)
            if arg:
                player_payoffs = self.payoff_rules.get(arg.claim, {})
                total += player_payoffs.get(player.value, 0.0)
        return total

    def find_equilibrium(self) -> Dict:
        """
        Find the legal Nash equilibrium: the strategy profile where
        no player can improve their payoff by unilaterally changing
        their argument set.

        For small games (≤3 players, ≤10 arguments each), exhaustive
        search is feasible. Returns the equilibrium strategy profile
        and payoffs.
        """
        player_args = {
            p: self.player_arguments(p) for p in Player
        }

        # Generate all possible strategies per player
        def subsets(items):
            """All subsets of items (including empty)."""
            result = [[]]
            for item in items:
                result += [s + [item] for s in result]
            return [frozenset(s) for s in result]

        strategies = {
            p: subsets(args) for p, args in player_args.items()
        }

        all_equilibria = []

        # Exhaustive search over all strategy profiles
        for sp in strategies[Player.PLAINTIFF]:
            for sd in strategies[Player.DEFENDANT]:
                # Court always presents all available arguments
                    sc = frozenset(player_args[Player.COURT])
                    presented = set(sp | sd | sc)
                    ge = self.compute_ge(presented)

                    payoffs = {
                        p: self.compute_payoff(p, ge) for p in Player
                    }

                    # Check if this is a Nash equilibrium
                    is_ne = True
                    for p in [Player.PLAINTIFF, Player.DEFENDANT]:
                        current = payoffs[p]
                        for alt in strategies[p]:
                            if alt == {p: sp if p == Player.PLAINTIFF else sd}[p]:
                                continue
                            alt_presented = set(
                                (alt if p == Player.PLAINTIFF else sp) |
                                (alt if p == Player.DEFENDANT else sd) |
                                sc
                            )
                            alt_ge = self.compute_ge(alt_presented)
                            alt_payoff = self.compute_payoff(p, alt_ge)
                            if alt_payoff > current:
                                is_ne = False
                                break
                        if not is_ne:
                            break

                    if is_ne:
                        all_equilibria.append({
                            "plaintiff_strategy": set(sp),
                            "defendant_strategy": set(sd),
                            "court_strategy": set(sc),
                            "grounded_extension": ge,
                                "payoffs": payoffs,
                            })

        return {
            "equilibria": all_equilibria,
            "total_equilibria": len(all_equilibria),
        }


def build_example_litigation_game() -> LitigationGame:
    """
    Build a concrete example: contract breach litigation.

    Plaintiff argues: contract formed, breach occurred, damages suffered
    Defendant argues: force majeure, plaintiff failed to mitigate
    Court provides: procedural framework arguments
    """
    arguments = {
        # Plaintiff arguments
        "P_contract": Argument("P_contract", Player.PLAINTIFF,
                               ArgumentType.CLAIM, "contract_formed",
                               frozenset({"offer", "acceptance", "consideration"}), 0.9),
        "P_breach": Argument("P_breach", Player.PLAINTIFF,
                              ArgumentType.CLAIM, "breach_occurred",
                              frozenset({"non_performance"}), 0.85),
        "P_damages": Argument("P_damages", Player.PLAINTIFF,
                               ArgumentType.CLAIM, "damages_suffered",
                               frozenset({"actual_loss", "foreseeability"}), 0.7),

        # Defendant arguments
        "D_force_majeure": Argument("D_force_majeure", Player.DEFENDANT,
                                     ArgumentType.REBUTTAL, "force_majeure_defense",
                                     frozenset({"unforeseeable_event", "causation"}), 0.6),
        "D_no_mitigate": Argument("D_no_mitigate", Player.DEFENDANT,
                                   ArgumentType.REBUTTAL, "failure_to_mitigate",
                                   frozenset({"mitigation_opportunity"}), 0.5),

        # Court framework arguments
        "C_burden_breach": Argument("C_burden_breach", Player.COURT,
                                     ArgumentType.CLAIM, "burden_on_plaintiff_breach",
                                     frozenset(), 1.0),
        "C_burden_fm": Argument("C_burden_fm", Player.COURT,
                                 ArgumentType.CLAIM, "burden_on_defendant_fm",
                                 frozenset(), 1.0),
    }

    attacks = frozenset({
        ("D_force_majeure", "P_breach"),       # FM attacks breach claim
        ("D_no_mitigate", "P_damages"),         # No-mitigate attacks damages
    })

    # Per-player payoffs: {claim: {player_value: payoff}}
    # Plaintiff benefits from contract/breach/damages; defendant benefits from defenses
    payoff_rules = {
        "contract_formed": {"P": 10.0, "D": -10.0, "C": 0.0},
        "breach_occurred": {"P": 20.0, "D": -20.0, "C": 0.0},
        "damages_suffered": {"P": 15.0, "D": -15.0, "C": 0.0},
        "force_majeure_defense": {"P": -20.0, "D": 20.0, "C": 0.0},
        "failure_to_mitigate": {"P": -10.0, "D": 10.0, "C": 0.0},
        "burden_on_plaintiff_breach": {"P": 0.0, "D": 0.0, "C": 0.0},
        "burden_on_defendant_fm": {"P": 0.0, "D": 0.0, "C": 0.0},
    }

    return LitigationGame(arguments, attacks, payoff_rules)


def run_example():
    """Run the example litigation game and find equilibrium."""
    print("=" * 72)
    print("LITIGATION GAME THEORY — Contract Breach Example")
    print("=" * 72)

    game = build_example_litigation_game()

    print(f"\nPlayers: Plaintiff, Defendant, Court")
    print(f"Arguments: {len(game.arguments)}")
    print(f"Attacks: {len(game.attacks)}")

    print(f"\nArgument Details:")
    for aid, arg in game.arguments.items():
        print(f"  {aid:20s} [{arg.player.value}] {arg.arg_type.value:18s} "
              f"strength={arg.strength:.1f} claim={arg.claim}")

    print(f"\nAttack Relations:")
    for att, defn in game.attacks:
        print(f"  {att} → {defn}")

    # Find equilibrium
    print(f"\nSearching for Nash equilibrium...")
    result = game.find_equilibrium()

    eq = result["equilibria"]
    if eq:
        print(f"\nEQUILIBRIA FOUND: {result['total_equilibria']}")
        for i, e in enumerate(eq, 1):
            print(f"\n  Equilibrium {i}:")
            print(f"    Plaintiff presents: {e['plaintiff_strategy']}")
            print(f"    Defendant presents: {e['defendant_strategy']}")
            print(f"    Grounded extension: {e['grounded_extension']}")
            print(f"    Payoffs: {e['payoffs']}")
    else:
        print(f"\nNo pure-strategy equilibrium found.")

    print(f"\n{'=' * 72}")
    print("LEGAL INTERPRETATION:")
    print("  The grounded extension represents the set of legal conclusions")
    print("  that survive adversarial attack — the legal analog of Nash")
    print("  equilibrium where no party can improve their position by")
    print("  unilaterally changing their argument strategy.")
    print(f"{'=' * 72}")

    return result


if __name__ == "__main__":
    run_example()
