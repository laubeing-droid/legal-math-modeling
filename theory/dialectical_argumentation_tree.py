"""
Dialectical Argumentation Tree (DAT) for Legal Proceedings.

Mathematical definition
-----------------------
A Dialectical Argumentation Tree is a directed acyclic graph T = (N, E, root)
where:
  - N is a set of argument nodes, each labeled with an argument and a role
    (PROONENT or OPPONENT)
  - E is a set of attack edges  (parent --attacker--> child)
  - root is the initial argument asserted by the proponent

Turn structure (bounded to R_max rounds):
  Round 0 (P):  P asserts initial argument A_0
  Round 1 (D):  D attacks A_0 with arguments B_1,...,B_k
  Round 2 (P):  P counter-attacks each B_i with arguments C_i1,...,C_im
  ...
  Round R_max:  last speaker to play wins any branch still unattacked

Winner determination (last-speaker rule):
  For each branch (root-to-leaf path):
    - If the leaf is unattacked, the side that played the leaf wins
    - If the depth is even (0-indexed), proponent wins the branch
    - If the depth is odd, opponent wins the branch

Overall winner: majority of branches won.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from enum import Enum, auto
from typing import Optional


class Role(Enum):
    PROPONENT = auto()   # Plaintiff / Prosecutor
    OPPONENT = auto()    # Defendant / Defense


class NodeStatus(Enum):
    UNDECIDED = auto()
    WINS = auto()
    LOSES = auto()


@dataclass
class DiaArgument:
    """A single argument node in the dialectical tree."""
    id: int
    text: str
    role: Role
    round_num: int
    children: list[DiaArgument] = field(default_factory=list)
    status: NodeStatus = NodeStatus.UNDECIDED
    attack_label: str = ""  # e.g. "undercut", "rebut"

    def __str__(self) -> str:
        role_tag = "P" if self.role == Role.PROPONENT else "D"
        return f"[R{self.round_num}|{role_tag}] #{self.id}: {self.text}"


@dataclass
class DialecticalTree:
    """
    Full dialectical argumentation tree.

    Attributes
    ----------
    root : initial proponent argument
    max_rounds : maximum number of attack rounds (default 3)
    """
    root: DiaArgument
    max_rounds: int = 3
    all_nodes: list[DiaArgument] = field(default_factory=list)

    # ------------------------------------------------------------------ #
    #  Construction helpers                                                #
    # ------------------------------------------------------------------ #

    _next_id: int = field(default=0, repr=False)

    def _alloc_id(self) -> int:
        nid = self._next_id
        self._next_id += 1
        return nid

    def create_argument(
        self,
        text: str,
        role: Role,
        round_num: int,
        attack_label: str = "",
    ) -> DiaArgument:
        arg = DiaArgument(
            id=self._alloc_id(),
            text=text,
            role=role,
            round_num=round_num,
            attack_label=attack_label,
        )
        self.all_nodes.append(arg)
        return arg

    def add_attack(
        self,
        parent: DiaArgument,
        attack_arg: DiaArgument,
    ) -> DiaArgument:
        """Add an attacking argument as a child of `parent`."""
        parent.children.append(attack_arg)
        return attack_arg

    # ------------------------------------------------------------------ #
    #  Winner determination                                                #
    # ------------------------------------------------------------------ #

    def compute_statuses(self) -> None:
        """
        Bottom-up status computation.

        A leaf node WINS (for its side) if:
          - it is at round < max_rounds and was never attacked, OR
          - it is at round >= max_rounds (forced stop)

        An internal node:
          - LOSES if any child WINS (attacker succeeds)
          - WINS if all children LOSE (defender succeeds)
          - If children are mixed: WINS iff all children LOSE
        """
        self._recurse_status(self.root)

    def _recurse_status(self, node: DiaArgument) -> None:
        for child in node.children:
            self._recurse_status(child)

        # If node has no children, it is a leaf
        if not node.children:
            node.status = NodeStatus.WINS
            return

        # Evaluate children: an internal node loses if any child (attacker) wins
        any_child_wins = any(c.status == NodeStatus.WINS for c in node.children)
        if any_child_wins:
            node.status = NodeStatus.LOSES
        else:
            node.status = NodeStatus.WINS

    def determine_winner(self) -> tuple[Role, dict[str, int]]:
        """
        Determine overall winner by counting branch winners.

        Returns (winning_role, stats_dict).
        """
        self.compute_statuses()
        stats = {Role.PROPONENT.name: 0, Role.OPPONENT.name: 0}
        self._count_branches(self.root, stats)
        if stats[Role.PROPONENT.name] >= stats[Role.OPPONENT.name]:
            return Role.PROPONENT, stats
        return Role.OPPONENT, stats

    def _count_branches(self, node: DiaArgument,
                        stats: dict[str, int]) -> None:
        if not node.children:
            if node.status == NodeStatus.WINS:
                stats[node.role.name] += 1
            return
        for child in node.children:
            self._count_branches(child, stats)

    # ------------------------------------------------------------------ #
    #  Pretty printing                                                     #
    # ------------------------------------------------------------------ #

    def print_tree(self, node: Optional[DiaArgument] = None,
                   indent: int = 0) -> None:
        if node is None:
            node = self.root
        prefix = "    " * indent
        role_tag = "P" if node.role == Role.PROPONENT else "D"
        atk = f" [{node.attack_label}]" if node.attack_label else ""
        status_sym = {
            NodeStatus.WINS: "+WINS",
            NodeStatus.LOSES: "-LOSES",
            NodeStatus.UNDECIDED: "?UNDEC",
        }
        print(
            f"{prefix}{atk} [{role_tag} R{node.round_num}] "
            f"#{node.id} {node.text}  ({status_sym[node.status]})"
        )
        for child in node.children:
            self.print_tree(child, indent + 1)


# ------------------------------------------------------------------ #
#  Demo: Contract breach dispute                                       #
# ------------------------------------------------------------------ #

def demo() -> None:
    print("=" * 64)
    print("Dialectical Argumentation Tree Demo")
    print("Scenario: Contract Breach -- Non-delivery of goods")
    print("=" * 64)

    # Round 0: Proponent (Plaintiff) asserts breach
    root_text = (
        "Defendant failed to deliver goods by contract deadline (Jan 15). "
        "This constitutes material breach under Art. 25 CISG."
    )
    # We need a temporary root to construct the tree, then re-assign.
    temp_root = DiaArgument(id=0, text="", role=Role.PROPONENT, round_num=0)
    tree = DialecticalTree(root=temp_root, max_rounds=3)
    tree.all_nodes.append(temp_root)

    # Properly create root
    root = tree.create_argument(root_text, Role.PROPONENT, round_num=0)
    tree.root = root

    # Round 1: Opponent (Defendant) attacks
    d1 = tree.add_attack(
        root,
        tree.create_argument(
            "Force majeure: Factory fire on Jan 10 prevented shipment. "
            "CISG Art. 79 exempts liability for impediments beyond control.",
            Role.OPPONENT, round_num=1, attack_label="rebut",
        ),
    )
    d2 = tree.add_attack(
        root,
        tree.create_argument(
            "Plaintiff waived the deadline by accepting partial delivery "
            "on Jan 20 without objection (estoppel).",
            Role.OPPONENT, round_num=1, attack_label="undercut",
        ),
    )

    # Round 2: Proponent counter-attacks
    p1 = tree.add_attack(
        d1,
        tree.create_argument(
            "Factory fire was foreseeable -- same factory had 2 fires in 2023. "
            "Defendant failed to mitigate by sourcing from backup supplier.",
            Role.PROPONENT, round_num=2, attack_label="undercut",
        ),
    )
    p2 = tree.add_attack(
        d2,
        tree.create_argument(
            "Acceptance of partial delivery does not waive deadline. "
            "Art. 49 CISG: buyer retains right to declare avoidance "
            "unless goods conform within additional reasonable period.",
            Role.PROPONENT, round_num=2, attack_label="rebut",
        ),
    )

    # Round 3 (final): Opponent counter-attacks one branch
    tree.add_attack(
        p1,
        tree.create_argument(
            "Backup supplier quoted 3x price. Cost prohibitive "
            "under commercial reasonableness standard (UCC 2-615).",
            Role.OPPONENT, round_num=3, attack_label="undercut",
        ),
    )

    # p2 branch: no further attack (D chooses not to attack)
    # => p2 wins for P

    # Determine winner
    winner, stats = tree.determine_winner()

    print("\n--- Argumentation Tree ---")
    tree.print_tree()

    print("\n--- Branch Statistics ---")
    print(f"  Proponent branches won : {stats[Role.PROPONENT.name]}")
    print(f"  Opponent branches won  : {stats[Role.OPPONENT.name]}")
    print(f"\n  Overall winner: {winner.name}")

    print()


if __name__ == "__main__":
    demo()
