"""
ASPIC+ Argumentation Framework for Legal Reasoning.

Mathematical foundation (Dung 1995, Caminada & Amgoud 2007, Modgil & Prakken 2013):

An ASPIC+ argumentation framework is a tuple (K, n, <=) where:
  - K is a knowledge base partitioned into:
      Kn  : necessary knowledge (strict, unattackable facts)
      Kp  : defeasible knowledge (preferences that can be attacked)
  - n   : naming function mapping each defeasible rule to its attackable label
  - <=  : a preference ordering on defeasible rules

An argument A is a tree built from:
  1. A premise p in Kn                       (fact-argument)
  2. A defeasible rule r in Kp applied to    (rule-argument)
     sub-arguments A1,...,An with
     premises(A1) U ... U premises(An) |- body(r)
     conclusion(A) = head(r)

Three attack relations (all asymmetric):
  undercut(A, B)  : A's conclusion names a defeasible inference rule used by B
  rebutter(A, B)  : A's conclusion contradicts B's conclusion
  underminer(A, B): A's conclusion contradicts a defeasible premise of B

Defeat = attack that survives the preference check:
  defeat(A,B) = attack(A,B) and not (B is strictly preferred to A)

Justification status (grounded semantics):
  - IN   : defended against all attackers
  - OUT  : attacked by an IN argument
  - UNDEC : neither IN nor OUT
"""

from __future__ import annotations

from dataclasses import dataclass, field
from enum import Enum, auto
from typing import Optional


class KnowledgeType(Enum):
    NECESSARY = auto()   # Kn -- strict, cannot be attacked
    DEFEASIBLE = auto()  # Kp -- can be attacked


class AttackType(Enum):
    UNDERCUT = auto()
    REBUTTER = auto()
    UNDERMINER = auto()


class JustificationStatus(Enum):
    IN = auto()
    OUT = auto()
    UNDEC = auto()


@dataclass(frozen=True)
class Proposition:
    """An atomic or negated proposition in the language."""
    name: str
    negated: bool = False

    def complement(self) -> Proposition:
        return Proposition(name=self.name, negated=not self.negated)

    def __str__(self) -> str:
        return f"~{self.name}" if self.negated else self.name


@dataclass(frozen=True)
class KnowledgeItem:
    """A single knowledge base element."""
    proposition: Proposition
    knowledge_type: KnowledgeType
    label: str  # human-readable identifier

    def __str__(self) -> str:
        tag = "Kn" if self.knowledge_type == KnowledgeType.NECESSARY else "Kp"
        return f"[{tag}] {self.label}: {self.proposition}"


@dataclass(frozen=True)
class DefeasibleRule:
    """A defeasible inference rule: body1 & ... & bodyN => head."""
    name: str
    body: tuple[Proposition, ...]
    head: Proposition
    authority: float = 0.5  # preference weight in [0, 1]

    def __str__(self) -> str:
        bodies = " & ".join(str(b) for b in self.body)
        return f"{self.name}: {bodies} => {self.head} (auth={self.authority})"


@dataclass
class Argument:
    """
    A tree-structured argument.

    An argument is built inductively:
      - Leaf:  a proposition from Kn or Kp
      - Node:  a defeasible rule applied to sub-arguments whose
               combined conclusions entail the rule body
    """
    id: int
    conclusion: Proposition
    premises: frozenset[Proposition]
    defeasible_rules_used: frozenset[DefeasibleRule]
    defeasible_premises: frozenset[Proposition]
    sub_arguments: tuple[Argument, ...] = ()
    is_leaf: bool = True

    def __str__(self) -> str:
        rules_str = ", ".join(r.name for r in self.defeasible_rules_used)
        return (
            f"Arg#{self.id}[{self.conclusion}] "
            f"premises={{{', '.join(str(p) for p in self.premises)}}} "
            f"rules={{{rules_str}}}"
        )


@dataclass
class Attack:
    """An attack relation between two arguments."""
    attacker: Argument
    attacked: Argument
    attack_type: AttackType

    def __str__(self) -> str:
        return (
            f"({self.attack_type.name}) "
            f"Arg#{self.attacker.id} -> Arg#{self.attacked.id}"
        )


@dataclass
class ASPICFramework:
    """
    Full ASPIC+ argumentation framework.

    Attributes
    ----------
    necessary_knowledge : propositions that cannot be attacked (Kn)
    defeasible_knowledge : propositions that can be attacked (Kp)
    rules : defeasible inference rules
    preferences : ordering on rules (dict: rule_name -> float, higher = preferred)
    """
    necessary_knowledge: list[KnowledgeItem] = field(default_factory=list)
    defeasible_knowledge: list[KnowledgeItem] = field(default_factory=list)
    rules: list[DefeasibleRule] = field(default_factory=list)
    arguments: list[Argument] = field(default_factory=list)
    attacks: list[Attack] = field(default_factory=list)
    _next_id: int = 0

    def _allocate_id(self) -> int:
        aid = self._next_id
        self._next_id += 1
        return aid

    # ------------------------------------------------------------------ #
    #  Argument construction                                              #
    # ------------------------------------------------------------------ #

    def build_leaf_argument(self, item: KnowledgeItem) -> Argument:
        """Build a leaf argument from a single knowledge item."""
        def_premises: frozenset[Proposition] = (
            frozenset({item.proposition})
            if item.knowledge_type == KnowledgeType.DEFEASIBLE
            else frozenset()
        )
        arg = Argument(
            id=self._allocate_id(),
            conclusion=item.proposition,
            premises=frozenset({item.proposition}),
            defeasible_rules_used=frozenset(),
            defeasible_premises=def_premises,
            sub_arguments=(),
            is_leaf=True,
        )
        self.arguments.append(arg)
        return arg

    def build_rule_argument(
        self,
        rule: DefeasibleRule,
        sub_args: list[Argument],
    ) -> Argument:
        """Build an argument by applying a defeasible rule to sub-arguments."""
        all_premises: frozenset[Proposition] = frozenset()
        all_def_rules: frozenset[DefeasibleRule] = frozenset({rule})
        all_def_premises: frozenset[Proposition] = frozenset()
        for sa in sub_args:
            all_premises = all_premises | sa.premises
            all_def_rules = all_def_rules | sa.defeasible_rules_used
            all_def_premises = all_def_premises | sa.defeasible_premises

        arg = Argument(
            id=self._allocate_id(),
            conclusion=rule.head,
            premises=all_premises,
            defeasible_rules_used=all_def_rules,
            defeasible_premises=all_def_premises,
            sub_arguments=tuple(sub_args),
            is_leaf=False,
        )
        self.arguments.append(arg)
        return arg

    # ------------------------------------------------------------------ #
    #  Attack & defeat detection                                          #
    # ------------------------------------------------------------------ #

    def _find_undercut(self, a: Argument, b: Argument) -> bool:
        """A undercuts B iff A's conclusion names a rule used by B."""
        for rule in b.defeasible_rules_used:
            if a.conclusion == Proposition(name=rule.name):
                return True
        return False

    def _find_rebut(self, a: Argument, b: Argument) -> bool:
        """A rebuts B iff A's conclusion negates B's conclusion."""
        return a.conclusion == b.conclusion.complement()

    def _find_undermine(self, a: Argument, b: Argument) -> bool:
        """A undermines B iff A's conclusion negates a defeasible premise of B."""
        for prem in b.defeasible_premises:
            if a.conclusion == prem.complement():
                return True
        return False

    def _pref_check(self, attacker: Argument, attacked: Argument) -> bool:
        """
        Preference-based defeat check.
        defeat(A, B) iff attack(A, B) and
        NOT (all rules in B strictly preferred to all rules in A).
        Simplified: if B has strictly stronger authority, attack is blocked.
        """
        if not attacker.defeasible_rules_used:
            return True  # strict or premise attack always defeats
        if not attacked.defeasible_rules_used:
            return True
        max_a = max(r.authority for r in attacker.defeasible_rules_used)
        max_b = max(r.authority for r in attacked.defeasible_rules_used)
        return max_a >= max_b  # attacker is at least as strong

    def compute_attacks(self) -> None:
        """Compute all attack relations between constructed arguments."""
        self.attacks.clear()
        for a in self.arguments:
            for b in self.arguments:
                if a.id == b.id:
                    continue
                atype: Optional[AttackType] = None
                if self._find_undercut(a, b):
                    atype = AttackType.UNDERCUT
                elif self._find_rebut(a, b):
                    atype = AttackType.REBUTTER
                elif self._find_undermine(a, b):
                    atype = AttackType.UNDERMINER

                if atype is not None and self._pref_check(a, b):
                    self.attacks.append(Attack(a, b, atype))

    # ------------------------------------------------------------------ #
    #  Grounded semantics (labeling)                                      #
    # ------------------------------------------------------------------ #

    def compute_grounded_labeling(self) -> dict[int, JustificationStatus]:
        """
        Compute grounded labeling via iterative fixed-point (Dung 1995).

        Algorithm:
          1. IN(args) = args with no attackers  (initially)
          2. OUT(args) = args attacked by IN args
          3. IN(args) += args defended by IN args (all attackers are OUT)
          4. repeat until fixpoint
        """
        label: dict[int, JustificationStatus] = {
            a.id: JustificationStatus.UNDEC for a in self.arguments
        }
        attackers_of: dict[int, list[int]] = {a.id: [] for a in self.arguments}
        for att in self.attacks:
            attackers_of[att.attacked.id].append(att.attacker.id)

        changed = True
        while changed:
            changed = False
            for arg in self.arguments:
                aid = arg.id
                if label[aid] != JustificationStatus.UNDEC:
                    continue
                atks = attackers_of[aid]
                if not atks:
                    if label[aid] != JustificationStatus.IN:
                        label[aid] = JustificationStatus.IN
                        changed = True
                    continue
                all_attackers_out = all(
                    label[a] == JustificationStatus.OUT for a in atks
                )
                any_attacker_in = any(
                    label[a] == JustificationStatus.IN for a in atks
                )
                if all_attackers_out:
                    # All attackers are OUT → this argument is defended → IN
                    if label[aid] != JustificationStatus.IN:
                        label[aid] = JustificationStatus.IN
                        changed = True
                elif any_attacker_in:
                    # At least one attacker is IN and not all are OUT → defeated → OUT
                    if label[aid] != JustificationStatus.OUT:
                        label[aid] = JustificationStatus.OUT
                        changed = True
                elif not all_attackers_out and all(
                    label[a] != JustificationStatus.UNDEC for a in atks
                ):
                    if label[aid] != JustificationStatus.OUT:
                        label[aid] = JustificationStatus.OUT
                        changed = True
                # otherwise stays UNDEC
        return label


# ------------------------------------------------------------------ #
#  Demo: Legal case -- medical malpractice                            #
# ------------------------------------------------------------------ #

def demo() -> None:
    print("=" * 64)
    print("ASPIC+ Framework Demo -- Medical Malpractice")
    print("=" * 64)

    fw = ASPICFramework()

    # --- Knowledge base ---
    # Kn: necessary (strict) facts
    kn_items = [
        KnowledgeItem(
            Proposition("patient_was_treated"), KnowledgeType.NECESSARY,
            "medical_record",
        ),
        KnowledgeItem(
            Proposition("signed_consent"), KnowledgeType.NECESSARY,
            "consent_form",
        ),
    ]

    # Kp: defeasible evidence
    kp_items = [
        KnowledgeItem(
            Proposition("standard_of_care_violated"), KnowledgeType.DEFEASIBLE,
            "expert_witness_A",
        ),
        KnowledgeItem(
            Proposition("standard_of_care_violated", negated=True),
            KnowledgeType.DEFEASIBLE,
            "defense_expert_B",
        ),
        KnowledgeItem(
            Proposition("patient_harmed"), KnowledgeType.DEFEASIBLE,
            "medical_assessment",
        ),
        KnowledgeItem(
            Proposition("negligence", negated=True), KnowledgeType.DEFEASIBLE,
            "informed_consent_defense",
        ),
    ]

    for item in kn_items + kp_items:
        if item.knowledge_type == KnowledgeType.NECESSARY:
            fw.necessary_knowledge.append(item)
        else:
            fw.defeasible_knowledge.append(item)

    # --- Defeasible rules ---
    neg_prop = Proposition("standard_of_care_violated", negated=True)
    neg_neg = Proposition("negligence", negated=True)
    rules = [
        DefeasibleRule(
            name="r1",
            body=(Proposition("standard_of_care_violated"),
                  Proposition("patient_harmed")),
            head=Proposition("negligence"),
            authority=0.8,
        ),
        DefeasibleRule(
            name="r2",
            body=(neg_prop,),
            head=neg_neg,
            authority=0.6,
        ),
        DefeasibleRule(
            name="r3",
            body=(neg_neg,),
            head=Proposition("no_liability"),
            authority=0.6,
        ),
    ]
    fw.rules = rules

    # --- Build leaf arguments ---
    print("\n--- Leaf Arguments ---")
    leaf_args: dict[str, Argument] = {}
    for item in kn_items + kp_items:
        arg = fw.build_leaf_argument(item)
        leaf_args[str(item.proposition)] = arg
        print(f"  {arg}")

    # --- Build rule arguments ---
    print("\n--- Rule Arguments ---")

    # Arg#6: negligence (r1 applied to violated & harmed)
    arg_negligence = fw.build_rule_argument(
        rules[0],
        [leaf_args["standard_of_care_violated"], leaf_args["patient_harmed"]],
    )
    print(f"  {arg_negligence}")

    # Arg#7: ~negligence from r2 (defense expert)
    arg_no_neg_r2 = fw.build_rule_argument(
        rules[1],
        [leaf_args["~standard_of_care_violated"]],
    )
    print(f"  {arg_no_neg_r2}")

    # Arg#8: ~negligence from r3 via r2 (informed consent defense)
    arg_no_neg_defense = fw.build_rule_argument(
        rules[2],
        [arg_no_neg_r2],
    )
    print(f"  {arg_no_neg_defense}")

    # --- Compute attacks ---
    fw.compute_attacks()
    print("\n--- Attacks (Defeats) ---")
    for att in fw.attacks:
        print(f"  {att}")

    # --- Grounded labeling ---
    labeling = fw.compute_grounded_labeling()
    print("\n--- Grounded Justification Status ---")
    for arg in fw.arguments:
        status = labeling[arg.id]
        marker = {"IN": "** JUSTIFIED **", "OUT": "DEFEATED", "UNDEC": "UNDECIDED"}
        print(f"  {arg}  =>  {status.name}  {marker[status.name]}")

    print()


if __name__ == "__main__":
    demo()
