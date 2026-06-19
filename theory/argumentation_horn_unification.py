#!/usr/bin/env python3
"""
#9: Rule Algebra + Dung Argumentation Frame --- Stratified Semantics
====================================================================

Formally bridges two independent mathematical systems in juris-calculus:

  Rule Algebra:        compose / conflict / derive
  Argumentation Frame: attack / defend / acceptable set

## Accepted 2026-06-11 Position

The original evaluator is not monotone once rebuttal/confidence-zeroing
is included. Therefore it cannot be justified by a single Tarski/Kleene
monotone fixpoint proof.

The accepted engineering design is stratified:

  Stage 1: monotone Horn closure.
  Stage 2: Dung abstract argumentation over the resulting static graph.

Dung grounded extension has an executable exhaustive proof for all
directed attack graphs with n <= 4. Equivalence with the original
production evaluator remains a separate, partial obligation.

## Model (Horn-derived Dung Frame)

Given a Horn knowledge base KB, define the induced argumentation frame
AF(KB) = (Args, Att) where:

  Args = {h | (h <- body) in KB and body is satisfiable}
  Att(a, b) iff a.conflicts(b) or b.chains_to_exception_of(a)

Then, under the encoded stratification assumptions:
  1. AF(KB) is finitary (each argument has finitely many attackers)
  2. The grounded extension GE(KB) can be used as the deterministic
     rebuttal/exception resolution layer
  3. GE(KB) is computable in polynomial time

## Verification Strategy

1. Formalize the canonical Dung argumentation framework
2. Construct the induced frame from juris-calculus Horn rules
3. Test correspondence on encoded fixtures
4. Compute stable/preferred/grounded semantics on real rule data
5. Show conflict resolution preserves admissibility
"""

from dataclasses import dataclass, field
from typing import Dict, Set, List, Tuple, FrozenSet, Optional
from collections import defaultdict
import itertools


# ============================================================
# Part A: Dung Argumentation Framework (Canonical)
# ============================================================

@dataclass(frozen=True)
class Argument:
    """An abstract argument in Dung's framework.

    In juris-calculus, each argument corresponds to a legal claim
    derived from a Horn rule application.
    """
    id: str
    rule_id: str       # Source Horn rule
    claim: str          # Legal conclusion
    premises: FrozenSet[str]  # Facts used


@dataclass
class DungFrame:
    """AF = (Args, Att) --- Dung's abstract argumentation framework.

    Att is a binary attack relation on Args.
    """
    args: Set[Argument]
    attacks: Set[Tuple[Argument, Argument]]  # (attacker, target)

    def attackers_of(self, a: Argument) -> Set[Argument]:
        return {src for (src, tgt) in self.attacks if tgt == a}

    def defends(self, s: Set[Argument], a: Argument) -> bool:
        """S defends a if S attacks all attackers of a."""
        return all(
            any((d, attacker) in self.attacks for d in s)
            for attacker in self.attackers_of(a)
        )

    def is_conflict_free(self, s: Set[Argument]) -> bool:
        """S is conflict-free if no two arguments in S attack each other."""
        for a, b in itertools.product(s, s):
            if (a, b) in self.attacks:
                return False
        return True

    def is_admissible(self, s: Set[Argument]) -> bool:
        """S is admissible if conflict-free and defends all its members."""
        return self.is_conflict_free(s) and all(
            self.defends(s, a) for a in s
        )

    def f_operator(self, s: Set[Argument]) -> Set[Argument]:
        """F(S) = {a | S defends a} --- Dung's characteristic function."""
        return {a for a in self.args if self.defends(s, a)}

    def grounded_extension(self) -> Set[Argument]:
        """Compute the grounded extension = lfp(F).

        The grounded extension is the least fixpoint of F.
        It is unique, always exists, and is computable in polynomial time
        for finitary frameworks.
        """
        current: Set[Argument] = set()
        max_iter = 1000

        for _ in range(max_iter):
            nxt = self.f_operator(current)
            if nxt == current:
                return nxt
            current = nxt
        return current

    def preferred_extensions(self) -> List[Set[Argument]]:
        """Compute all preferred extensions --- maximal admissible sets.

        For our bounded Horn KB (k <= 3, no cycles), the preferred
        extension is unique and equals the grounded extension.
        """
        admissible_sets = []
        # For small argument sets, enumerate; for large, use grounded
        if len(self.args) <= 20:
            args_list = list(self.args)
            for mask in range(1 << len(args_list)):
                s = {args_list[i] for i in range(len(args_list)) if mask & (1 << i)}
                if self.is_admissible(s):
                    admissible_sets.append(s)
            # Return maximal ones
            maximal = []
            for s in admissible_sets:
                if not any(
                    other != s and s.issubset(other)
                    for other in admissible_sets
                ):
                    maximal.append(s)
            return maximal if maximal else [self.grounded_extension()]
        return [self.grounded_extension()]

    def stable_extensions(self) -> List[Set[Argument]]:
        """Stable extensions = preferred extensions that attack all outsiders.

        For our bounded Horn KB, the grounded extension is also stable
        because the attack relation is stratified by exception chain depth.
        """
        grounded = self.grounded_extension()
        outsiders = self.args - grounded
        # Check: does grounded attack ALL outsiders?
        attacks_all = all(
            any((g, o) in self.attacks for g in grounded)
            for o in outsiders
        )
        if attacks_all or not outsiders:
            return [grounded]
        return []


# ============================================================
# Part B: Constructing AF(KB) from juris-calculus Horn Rules
# ============================================================

@dataclass
class HornRule:
    """A Horn rule from the juris-calculus knowledge base."""
    id: str
    premises: List[str]
    head: str
    exceptions: List[str]  # Rule IDs of exception rules
    concepts: List[str] = field(default_factory=list)
    head_type: str = "HORN"
    namespace: str = "general"
    depth: int = 1


class HornToDungBridge:
    """Constructs the induced Dung frame from a Horn KB."""

    def __init__(self, rules: List[HornRule], facts: Set[str]):
        self.rules = {r.id: r for r in rules}
        self.facts = facts

    def construct_deductive_frame(self, max_depth: int = 10) -> DungFrame:
        """Build AF(KB) with defeat-aware forward chaining.

        Each iteration:
        1. Builds the argumentation frame from current facts
        2. Computes grounded extension to identify accepted arguments
        3. Derives new facts from accepted rules only
        4. Repeats until no new facts appear or max_depth reached

        This prevents defeated rules from contributing facts to dependent
        rules, AND correctly handles rules whose premises are only satisfied
        after accepted rules derive new facts.

        Args:
            max_depth: Maximum deduction depth (safety valve).

        Returns:
            DungFrame built on the defeat-aware closure.
        """
        import warnings

        original_facts = self.facts
        defeat_aware_closure = set(original_facts)
        converged = False
        for _ in range(max_depth):
            # Rebuild frame from current closure and recompute accepted rules
            self.facts = defeat_aware_closure
            current_frame = self.construct_frame()
            current_accepted = current_frame.grounded_extension()
            accepted_rule_ids = {arg.rule_id for arg in current_accepted}

            # Derive facts from accepted rules
            changed = False
            for rule in self.rules.values():
                if rule.id in accepted_rule_ids and rule.head not in defeat_aware_closure:
                    if all(p in defeat_aware_closure for p in rule.premises):
                        defeat_aware_closure.add(rule.head)
                        changed = True
            if not changed:
                converged = True
                break

        if not converged:
            warnings.warn(
                f"DeductionDepthExceededWarning: defeat-aware closure did not "
                f"converge within {max_depth} iterations. Possible cyclic rules.",
                stacklevel=2,
            )

        # Build final frame from defeat-aware closure
        old_facts = self.facts
        self.facts = defeat_aware_closure
        filtered_frame = self.construct_frame()
        self.facts = old_facts
        return filtered_frame

    def construct_frame(self) -> DungFrame:
        """Build AF(KB) = (Args, Att).

        Args: Each fireable rule produces an argument for its head claim.
        Att(a, b): a attacks b if:
          - a is an exception rule of b (a defeats b), OR
          - a's head conflicts with b's head AND no exception relationship exists

        EXCEPTION EDGES TAKE PRIORITY: if R3 is an exception of R2,
        then R3 -> R2 is the only attack. R2 -> R3 is NOT added even
        if heads appear to conflict, because the exception chain
        already resolves the conflict.
        """
        args: Set[Argument] = set()
        attacks: Set[Tuple[Argument, Argument]] = set()
        exception_pairs: Set[Tuple[str, str]] = set()

        # Step 1: Build all fireable rules as arguments
        arg_by_rule: Dict[str, Argument] = {}
        for rule in self.rules.values():
            if self._premises_satisfied(rule):
                arg = Argument(
                    id=f"arg_{rule.id}",
                    rule_id=rule.id,
                    claim=rule.head,
                    premises=frozenset(rule.premises)
                )
                args.add(arg)
                arg_by_rule[rule.id] = arg

        # Step 2: Build attack relations (exception-first)
        for r_id, rule in self.rules.items():
            a = arg_by_rule.get(r_id)
            if a is None:
                continue

            # Attack 1: Exception chain --- exceptions defeat the rule they override
            for exc_id in rule.exceptions:
                exc_arg = arg_by_rule.get(exc_id)
                if exc_arg:
                    attacks.add((exc_arg, a))  # exception defeats main rule
                    exception_pairs.add((exc_id, r_id))

        # Attack 2: Cross-rule conflicts (via concept overlap)
        # SKIP if there's already an exception relationship between the two
        for r_id, rule in self.rules.items():
            a = arg_by_rule.get(r_id)
            if a is None:
                continue
            for r2_id, rule2 in self.rules.items():
                if r_id >= r2_id:
                    continue
                b = arg_by_rule.get(r2_id)
                if b is None:
                    continue
                # Only add mutual conflict if no exception relationship exists
                if (r_id, r2_id) in exception_pairs or (r2_id, r_id) in exception_pairs:
                    continue
                if self._heads_conflict(rule, rule2):
                    attacks.add((a, b))
                    attacks.add((b, a))

        return DungFrame(args=args, attacks=attacks)

    def _premises_satisfied(self, rule: HornRule) -> bool:
        return all(p in self.facts for p in rule.premises)

    def _heads_conflict(self, r1: HornRule, r2: HornRule) -> bool:
        """Two heads conflict if they describe incompatible legal states."""
        # Simple heuristic: if heads are opposite (VALID vs VOID, etc.)
        head_pairs = [
            ("VALID", "VOID"), ("FORMED", "NOT_FORMED"),
            ("BREACH", "PERFORMED"), ("ENFORCEABLE", "UNENFORCEABLE"),
            ("GRANTED", "DENIED"), ("EXIST", "NOT_EXIST"),
        ]
        for pos, neg in head_pairs:
            if (pos in r1.head and neg in r2.head) or \
               (neg in r1.head and pos in r2.head):
                return True
        return False


# ============================================================
# Part C: Fixture Correspondence --- Grounded Extension as Stage 2 Output
# ============================================================

def prove_horn_dung_correspondence():
    """Fixture claim: GE(AF(KB)) matches the stratified encoded output.

    This is not a production-wide proof that GE(AF(KB)) equals the
    original FixpointEvaluator. The original evaluator's rebuttal and
    confidence-zeroing semantics are nonmonotone.

    Proof:
    1. The characteristic function F(S) of a Dung frame is monotone
       on the complete lattice (P(Args), subset).
    2. By the Knaster-Tarski theorem, F has a least fixpoint lfp(F).
    3. The grounded extension GE = lfp(F) by definition.
    4. In the induced frame AF(KB), F(S) adds argument a iff
       all attackers of a are attacked by some argument in S.
    5. In the stratified model, attack/defense edges encode the
       rebuttal/exception layer after Horn closure:
       - An exception rule "attacks" the main rule
       - The exception itself is "defended" if its premises are satisfied
       - The fixpoint converges when no new undefeated arguments arise
    6. Therefore GE(AF(KB)) is the recommended deterministic stage-2
       output for encoded static attack graphs.
    """
    print("=" * 60)
    print("FIXTURE CLAIM: Horn closure + Dung grounded extension correspondence")
    print("=" * 60)

    # Build a test KB with the same structure as juris-calculus rules
    facts = {
        "Fact.Offer.MADE", "Fact.Acceptance.GIVEN",
        "Fact.Performance.FAILED", "Fact.ForceMajeure.OCCURRED",
    }

    # R2 has R3 as exception: "Breach occurred" is EXCUSED by "Force majeure".
    # R4 has R3 as exception: "Breach remedied" is EXCUSED by "Force majeure".
    # Meaning: when Force Majeure fires (R3), it DEFEATS both R2 and R4.
    # In the Dung frame: R3 attacks R2 and R3 attacks R4.
    # R2 should NOT be in grounded; R1 and R3 should.

    rules = [
        HornRule("R1", ["Fact.Offer.MADE", "Fact.Acceptance.GIVEN"],
                 "Contract.Status.FORMED", []),
        HornRule("R2", ["Fact.Performance.FAILED"],
                 "Contract.Breach.OCCURRED", ["R3"]),   # R3 is exception to R2
        HornRule("R3", ["Fact.ForceMajeure.OCCURRED"],
                 "Contract.Breach.EXCUSED", [], depth=2),  # R3 defeats R2
        HornRule("R4", ["Fact.Offer.MADE", "Fact.Acceptance.GIVEN",
                 "Fact.Performance.FAILED"],
                 "Contract.Breach.REMEDIED", ["R3"], depth=3),  # R3 defeats R4 too
    ]

    bridge = HornToDungBridge(rules, facts)
    frame = bridge.construct_frame()

    print(f"\n  Arguments: {len(frame.args)}")
    for a in sorted(frame.args, key=lambda x: x.id):
        print(f"    {a.id}: {a.claim} [{', '.join(a.premises)}]")

    print(f"\n  Attacks: {len(frame.attacks)}")
    for src, tgt in frame.attacks:
        print(f"    {src.id}  attacks  {tgt.id}  ({src.claim} -> {tgt.claim})")

    # Compute extensions
    grounded = frame.grounded_extension()
    print(f"\n  Grounded extension: {[a.claim for a in grounded]}")

    preferred = frame.preferred_extensions()
    print(f"  Preferred extensions: {len(preferred)}")
    for i, ext in enumerate(preferred):
        print(f"    PE[{i}]: {[a.claim for a in ext]}")

    stable = frame.stable_extensions()
    print(f"  Stable extensions: {len(stable)}")

    # Verify correspondence: in exception chain semantics,
    # R3 defeats R2. So grounded should contain R3 and NOT R2.
    # R1 is uncontested. R4 has premises satisfied but R3 attacks R4
    # (R3 is exception of R4). However, R3 is undefended against its
    # own attackers -- but nothing attacks R3 here.
    # So grounded = {R1, R3, R4} if EXCUSED does not conflict with REMEDIED.
    # But they DO conflict: "breach excused" vs "breach remedied".
    # Since R3 -> R4 via exception chain, R3 defeats R4.
    # Grounded = {R1, R3}.

    r2_grounded = any(a.rule_id == "R2" for a in grounded)
    r3_grounded = any(a.rule_id == "R3" for a in grounded)
    r1_grounded = any(a.rule_id == "R1" for a in grounded)

    print(f"\n  R1 (Contract Formed) in grounded: {r1_grounded}")
    print(f"  R2 (Breach) in grounded: {r2_grounded}")
    print(f"  R3 (FM Excuse) in grounded: {r3_grounded}")

    # R3 should defeat R2 (FM occurred, breach excused)
    correct = r1_grounded and r3_grounded and not r2_grounded
    print(f"  Exception chain resolved correctly: {correct}")

    return correct


def prove_complexity():
    """Bounded model claim: GE(AF(KB)) is computable for encoded finite frames.

    Proof:
    1. Building AF(KB): O(N * M) --- check premises for each rule
    2. Attack relation: O(N^2) --- pairwise head conflict check
    3. Grounded extension: O(N^3) --- F(S) iterates at most N times,
       each iteration checking O(N^2) attack pairs
    4. With k <= 3, exception chain depth bounded, reducing
       effective N to ~ |depth-1 rules| = much smaller than |KB|
    """
    print("\n" + "=" * 60)
    print("BOUNDED CLAIM: Grounded Extension Computability")
    print("=" * 60)
    print("""
    AF(KB) construction:  O(N * M)     --- premise satisfaction
    Attack detection:     O(N^2)       --- pairwise head conflict
    Grounded extension:   O(N^3)       --- F(S) fixpoint iteration
      with k <= 3 bound:  O(|depth1|^3) --- only base rules matter

    This is polynomial --- the combined system stays in P.
    """)


if __name__ == "__main__":
    correspondence = prove_horn_dung_correspondence()
    prove_complexity()

    # THEOREM OUTPUT -- GATED on actual correspondence verification
    if not correspondence:
        print("\n" + "=" * 60)
        print("THEOREM (Horn-Dung): NOT VERIFIED")
        print("=" * 60)
        print("  Exception chain not correctly resolved.")
        print("  R2 (Breach) should be DEFEATED by R3 (Force Majeure)")
        print("  in the grounded extension, but the test shows otherwise.")
        exit(1)

    print("\n" + "=" * 60)
    print("SUMMARY: Stratified Rule Algebra + Argumentation Semantics")
    print("=" * 60)
    print(f"""
    CLAIM 1 (Fixture correspondence):
      GE(AF(KB)) matches the encoded stratified fixture above.
      This does not prove equivalence with the original nonmonotone
      production evaluator.

    CLAIM 2 (Bounded computability):
      Finite encoded Dung frames are computable by grounded-extension
      iteration. Production complexity still needs module-level bounds.

    ENGINEERING IMPLICATION:
      Implement a two-stage evaluator: monotone Horn closure first,
      then Dung AAF for rebuttal/exception handling.

    CODE LIFT TARGET:
      Add an AAF shadow pipeline and compare it against production
      evaluator traces before replacing any default semantics.
    """)
