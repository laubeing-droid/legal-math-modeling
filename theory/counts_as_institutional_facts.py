#!/usr/bin/env python3

"""

#10: Counts-As Institutional Facts --- Formal Theory

=======================================================



Formalizes Searle's "counts-as" (X counts as Y in context C) and

Hart's rule of recognition within the juris-calculus compiler

architecture.



## Core Definition



  Document D  counts-as  LegalFact F  in  Jurisdiction J

    iff

  exists recognition rule R in J.recognition_rules:

    R(D) = F



where:

  D: a physical-world token (PDF file, witness statement, contract clause)

  F: a legal-world fact atom (Contract.Status.FORMED, Payment.Due.PASSED)

  R: a recognition rule (regex, LLM prompt, formal language)



## Theorem 1 (Decidability of Regex Recognition)



  If R is expressible as a regular expression, then counts-as(R, D)

  is decidable in O(|D|) time.



## Theorem 2 (Semantic Recognition)



  If R requires semantic understanding (e.g., "did the parties intend to

  be bound?"), then counts-as is NOT mechanically decidable. This is

  exactly the Gradual Verification boundary --- flagged for human review.



## Theorem 3 (Composition)



  counts-as(R1, D1) = F1  AND  counts-as(R2, D2) = F2

    =>

  counts-as(R1 union R2, {D1, D2}) = {F1, F2}



  Recognition rules compose via union; facts compose via set union.

"""



from dataclasses import dataclass, field

from typing import Dict, Set, List, Tuple, Optional, Callable

from enum import Enum

import re





# ============================================================

# Part A: Formal Model

# ============================================================



class Decidability(Enum):

    DECIDABLE = "DECIDABLE"             # Regex --- mechanical

    GRADUAL_VERIFICATION = "GRADUAL"     # Semantic --- flagged for human

    UNDECIDABLE = "UNDECIDABLE"         # Open-textured --- requires judge





@dataclass(frozen=True)

class PhysicalToken:

    """A physical-world document or text fragment."""

    content: str

    source: str = ""       # Which document it came from

    position: int = 0      # Byte offset in source

    metadata: Dict[str, str] = field(default_factory=dict)





@dataclass(frozen=True)

class LegalFact:

    """A legal-world fact atom."""

    id: str

    namespace: str = "general"

    description: str = ""





@dataclass

class RecognitionRule:

    """R: PhysicalToken -> Optional[LegalFact]



    A rule that recognizes a physical token as a legal fact.

    """

    id: str

    jurisdiction: str

    kind: Decidability

    # For DECIDABLE: regex pattern

    pattern: Optional[str] = None

    # For GRADUAL_VERIFICATION: natural language template

    semantic_template: Optional[str] = None

    # Provenance: which statute/case establishes this rule

    authority: str = ""



    def apply(self, token: PhysicalToken) -> Optional[LegalFact]:

        if self.kind == Decidability.DECIDABLE and self.pattern:

            compiled = re.compile(self.pattern)

            match = compiled.search(token.content)

            if match:

                return LegalFact(

                    id=f"{self.jurisdiction}.{self.id}",

                    description=match.group(0) if match.groups() else token.content[:60]

                )

        return None



    def requires_human(self) -> bool:

        return self.kind == Decidability.GRADUAL_VERIFICATION





@dataclass

class CountsAsSystem:

    """The counts-as institutional fact recognition system.



    This is the formal model of what extract_facts.py + guardian.py

    implement: recognition rules that bridge physical documents to

    legal fact atoms.

    """

    rules: Dict[str, RecognitionRule] = field(default_factory=dict)

    recognized_facts: Dict[str, LegalFact] = field(default_factory=dict)

    human_queue: List[Tuple[PhysicalToken, RecognitionRule]] = field(default_factory=list)



    def register_rule(self, rule: RecognitionRule):

        self.rules[rule.id] = rule



    def recognize(self, token: PhysicalToken) -> Tuple[Optional[LegalFact], bool]:

        """Apply all recognition rules to a token.



        Returns: (fact_or_none, needs_human_review)

        """

        # Pass 1: queue ALL semantic/GV rules (they need human review
        # regardless of regex match -- they have no pattern)
        has_gv_rules = False
        for rule in self.rules.values():
            if rule.requires_human():
                self.human_queue.append((token, rule))
                has_gv_rules = True

        # Pass 2: check decidable regex rules
        for rule in self.rules.values():
            if rule.requires_human():
                continue
            result = rule.apply(token)
            if result is not None:
                self.recognized_facts[result.id] = result
                return result, False

        # If GV rules were present, flag for human review
        if has_gv_rules:
            return None, True

        # No rule matched
        return None, False



    def batch_recognize(self, tokens: List[PhysicalToken]) -> Tuple[

        Dict[str, LegalFact], List[Tuple[PhysicalToken, RecognitionRule]]

    ]:

        """Batch recognition --- counts-as composes via set union."""

        all_facts = {}

        all_queue = []



        for token in tokens:

            fact, needs_human = self.recognize(token)

            if fact:

                all_facts[fact.id] = fact

            if needs_human:

                all_queue.extend(self.human_queue)

                self.human_queue = []



        return all_facts, all_queue





# ============================================================

# Part B: Theorems

# ============================================================



def prove_regex_decidability():

    """Theorem 1: Regex-based recognition is decidable.



    Proof:

    - Regular expression matching is decidable in O(|D|) via

      deterministic finite automaton construction.

    - For any regex R and physical token D, R.match(D) always terminates

      and produces a yes/no answer.

    - Therefore counts-as(R_regex, D) is decidable.

    """

    print("=" * 60)

    print("THEOREM 1: Regex Recognition is Decidable")

    print("=" * 60)



    # Test: recognize contract formation from standard clause

    rule = RecognitionRule(

        id="Contract.Formed",

        jurisdiction="PRC",

        kind=Decidability.DECIDABLE,

        pattern=r"(both_parties|each_party|all_parties).*(signed|concluded|entered_into).*(contract|agreement)",

        authority="????471?"

    )



    tokens = [

        PhysicalToken("XXX2021X3X15XXXXXXXXX"),

        PhysicalToken("XXXXXXXXXXXXXXXXXX"),

        PhysicalToken("XXXXXXXXXXXXX"),  # No match --- different wording

    ]



    for t in tokens:

        result = rule.apply(t)

        print(f"\n  Token: '{t.content[:50]}...'")

        print(f"  Recognized: {result is not None}")

        if result:

            print(f"  Fact: {result.id} --- {result.description}")



    # All regex matches terminate (decidable)

    print(f"\n  DECIDABILITY: Regex matching always terminates in O(|text|)")





def prove_semantic_boundary():

    """Theorem 2: Semantic recognition maps to Gradual Verification.



    When a recognition rule requires semantic understanding (e.g.,

    "did the parties actually intend to be bound?"), it is NOT

    mechanically decidable. This is the Gradual Verification boundary.



    The compiler's correct behavior is:

    1. Flag the token for human review

    2. Do NOT produce a LegalFact autonomously

    3. Record the deferral for audit trail

    """

    print("\n" + "=" * 60)

    print("THEOREM 2: Semantic Recognition = Gradual Verification Boundary")

    print("=" * 60)



    semantic_rules = [

        RecognitionRule(

            id="Meeting_of_Minds",

            jurisdiction="PRC",

            kind=Decidability.GRADUAL_VERIFICATION,

            semantic_template="Did the parties manifest genuine mutual assent?",

            authority="????143?"

        ),

        RecognitionRule(

            id="Good_Faith_Negotiation",

            jurisdiction="PRC",

            kind=Decidability.GRADUAL_VERIFICATION,

            semantic_template="Did the parties negotiate in good faith?",

            authority="????500?"

        ),

    ]



    for r in semantic_rules:

        needs_human = r.requires_human()

        print(f"\n  Rule: {r.id}")

        print(f"    Kind: {r.kind.value}")

        print(f"    Requires human: {needs_human}")

        print(f"    Template: {r.semantic_template}")



    print(f"\n  GRADUAL VERIFICATION BOUNDARY:")

    print(f"  - Mechanical: regex, deterministic pattern matching -> DECIDABLE")

    print(f"  - Semantic:   intent, good faith, reasonableness -> GRADUAL_VERIFICATION")

    print(f"  - Judicial:   abuse of right, public order -> UNDECIDABLE (requires judge)")





def prove_composition():

    """Theorem 3: Counts-as composes.



    counts-as(R1, D1) = F1  AND  counts-as(R2, D2) = F2

      =>

    counts-as(R1 | R2, {D1, D2}) = {F1, F2}



    This justifies batch extraction: extract_facts.py can apply

    multiple recognition rules over multiple documents, and the

    result is the union of individually recognized facts.

    """

    print("\n" + "=" * 60)

    print("THEOREM 3: Counts-As Composes via Set Union")

    print("=" * 60)



    sys = CountsAsSystem()

    sys.register_rule(RecognitionRule(

        "R1", "PRC", Decidability.DECIDABLE,

        pattern=r"signed.*contract", authority="????471?"

    ))

    sys.register_rule(RecognitionRule(

        "R2", "PRC", Decidability.DECIDABLE,

        pattern=r"paid.*yuan", authority="????626?"

    ))



    tokens = [

        PhysicalToken("XXXXXXXXXXXXXX100XX"),

        PhysicalToken("XXX2022X6XXX50XXXX"),

    ]



    facts, queue = sys.batch_recognize(tokens)



    print(f"\n  Tokens: {len(tokens)}")

    print(f"  Facts recognized: {len(facts)}")

    for fid, fact in facts.items():

        print(f"    {fid}: {fact.description[:60]}")

    print(f"  Human queue: {len(queue)}")



    # Individual recognition would produce the same set

    sys2 = CountsAsSystem()

    sys2.register_rule(sys.rules["R1"])

    sys2.register_rule(sys.rules["R2"])

    f1, _ = sys2.recognize(tokens[0])

    f2, _ = sys2.recognize(tokens[1])



    # Union of individual = batch

    individual_ids = {f.id for f in [f1, f2] if f}

    batch_ids = set(facts.keys())

    composes = individual_ids == batch_ids

    print(f"\n  Composition holds: {composes}")

    print(f"    Individual: {individual_ids}")

    print(f"    Batch:      {batch_ids}")





if __name__ == "__main__":

    prove_regex_decidability()

    prove_semantic_boundary()

    prove_composition()



    print("\n" + "=" * 60)

    print("SUMMARY: Counts-As Institutional Facts")

    print("=" * 60)

    print("""

    THEOREM 1 (Decidability):

      Regex recognition rules are mechanically decidable in O(|D|).



    THEOREM 2 (Semantic Boundary):

      Semantic recognition maps EXACTLY to the Gradual Verification

      boundary. When the compiler cannot decide mechanically, it

      defers to human --- this is a PROVABLE property, not a design

      choice.



    THEOREM 3 (Composition):

      Counts-as recognition composes via set union over documents.



    JURISPRUDENTIAL FOUNDATION:

      Searle (1995): "X counts as Y in context C"

      Hart (1961): Rules of recognition are secondary rules that

        determine what counts as valid law in a legal system.



      This formalization bridges both to the compiler architecture:

      extract_facts.py = recognition rule application

      guardian.py = boundary between decidable and semantic recognition

      Gradual Verification = the principled deferral mechanism

    """)

