# Argumentation Frameworks Beyond Dung: A Formal Comparison of Dung AF and ASPIC+

**Author:** Legal Math Modeling Research Group
**Date:** 2026-06-27

---

## Abstract

We formally compare Dung abstract argumentation frameworks (AF) and the ASPIC+ framework. The Dung AF core is mechanized in Lean 4 with proved theorems in DungFixedPoint.lean (0 sorry, 0 project-defined axioms; Lean built-in axiom dependencies disclosed where audited), establishing the grounded extension as the unique least fixed point of the characteristic function (`groundedSpec_unique_least_fixed_point`), the labelling as a partition (`labelling_partition`), and soundness properties for IN, OUT, and UNDECIDED labels. ASPIC+ is described at the specification level but is NOT formalized in Lean. We prove (at the hand-proof level) that ASPIC+ strictly subsumes Dung AF: every finite Dung AF can be encoded as an ASPIC+ framework (Encoding Lemma), but ASPIC+ with preferences cannot be fully captured by Dung AF (Strict Subsumption). We identify the formalization of ASPIC+ with preference-based defeat as a key open problem.

**Keywords:** argumentation frameworks, Dung AF, ASPIC+, grounded extension, Lean 4, formal comparison

---

## 1. Introduction

Dung [1995] introduced abstract argumentation frameworks (AF), which represent arguments as nodes and attacks as edges. The semantics (grounded, preferred, stable, complete) are defined via fixed-point operators on sets of arguments. Dung AF is the dominant paradigm in formal argumentation and has been applied to legal reasoning (Prakken and Sartor, 2015), multi-agent systems (Rahwan and Simari, 2009), and AI ethics.

ASPIC+ (Modgil and Prakken, 2014; Prakken, 2010) extends Dung AF with:
1. **Internal argument structure:** arguments are trees of inference rules, not abstract nodes
2. **Preferences:** a preference ordering on arguments determines which attacks succeed as defeats
3. **Three attack types:** rebuttal (contrary conclusion), undermining (contrary premise), undercutting (defeating inference applicability)

The extension is strict: ASPIC+ can express distinctions that Dung AF cannot (e.g., preference-sensitive defeat).

### 1.1 Formalization Status

| Component | Lean Status | File |
|-----------|------------|------|
| Dung AF definitions | Proved (0 sorry) | DungDefinitions.lean |
| Dung grounded extension | 13 theorems, all proved | DungFixedPoint.lean |
| Dung fixed-point kernel | 10 theorems, all proved | FiniteMonotoneIteration.lean |
| ASPIC+ framework | NOT formalized | Planned (no file exists) |
| ASPIC+ preference defeat | NOT formalized | Planned (no file exists) |

---

## 2. Definitions

### 2.1 Dung AF

**Definition 2.1 (Dung AF).** A Dung AF is a pair (Args, Attacks) where Args is a finite set of arguments and Attacks is a subset of Args x Args. Formally in Lean:

```
structure DungAAF where
  args : Finset Arg
  attacks : Finset (Arg x Arg)
```

where `abbrev Arg : Type := String`.

The characteristic function F is defined as:

F(S) = {a in Args : for all b with (b, a) in Attacks, exists c in S with (c, b) in Attacks}

The grounded extension GE is the least fixed point of F, computed by iterating from the empty set:

GE = iter_F^n(empty) where n = |Args|

### 2.2 ASPIC+ Framework

**Definition 2.2 (ASPIC+ Framework).** An ASPIC+ framework is a tuple (K, n, R, <=) where:
- K is a set of premises (knowledge base)
- n is a naming function mapping rules to names
- R is a set of inference rules (strict rules R_s and defeasible rules R_d)
- <= is a preference ordering on rules

**Definition 2.3 (Argument).** An argument in ASPIC+ is a tree where:
- Leaves are premises from K
- Internal nodes are applications of rules from R
- The conclusion is the root

**Definition 2.4 (Contraries).** A contraries function maps each formula to a set of formulas that contradict it.

**Definition 2.5 (Attack and Defeat).** An attack on argument A by argument B is one of:
- **Rebuttal:** B's conclusion is contrary to A's defeasible sub-conclusion
- **Undermining:** B's conclusion is contrary to A's premise
- **Undercutting:** B's conclusion attacks the applicability of A's rule

An attack becomes a defeat if the attacker is preferred to or equal to the target in the ordering <=.

**Definition 2.6 (Dung Translation).** Given an ASPIC+ framework F, the Dung translation T(F) maps each argument to a node and each defeat to an attack edge, discarding internal structure and preferences.

---

## 3. Main Results

### 3.1 Encoding Lemma

**Lemma 3.0 (Encoding Lemma).** Every finite Dung AF can be encoded as an ASPIC+ framework such that the Dung translation of the encoding recovers the original AF.

**Proof sketch.** Given a Dung AF (Args, Attacks):
- Let K = Args (each argument is a premise)
- Let R_s = empty (no strict rules)
- Let R_d = {r_a : a in Args} where r_a has premise a and conclusion a (identity rules)
- Let <= be the trivial ordering (all rules equally preferred)
- For each attack (b, a) in Attacks, define the contraries so that b's conclusion is contrary to a's premise

Then T(F) = (Args, Attacks). QED.

### 3.2 Weak Subsumption

**Theorem 3.1 (Weak Subsumption).** Every semantics that can be defined on Dung AF can also be defined on ASPIC+ frameworks (via the Dung translation).

**Proof.** By Lemma 3.0, the Dung translation is surjective. Therefore any function defined on Dung AF can be pulled back to ASPIC+ via the translation. QED.

### 3.3 Strict Subsumption

**Theorem 3.2 (Strict Subsumption).** There exist ASPIC+ frameworks with preferences whose defeat relation cannot be captured by any Dung AF.

**Proof.** Consider two arguments A and B where A attacks B and B attacks A (symmetric attack). In a Dung AF without preferences, neither argument is in the grounded extension (both are undecided). In ASPIC+ with the preference A <= B (A is less preferred), B defeats A but A does not defeat B. The grounded extension of the resulting defeat graph contains B but not A.

No Dung AF can express this asymmetric defeat from symmetric attacks: in a Dung AF, if (A, B) and (B, A) are both in Attacks, the structure is symmetric and the grounded extension cannot distinguish A from B. QED.

### 3.4 Grounded Extension Under Preferences

**Theorem 3.3.** Under a strict partial order on arguments, the grounded extension exists and is unique.

**Proof sketch.** A strict partial order is irreflexive and transitive. The defeat relation D defined by:

(A, B) in D iff (A, B) in Attacks and not (B < A in preferences)

is well-defined. The characteristic function F_D is monotone (since defeating fewer attacks can only add arguments to the defended set). By Knaster-Tarski, the least fixed point exists and is unique. QED.

---

## 4. Lean Formalization of Dung AF

### 4.1 Core Theorems (DungFixedPoint.lean)

All 13 theorems are proved with 0 sorry:

| Theorem | Statement |
|---------|-----------|
| `F_monotone` | The characteristic function is monotone |
| `groundedSpec_is_fixed_point` | GE is a fixed point of F |
| `groundedSpec_is_least_fixed_point` | GE is the least fixed point |
| `groundedSpec_unique_least_fixed_point` | GE is the unique least fixed point |
| `labelling_partition` | IN, OUT, UNDECIDED partition args |
| `in_soundness` | Every IN argument has all attackers attacked by IN |
| `out_soundness` | Every OUT argument has an attacker in IN |
| `undecided_characterization` | UNDECIDED iff not in GE and no attacker in GE |
| `self_attack_precise_theorem` | Self-attacking arguments with only self-attackers are excluded |
| `finite_termination` | Iteration count <= |args| |

### 4.2 What Is NOT Formalized

The following are NOT in the Lean codebase:
- ASPIC+ framework definitions
- Preference orderings on arguments
- Preference-based defeat
- Undercutting and undermining attacks
- Translation from ASPIC+ to Dung AF
- Strict subsumption theorem (Theorem 3.2)

These are identified as open formalization problems.

---

## 5. Open Problems

1. **ASPIC+ Formalization.** Define the ASPIC+ framework in Lean 4 with inference rules, contraries, and preference orderings.
2. **Preference-Based Defeat.** Formalize the defeat relation conditioned on a strict partial order.
3. **Strict Subsumption Mechanization.** Prove Theorem 3.2 in Lean by constructing the explicit counterexample.
4. **Grounded Extension Under Preferences.** Mechanize Theorem 3.3 by showing that the defeat relation under a strict partial order is monotone.
5. **Legal Application.** Apply the ASPIC+ formalization to the juris-calculus canonical semantics, mapping `CanonicalAttack` kinds (REBUTTAL, EXCEPTION, PRIORITY_DEFEAT) to ASPIC+ attack types.

---

## References

1. Dung, P.M. (1995). On the acceptability of arguments and its fundamental role in nonmonotonic reasoning, logic programming and n-person games. *Artificial Intelligence*, 77(2), 321--357.
2. Prakken, H. (2010). An abstract framework for argumentation with structured arguments. *Argument and Computation*, 1(2), 93--124.
3. Modgil, S. and Prakken, H. (2014). The ASPIC+ framework for structured argumentation: a tutorial. *Argument and Computation*, 5(1), 31--62.
4. Besnard, P. and Hunter, A. (2008). *Elements of Argumentation*. MIT Press.
5. Bench-Capon, T.J.M. and Dunne, P.E. (2007). Argumentation in artificial intelligence. *Artificial Intelligence*, 171(10--15), 619--641.
6. Rahwan, I. and Simari, G.R. (2009). *Argumentation in Artificial Intelligence*. Springer.
7. Prakken, H. and Sartor, G. (2015). Law and logic: a review from an argumentation perspective. *Artificial Intelligence*, 227, 214--245.
8. The mathlib Community (2020). The Lean mathematical library. *CPP 2020*, 367--381.
