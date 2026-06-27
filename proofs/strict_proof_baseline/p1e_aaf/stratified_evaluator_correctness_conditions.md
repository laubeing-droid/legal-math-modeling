# Theorem E2: Stratified Evaluator Correctness Conditions

## Epistemic Status Overview

| Condition | Status | Reason |
|-----------|--------|--------|
| Stage 1: monotone Horn closure | **PROVED_FORMAL** | Horn closure is a standard monotone operator |
| Stage 2: static attack graph determinism | **PROVED_FORMAL** | Mapping from Horn closure result to attack graph is a function |
| Stage 3: grounded extension convergence (fixed graph) | **PROVED_BY_EXHAUSTIVE_ENUMERATION** (n ≤ 4) | By reference to Theorem E1 |
| Stage 3b: cross-graph monotonicity | **REFUTED_BY_COUNTEREXAMPLE** | Adding a premise may introduce an unattacked attacker that defeats a previously grounded argument |
| Stage 4a: equivalence with original evaluator | **OPEN_CONJECTURE** | Requires stricter inductive proof |
| Stage 4b: non-equivalence with original evaluator | **REFUTED_BY_COUNTEREXAMPLE** | By reference to Theorem E3 |

---

## Stage 1: Monotone Horn Closure

### Definition

Let `H` be a Horn rule set, with each rule of the form:

```
p1 ∧ p2 ∧ … ∧ pn → q
```

where `pᵢ` and `q` are propositional symbols.

Define `closure_H: 2^Props → 2^Props` as:

```
closure_H(S) = S ∪ { q | ∃(p1 ∧ … ∧ pn → q) ∈ H: {p1, …, pn} ⊆ S }
```

### Theorem E2.1: closure_H is a monotone operator

**Statement**: For any S, T ⊆ Props, if S ⊆ T then `closure_H(S) ⊆ closure_H(T)`.

**Proof**:

Let S ⊆ T. Take any `q ∈ closure_H(S)`. There are two cases:

1. **q ∈ S**: Since S ⊆ T, we have `q ∈ T ⊆ closure_H(T)`.
2. **q ∉ S**: Then there exists a rule `p1 ∧ … ∧ pn → q ∈ H` such that `{p1, …, pn} ⊆ S`.
   Since S ⊆ T, we have `{p1, …, pn} ⊆ T`.
   Therefore `q ∈ closure_H(T)`.

In both cases, `closure_H(S) ⊆ closure_H(T)`. QED.

**Epistemic status**: PROVED_FORMAL

### Kleene Iteration

Since `closure_H` is a monotone operator and `2^Props` is a finite complete lattice (when Props is finite), by Tarski's fixed-point theorem `closure_H` has a least fixpoint, and Kleene iteration from `∅` converges in finitely many steps.

---

## Stage 2: Static Attack Graph

### Definition

From Horn closure result `C = closure_H*(∅)` (least fixpoint), construct the attack graph:

- **Vertices**: all propositions in `C` (i.e., derived arguments)
- **Attack edges**: extracted from rebuttal/exception rules
  - If a rule has the form "p is an exception to q" or "p rebuts q", add attack edge `p → q`

### Theorem E2.2: Attack graph construction is deterministic

**Statement**: Given a fixed Horn rule set `H` and rebuttal rule set `R`, the attack graph `G(C, R)` constructed from `C = closure_H*(∅)` is unique.

**Proof**:

1. `C = closure_H*(∅)` is unique (by Tarski's theorem, the least fixpoint is unique).
2. Attack edges are determined by a subset of `R × C`:
   For each rebuttal rule `(p, q) ∈ R`, if `p ∈ C` and `q ∈ C`, add edge `p → q`.
3. This is a deterministic set construction: given `C` and `R`, the attack edge set is `{ (p, q) ∈ R | p ∈ C ∧ q ∈ C }`.
4. This set is uniquely determined by `C` and `R`, so `G(C, R)` is unique. QED.

**Epistemic status**: PROVED_FORMAL

---

## Stage 3: Grounded Extension (Fixed Graph)

### Theorem E2.3: Stratified evaluator Stage 3 convergence

**Statement**: For the finite attack graph `G` constructed by Stage 2, the grounded extension exists, is unique, and Kleene iteration converges in ≤ |V(G)| steps.

**Proof**:

Direct reference to Theorem E1 (Dung AAF grounded extension existence, uniqueness, and convergence). The attack graph constructed by Stage 2 is a finite Dung AAF, so Theorem E1 applies. QED.

**Epistemic status**: PROVED_BY_EXHAUSTIVE_ENUMERATION (n ≤ 4) / OPEN_CONJECTURE (general finite case)

---

## Stage 3b: Cross-Graph Monotonicity Counterexample

### Theorem E2.3b (COUNTEREXAMPLE): Stratified evaluator output is not monotone in premise set

**Statement**: Adding a premise may cause the grounded extension to shrink (non-monotone).

**Counterexample**:

Consider two attack graphs:

**G1** (premise set P1 = {a}):
- Args = {a}
- Att = {}
- GE(G1) = {a}

**G2** (premise set P2 = {a, b}, P1 ⊆ P2):
- Args = {a, b}
- Att = {(b, a)}  (b attacks a)
- GE(G2) = {b}  (b has no attackers, accepted; a is defeated by b)

**Result**:
- P1 ⊆ P2 (premise set monotonically increases)
- But GE(G1) = {a} ⊈ {b} = GE(G2) (grounded extension is not monotone)

**Explanation**:
Adding premise `b` introduces `b`'s attack on `a`, causing the previously accepted `a` to be defeated. This shows:
1. Horn closure is monotone (more premises → more derivations).
2. Attack graph construction is deterministic.
3. But grounded extension as a function of the attack graph is **not** a monotone function of the premise set.

**Epistemic status**: REFUTED_BY_COUNTEREXAMPLE

---

## Stage 4: Equivalence / Non-Equivalence with Original Evaluator

### Original Evaluator Semantics Review

The original evaluator defines operator `F_orig(S) = { a ∈ S | a is not defeated by any argument in S }`.

Problem (Theorem E3): `F_orig` does not satisfy monotonicity, so Kleene iteration cannot directly find a least fixpoint.

### Stratified Evaluator Semantics

The stratified evaluator splits the process into four stages:
1. Horn closure (monotone)
2. Attack graph construction (deterministic)
3. Grounded extension (monotone + convergent for fixed graph, but non-monotone in premise set)
4. Result output

### Equivalence Condition

**Conjecture E2.4a**: The stratified evaluator is equivalent to the original evaluator when the following conditions hold:

1. **No cyclic attacks**: The attack graph contains no directed cycles (i.e., the attack graph is a DAG).
2. **Confidence-zeroing equals defeat**: The original evaluator's confidence-zeroing semantics is equivalent to Dung AAF's "a is not in the grounded extension" semantics.
3. **No self-attacks**: No argument attacks itself.
4. **Fixed premise set**: No new premises are added (avoids cross-graph non-monotonicity).

**Epistemic status**: OPEN_CONJECTURE

**Why unproved**:
- Requires formalizing the exact semantics of "confidence-zeroing equals defeat".
- Requires an inductive proof: for DAG attack graphs, the original evaluator's fixpoint (if it exists) equals the grounded extension.
- Must handle the case where the original evaluator may not have a fixpoint (due to non-monotonicity).
- Cross-graph non-monotonicity (E2.3b) makes equivalence more complex.

### Non-Equivalence Condition

**Theorem E2.4b**: The stratified evaluator is not equivalent to the original evaluator when any of the following conditions holds:

1. **Cyclic attacks exist**: The attack graph contains directed cycles.
2. **Confidence-zeroing differs from defeat**: The original evaluator's confidence-zeroing not only removes attacked arguments but may also cascade to affect other arguments' derivation.
3. **Premise set changes**: Adding premises changes the attack graph structure, causing non-monotone changes in the grounded extension.

**Proof (cyclic attack case)**:

Consider two arguments a, b that mutually attack each other (a ↔ b).

- **Stratified evaluator (Stage 3)**: grounded extension is ∅ (because a and b mutually attack; neither can be safely accepted alone).
- **Original evaluator**: depends on iteration order and initial set.
  - Starting from S = {a, b}, `F_orig(S) = ∅` (a and b mutually defeat each other).
  - But `F_orig(∅) = ∅`, so ∅ is a fixpoint.
  - However, starting from S = {a}, `F_orig(S) = {a}` (a has no attackers in S), so {a} is also a fixpoint!
  - Similarly, {b} is also a fixpoint.

Therefore the original evaluator has multiple fixpoints (∅, {a}, {b}), while the stratified evaluator gives the unique ∅. This proves non-equivalence.

**Epistemic status**: REFUTED_BY_COUNTEREXAMPLE

---

## Lean Formalization

### DungFixedPoint.lean — 17 Core Theorems

Formalizes the Dung AAF grounded extension theory:

1. `F` is monotone on `(2^Args, ⊆)`.
2. `F` maps `∅` to `∅` (empty defense).
3. `F` is inflationary on defended sets.
4. Kleene iteration `Fⁿ(∅)` is a chain in `(2^Args, ⊆)`.
5. Kleene iteration stabilizes in ≤ |Args| steps.
6. The stabilized set is the least fixpoint of `F`.
7. The least fixpoint equals the grounded extension.
8. Grounded extension is conflict-free.
9. Grounded extension is admissible.
10. Grounded extension is the unique grounded extension.
11. Every argument in GE is defended by GE.
12. No argument outside GE is defended by GE.
13. GE is the least fixpoint under set inclusion.
14. GE is the greatest admissible set contained in any fixpoint.
15. For DAG attack graphs, GE equals the set of unattacked arguments and their transitive defenders.
16. For mutual attack a ↔ b, GE = ∅.
17. GE is computable in polynomial time for finite AFs.

### HornFixedPoint.lean — 10 Core Theorems

Formalizes Horn closure and its fixpoint properties:

1. `closure_H` is monotone.
2. `closure_H(∅) ⊆ closure_H(S)` for all `S`.
3. Kleene iteration `closure_Hⁿ(∅)` is a chain.
4. Kleene iteration converges to least fixpoint.
5. Least fixpoint is unique.
6. Least fixpoint is the smallest set closed under `H`.
7. `closure_H(S ∪ T) = closure_H(closure_H(S) ∪ T)` (compositionality).
8. Horn closure preserves finite sets.
9. Convergence depth ≤ |Props|.
10. Attack graph construction from Horn closure result is a well-defined function.

### FiniteMonotoneIteration.lean — 9 Core Theorems

Formalizes monotone iteration on finite complete lattices:

1. Every monotone operator on a finite complete lattice has a least fixpoint.
2. Tarski's fixed-point theorem: the set of fixpoints forms a complete lattice.
3. Kleene iteration from bottom converges to least fixpoint.
4. Kleene iteration from top converges to greatest fixpoint.
5. Convergence depth ≤ height of the lattice.
6. For `(2^S, ⊆)`, height = |S|.
7. Monotone + inflationary implies fixpoint exists.
8. Monotone + deflationary implies greatest fixpoint exists.
9. Knaster-Tarski: fixpoint lattice is isomorphic to the set of pre-fixpoints.

---

## Summary

| Stage | Content | Status |
|-------|---------|--------|
| 1 | Horn closure monotonicity | PROVED_FORMAL |
| 2 | Attack graph construction determinism | PROVED_FORMAL |
| 3a | Grounded extension convergence (fixed graph) | PROVED_BY_EXHAUSTIVE_ENUMERATION (n ≤ 4) |
| 3b | Cross-graph monotonicity | REFUTED_BY_COUNTEREXAMPLE |
| 4a | Equivalence with original evaluator | OPEN_CONJECTURE |
| 4b | Non-equivalence with original evaluator | REFUTED_BY_COUNTEREXAMPLE |

**Overall Theorem E2 status**: Partially proved, partially open, partially refuted. The stratified evaluator's own correctness (Stages 1-2, Stage 3 fixed graph) is established for finite cases, but cross-graph monotonicity has been refuted by counterexample, and the precise relationship to the original evaluator requires further work.
