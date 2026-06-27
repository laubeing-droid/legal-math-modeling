# Theorem Statements: E1, E2, E3

---

## Theorem E1: Finite Dung AAF Grounded Extension Existence and Uniqueness

### Formal Statement

Let AF = (Args, Att) be a finite Dung abstract argumentation framework, where:
- Args is a finite non-empty set of arguments
- Att ⊆ Args × Args is a directed attack relation

Define the characteristic function `F: 2^Args → 2^Args` as:

```
F(S) = { a ∈ Args | ∀b ∈ Args: (b, a) ∈ Att → ∃c ∈ S: (c, b) ∈ Att }
```

That is, `F(S)` is the set of all arguments "defended" by `S`.

**Theorem E1.1 (Existence)**: For any finite AF, the grounded extension GE(AF) exists.

**Theorem E1.2 (Uniqueness)**: For any finite AF, the grounded extension GE(AF) is unique.

**Theorem E1.3 (Convergence)**: For any finite AF, the Kleene iteration sequence ∅, F(∅), F²(∅), … converges to GE(AF) in finitely many steps.

**Theorem E1.4 (Convergence Depth Bound)**: For a finite AF with |Args| = n, Kleene iteration converges in ≤ n steps.

### Proof Method

- **E1.1–E1.3**: Based on Tarski's fixed-point theorem (`F` is a monotone operator on the complete lattice `(2^Args, ⊆)`).
- **E1.4**: Exhaustive verification (n ≤ 4, enumerating 2^(n²) attack graphs).

### Epistemic Status

- **n ≤ 4**: PROVED_BY_EXHAUSTIVE_ENUMERATION
- **General finite case**: OPEN_CONJECTURE (relies on standard Tarski proof, but convergence depth bound `n` requires inductive proof)

---

## Theorem E2: Stratified Evaluator Correctness Conditions

### Formal Statement

Let:
- `H` be a finite Horn rule set
- `R` be a finite rebuttal/exception rule set
- `Props` be a finite set of propositional symbols

Define the stratified evaluator as a four-stage pipeline:

**Stage 1**: `closure_H: 2^Props → 2^Props`
```
closure_H(S) = S ∪ { q | ∃(p₁ ∧ … ∧ pₙ → q) ∈ H: {p₁, …, pₙ} ⊆ S }
```

**Stage 2**: `attack_graph: 2^Props → AttackGraph`
```
attack_graph(C) = (C, { (p, q) ∈ R | p ∈ C ∧ q ∈ C })
```

**Stage 3**: `grounded_extension: AttackGraph → 2^Props`
```
grounded_extension(G) = lfp(F_G)   (F_G is G's characteristic function)
```

**Stage 4**: `output: 2^Props → Result`

**Theorem E2.1 (Stage 1 Monotonicity)**: `closure_H` is a monotone operator, i.e., `S ⊆ T → closure_H(S) ⊆ closure_H(T)`.

**Theorem E2.2 (Stage 2 Determinism)**: `attack_graph` is a deterministic function, i.e., given `C` and `R`, `attack_graph(C)` is unique.

**Theorem E2.3 (Stage 3 Convergence)**: For the finite attack graph `G` output by Stage 2, `grounded_extension(G)` exists, is unique, and Kleene iteration converges in finitely many steps.

**Theorem E2.3b (Cross-Graph Monotonicity Counterexample)**: Adding a premise may cause the grounded extension to shrink (non-monotone in premise set).

**Conjecture E2.4a (Equivalence Condition)**: If the attack graph is a DAG and confidence-zeroing semantics equals defeat, then the stratified evaluator's output equals the original evaluator's output.

**Theorem E2.4b (Non-Equivalence Condition)**: If the attack graph contains directed cycles, then the stratified evaluator is not equivalent to the original evaluator.

### Epistemic Status

| Sub-theorem | Status |
|-------------|--------|
| E2.1 | PROVED_FORMAL |
| E2.2 | PROVED_FORMAL |
| E2.3 | PROVED_BY_EXHAUSTIVE_ENUMERATION (n ≤ 4) |
| E2.3b | REFUTED_BY_COUNTEREXAMPLE |
| E2.4a | OPEN_CONJECTURE |
| E2.4b | REFUTED_BY_COUNTEREXAMPLE |

---

## Theorem E3: Original Evaluator Does Not Satisfy Tarski Monotonicity

### Formal Statement

Let the original evaluator's operator be `F_orig: 2^Args → 2^Args`:

```
F_orig(S) = { a ∈ S | ¬∃b ∈ S: (b, a) ∈ Att }
```

That is, `F_orig(S)` is the set of arguments in `S` not attacked by any argument in `S`.

**Theorem E3.1 (Non-Monotonicity)**: `F_orig` is not a monotone operator.

That is: there exist `A, B ⊆ Args` such that `A ⊆ B` but `F_orig(A) ⊈ F_orig(B)`.

### Counterexample

Let `Args = {a, b}`, `Att = {(b, a)}`.

- `A = {a}`, `F_orig(A) = {a}` (a has no attackers in A).
- `B = {a, b}`, `F_orig(B) = ∅` (b attacks a, so a is removed).

Verification: `A ⊆ B`, but `F_orig(A) = {a} ⊈ ∅ = F_orig(B)`.

### Epistemic Status

- **E3.1**: REFUTED_BY_COUNTEREXAMPLE

### Corollary

Since `F_orig` does not satisfy monotonicity:
1. The least fixpoint is not guaranteed to exist (Tarski's theorem preconditions fail).
2. Even if a fixpoint exists, it is not guaranteed to be unique.
3. Kleene iteration may not converge or may converge to an unintended result.

---

## Dependency Graph

```
E2.1 (Horn closure monotonicity) ──┐
                                    ├──→ E2.3 (Stage 3 convergence) ──→ E2 (overall correctness)
E1 (Grounded extension) ─────────────┘

E3 (Evaluator non-monotonicity) ────→ E2.4b (non-equivalence condition)

E2.4a (equivalence condition) ─────→ OPEN_CONJECTURE
```

---

## Lean Formalization References

| Lean File | Core Theorems | Coverage |
|-----------|---------------|----------|
| `DungFixedPoint.lean` | 17 core theorems | E1.1–E1.4, grounded extension theory |
| `HornFixedPoint.lean` | 10 core theorems | E2.1, E2.2, Horn closure fixpoint properties |
| `FiniteMonotoneIteration.lean` | 9 core theorems | E1.3, E1.4, Tarski/Knaster-Tarski on finite lattices |
| `DungDefinitions.lean` | foundational definitions | Args, Att, F, conflict-free, admissible, grounded |
| `DungAAF.lean` | AAF framework definitions | Abstract argumentation framework formalization |
| `HornDefinitions.lean` | Horn rule definitions | Rule syntax, propositional symbols, closure operator |
| `HornOperationalRefinement.lean` | operational refinement | Stratified evaluator pipeline formalization |

---

## File Index

| File | Content | Theorems |
|------|---------|----------|
| `aaf_grounded_extension_proof.py` | Exhaustive verification n ≤ 4 | E1 |
| `evaluator_nonmonotone_counterexample.py` | Non-monotonicity counterexample | E3 |
| `stratified_evaluator_correctness_conditions.md` | Stratified evaluator conditions | E2 |
| `theorem_statement.md` | Theorem formalization statements | E1, E2, E3 |
