# juris-calculus Mathematical Proof Logic Audit Report

Audit date: 2026-06-09
Audit basis: CLAUDE_MATH_PROOF_LOGIC_AUDIT_PROMPT.md
Experiment data: <verification-runs-root>
Latest run: 20260609-214205-full-suite-all-verification

---

## 1. Overall Conclusion

The mathematical proof logic of juris-calculus is in a state of mixed maturity. Seven formal verification tools were applied, but the number of entries that can strictly be called fully verified proofs is small. The primary patterns:

- Pass items: Hypothesis property tests (6/6), Z3 bounded-domain proofs, Dafny model verification, TLA+/Alloy bounded model checks
- Refuted item: Graph similarity strict reflexivity was empirically falsified (`sim(G,G)=0.4` rather than 1.0)
- Inconclusive item: CrossHair returned Not confirmed
- Skeleton item: Lean verified only an identity skeleton; the genuine Galois adjunction was not addressed
- Blocked item: Project full pytest fails at collection due to missing configs/en_US/rules.yaml

Actionable items: complete the missing config file; demote the graph similarity theorem; advance the Lean skeleton from identity to a genuine powerset Galois connection; extend TLA+ from a guard skeleton to the full evaluator state machine.

---

## 2. Trust Label Summary Table

| Theorem/Module | Current Evidence | Recommended Label | Can Be Called Proof | Reason |
| --- | --- | --- | --- | --- |
| Python/Hypothesis property tests | 6/6 passed | TESTED_PROPERTY | No | Property tests passing does not equal a universal proof |
| Graph similarity strict reflexivity | Counterexample sim(G,G)=0.4 | REFUTED | No | Conservative empty-feature semantic causes reflexivity to fail |
| Z3 graph range [0,1] | UNSAT on sim<0, sim>1 | SMT_PROVED_FINITE | Yes (abstract real domain) | Z3 proves no range violation for arbitrary real inputs |
| Z3 finite Galois sanity | 0 violations | SMT_PROVED_FINITE | Yes (finite enumeration domain) | Finite atoms/descriptions enumeration passes |
| CrossHair graph contract | Not confirmed | INCONCLUSIVE | No | CrossHair neither proved nor refuted |
| TLA+ oscillation guard | No error found | MODEL_CHECKED | No | Only a bounded guard skeleton, not the full evaluator |
| Alloy relation disjoint | UNSAT | MODEL_CHECKED | No | Bounded Alloy scope, not infinite domain |
| Lean Galois skeleton | exit 0 | LEAN_PROVED_SKELETON | No | Only identity skeleton; not the alpha/gamma adjunction of juris-calculus |
| Dafny graph range | 1 verified, 0 errors | SMT_PROVED | Yes (within Dafny model) | Dafny verifier passes |
| Project unit tests | 32 passed | REGRESSION_PASS | N/A | Unit test regression passes |
| Project full pytest | Collection failed | BLOCKED_BY_MISSING_FIXTURE | N/A | configs/en_US/rules.yaml missing |
| Galois connection (theory/) | Finite sanity + Z3 + Lean skeleton | MIXED: SMT_PROVED_FINITE + LEAN_PROVED_SKELETON | Partial | Finite check passes; full adjunction not proved in Lean |
| Fixpoint convergence | Bounded model + Hypothesis | MIXED: TESTED_PROPERTY + MODEL_CHECKED | No | Tarski applies only to abstract claim-set fragment; full evaluator has rebuttal/critical halt that break global monotonicity |
| Non-Horn formalizable score | Hypothesis test passes | TESTED_PROPERTY | No | Sigmoid smoothing improves continuity, but weights (0.2,0.2,0.4,0.2) remain empirical parameters |
| DP ratio-preserving | dp_diagnostics instrumentation | EMPIRICAL_HYPOTHESIS | No | Instrumentation is not a DP proof; adjacency/sensitivity/floor/rounding are not formalized |
| Banach contraction | Analytic c=0.5 proof | Partial | Partial | Analytic compression proof for exponential smoothing is valid, but applies only to the effective_nodes dimension |
| Category theory natural transform | Executable counter-proof | TESTED_PROPERTY | No | Surjectivity failure detection is effective, but is not a category-theoretic formal proof |

---

## 3. Proved or Partially Proved

### 3A. Z3 + Dafny: Graph Similarity Range Does Not Exceed Bounds

- Z3: Proved that `sim<0` and `sim>1` are both UNSAT for abstract real domain variables r, i, a.
- Dafny: Independently verified graph similarity output range [0,1].
- Conclusion: Graph similarity staying within [0,1] is SMT-provable.

### 3B. Z3 Finite Galois Sanity

- For finite atoms/descriptions enumeration: 0 violations.
- Limitation: This is a finite-domain proof, not a full Galois adjunction universal proof.

### 3C. Banach Contraction c=0.5

- Exponential smoothing `c = 1 - beta = 0.5 < 1` is an analytic proof (not numerical testing).
- Constraint: Applies only to the effective_nodes dimension.
- Assessment: This partial proof is valid.

### 3D. TLA+ / Alloy Bounded Model Check

- TLA+ oscillation guard skeleton: No error found.
- Alloy relation disjoint skeleton: UNSAT.
- Limitation: Bounded scope, not infinite-domain proof.

---

## 4. Refuted by Counterexample

### Graph Similarity Strict Reflexivity -- REFUTED

Counterexample:
```
G = (v=1, e=0, features=empty set)
sim(G, G) = 0.4
```

Analysis: Empty feature set causes jaccard=0.0 (conservative semantic), size_ratio=1.0, and weighted result sim=0.4. This is a consistent design decision (empty features cannot determine similarity), but it constitutes a counterexample to any blanket strict reflexivity claim.

Correction suggestion: Demote "forall G: sim(G,G)=1" to "forall G with non-empty features: sim(G,G)=1," or explicitly state that empty features are a conservative degenerate boundary case.

---

## 5. Tests Passed but Not Proof

### 5A. Hypothesis Property Tests (TESTED_PROPERTY)

- 6 passed; tested randomly constructed Horn knowledge bases.
- Not proof: Hypothesis is random search and cannot substitute for a universal proof.

### 5B. Non-Horn Formalizable Score (TESTED_PROPERTY)

- Sigmoid smoothing continuity passes tests.
- Weights (0.2, 0.2, 0.4, 0.2) remain empirical parameters with no formalized calibration.

### 5C. Category Theory Natural Transform (TESTED_PROPERTY)

- Executable counter-proof (surjectivity failure detection) is effective.
- But it is not a category-theoretic formal proof.

---

## 6. Proof Skeletons Only

### 6A. Lean Galois Skeleton (LEAN_PROVED_SKELETON)

- Compiled successfully (exit 0).
- But only an identity skeleton: verified `a = a` and `a <= a` and similar identity properties.
- Did not touch the definition of alpha/gamma functions or the Galois adjunction condition `alpha(d) subseteq {a} <=> d in gamma(a)`.
- Gap: Need to define concrete signatures for `alpha` and `gamma` and prove the bidirectional implication.

### 6B. TLA+ Oscillation Guard Skeleton (MODEL_CHECKED)

- Only a bounded guard model.
- Did not model the full evaluator (missing fact state, rebuttal log, CriticalClarityFailure).
- Gap: Needs extension to the full evaluator state machine.

---

## 7. Still Conjecture / Empirical Hypothesis

### 7A. DP Ratio-Preserving Mechanism (EMPIRICAL_HYPOTHESIS)

- `dp_diagnostics` is audit instrumentation, not a DP proof.
- Missing: Adjacent dataset definition, sensitivity computation, tuple-level privacy guarantees, privacy impact of floor clipping.

### 7B. Fixpoint Convergence (MIXED)

- Tarski applies only to the abstract claim-set fragment.
- The full evaluator includes rebuttal, state_tracker modification, and confidence zeroing -- all of which break global monotonicity.

### 7C. Kolmogorov MDL (CONJECTURE)

- P(FP) ~ 2^{-MDL(r)} is a hypothesis, not a theorem.
- Already labeled as CONJECTURE in the codebase.

---

## 8. Mathematical Model Correction Suggestions

1. Graph similarity: Demote from "metric" to "similarity function." Strict reflexivity has been refuted by counterexample; the triangle inequality was never proved.
2. Fixpoint convergence: Change from "Tarski guarantees convergence" to "abstract claim-set fragment converges under Tarski; full evaluator has bounded operational termination via rules_applied finiteness + max_iterations."
3. DP ratio-preserving: Change from "provides tuple-level DP" to "provides conditional DP under scalar principal query adjacency; floor clipping + rounding affect utility but not per-se DP."
4. M17 Calibration Theorem: Rename to "Expert Agreement Score" (not calibration).
5. Oscillation guard: Define as "detection mechanism with counter logging"; remove the "absorbing halted state" claim.

---

## 9. Source Code Correction Suggestions

1. configs/en_US/rules.yaml: Provide or fix it to unblock project full pytest collection.
2. ConstraintValidator: Comment has been changed to block, but code still passes through -- unify to logging-only and correct the comment, or implement the absorbing state.
3. SemanticFactMatcher: Completed: threshold parameterized (default 0.35), hardcoding removed.
4. evaluator._apply_rule(): Completed: recursion visited set implemented.

---

## 10. Future Lean/Z3/TLA+ Proof Route Suggestions

1. Lean: Advance from identity skeleton to a genuine Galois connection. Define `alpha: Set String -> Set Atom` and `gamma: Atom -> Set String`. Prove `alpha(d) subseteq {a} <=> d in gamma(a)`.
2. TLA+: Extend from guard skeleton to the full evaluator. Model five state variables: facts, claims, rules_applied, state_tracker, rebuttal_log. Prove bounded operational termination.
3. Z3: Continue for bounded-domain proofs (graph range, Kripke mutex, temporal induction). Cost-effective on abstract domains without requiring the full state space.
4. Dafny: Extend to graph similarity triangle inequality checking (if calling it a metric) or label as non-metric similarity.
5. CrossHair: Re-test inconclusive items with simpler contracts, or convert to Z3 proofs.

---

## 11. Final Ratings

| Dimension | Rating | Explanation |
| --- | --- | --- |
| Test coverage | PASS | Hypothesis + Z3 + Dafny + TLA+ + Alloy multi-tool coverage |
| Strict proof | SUSPECT | Strict proofs exist only for finite/abstract domains; most theorems are in skeleton or tested stage |
| Counterexample discovery | PASS | Graph similarity strict reflexivity successfully falsified |
| Toolchain completeness | PASS | All 7 formal verification tools participated |
| Lean commitment | INCOMPLETE | Lean skeleton is far from the juris-calculus theorems |
| Self-awareness | PASS | CONJECTURE/EMPIRICAL_HYPOTHESIS/TESTED_PROPERTY labels correctly self-assigned |

Overall: The formal verification infrastructure is ready, but strict proof of core theorems remains at an early stage. The highest-value upgrade path is: advance the Lean skeleton to a genuine Galois connection, and extend the TLA+ skeleton to the full evaluator.
