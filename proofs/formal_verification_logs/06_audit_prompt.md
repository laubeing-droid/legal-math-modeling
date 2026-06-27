# juris-calculus Mathematical Proof Logic Audit Prompt

Audit the mathematical proof logic of juris-calculus. The focus is not whether the code runs, but whether each mathematical theorem has genuinely been proved, or whether it is merely a test, model sketch, empirical hypothesis, or already-refuted claim.

## Background

Project directory:

```text
D:\Codex\juris-calculus\源码
```

Experiment record directory:

```text
D:\juris_calculus_verification_runs
```

Latest experiment summary report:

```text
D:\juris_calculus_full_verification_run_report.md
```

Latest run directory:

```text
D:\juris_calculus_verification_runs\07_report\runs\20260609-214205-full-suite-all-verification
```

Completed verification toolchain:

- Python / Hypothesis
- Z3
- CrossHair
- TLA+
- Alloy
- Lean
- Dafny

## Known Experiment Results Summary

1. Python/Hypothesis property tests passed: 6 passed.
2. Z3 proved graph similarity abstract range does not exceed bounds:
   - `sim < 0`: unsat
   - `sim > 1`: unsat
3. Finite Galois sanity check: 0 violations.
4. CrossHair returned `Not confirmed` for graph similarity contract; this is not proof.
5. TLA+ oscillation guard skeleton: No error found.
6. Alloy relation disjoint skeleton: UNSAT.
7. Lean Galois skeleton: compiled successfully, but only an identity skeleton -- not the full juris-calculus theorem.
8. Dafny graph range model: 1 verified, 0 errors.
9. Project unit tests: 32 passed.
10. Project full pytest fails at collection due to missing `configs/en_US/rules.yaml`; this issue is not addressed here.

## Key Counterexample

The strict reflexivity of `compute_graph_similarity()` has been refuted:

```text
G = (v=1, e=0, features=empty set)
sim(G, G) = 0.4
```

Therefore the global claim `sim(G, G) = 1` cannot stand.

Focus your analysis: Is this an implementation bug, or a theorem demotion caused by the conservative empty-feature semantic?

## Audit Objective

Perform a graded audit of the entire mathematical proof logic.

Do not simply say "pass" or "fail." Assign a label to every theorem/proof claim:

| Label | Definition |
| --- | --- |
| `CODE_FACT` | Source code fact only |
| `TESTED_PROPERTY` | Test passed, but not proof |
| `SMT_PROVED_FINITE` | SMT proof in finite or abstract domain |
| `MODEL_CHECKED` | TLA+/Alloy bounded model check |
| `LEAN_PROVED_SKELETON` | Lean skeleton compiles, but not a complete proof |
| `LEAN_PROVED` | Lean proof complete with no sorry |
| `EMPIRICAL_HYPOTHESIS` | Empirical hypothesis |
| `CONJECTURE` | Not yet proved |
| `REFUTED` | Counterexample exists |
| `INCONCLUSIVE` | Tool cannot confirm |

## Audit Sections

### 1. Galois Connection

Check:

- Is the current finite sanity check sufficient?
- Is the Lean identity skeleton too weak?
- What definitions are still missing for a genuine alpha/gamma adjunction?
- Is vacuous truth masking a missing reverse proof?

### 2. Fixpoint Convergence

Check:

- Can Tarski's theorem be directly applied to the evaluator?
- Do `rules_applied`, `max_iterations`, exception recursion, and critical halt break monotonicity?
- Does the TLA+ skeleton only prove the guard model, not the full evaluator?

### 3. Graph Similarity

Check:

- Has the `[0,1]` range been sufficiently proved?
- Is symmetry merely tested or provable?
- Should strict reflexivity be demoted?
- Can it still be called a metric?
- How does the current counterexample affect the mathematical reports?

### 4. Non-Horn Formalizable Score

Check:

- Does sigmoid smoothing improve the hard truncation?
- Is this currently just a passing test, or is there mathematical proof?
- Are the weights `(0.2, 0.2, 0.4, 0.2)` still empirical parameters?

### 5. DP Ratio-Preserving Mechanism

Check:

- `dp_diagnostics` is audit instrumentation only; it is not a DP proof.
- Can the current mechanism claim tuple-level differential privacy?
- Do adjacency, sensitivity, floor clipping, and rounding all need restatement?

### 6. Constraint Guard / Oscillation Guard

Check:

- What does the TLA+ skeleton actually prove?
- Is it sufficient to guarantee the real `ConstraintValidator` will not oscillate?
- What state variables are still missing?

### 7. Category / Banach / Abstract Interpretation

Check:

- Which claims are merely mathematical metaphors?
- Which can enter Lean?
- Which should be demoted to conjecture?
- Can Banach contraction be refuted by counterexample?

### 8. Core Inference Safety Boundary

Audit the core inference safety boundary from the perspective of "will the legal reasoning machine run away."

Focus on:

- Does the fixpoint always terminate?
- Which parts of rule firing are monotone and which are not?
- Does exception recursion have visited/depth protection?
- Are confidence and formalizable_score always within `[0,1]`?
- Which graph similarity properties hold and which have been refuted by counterexample?
- Does the DP mechanism protect principal, tuple, or only provide audit instrumentation?

Output a table:

| Safety Boundary | Current Evidence | Risk | Recommended Label | Next Proof Method |
| --- | --- | --- | --- | --- |

### 9. Practical Legal Application Interface

Audit the practical interface from the perspective of "how to honestly output when processing real case files."

Focus on:

- Which rules can be labeled as proved?
- Which are merely testable properties?
- Which are empirical parameters?
- Which need real-case calibration?
- Which propositions have been refuted by counterexample?
- How should trust labels be attached to system legal conclusions?
- Is a rule maturity classification needed?
- Should `US_Adapter.yaml` be treated as a terminology layer only, not a rule layer?

Output a table:

| Output Object | Current Maturity | Recommended Trust Label | Requires Manual Review | Reason |
| --- | --- | --- | --- | --- |

## Output Format

Output in the following structure:

```markdown
# juris-calculus Mathematical Proof Logic Audit Report

## 1. Overall Conclusion

## 2. Trust Label Summary Table

| Theorem/Module | Current Evidence | Recommended Label | Can Be Called Proof | Reason |
| --- | --- | --- | --- | --- |

## 3. Proved or Partially Proved

## 4. Refuted by Counterexample

## 5. Tests Passed but Not Proof

## 6. Proof Skeletons Only

## 7. Still Conjecture / Empirical Hypothesis

## 8. Mathematical Model Correction Suggestions

## 9. Source Code Correction Suggestions

## 10. Future Lean/Z3/TLA+ Proof Route Suggestions

## 11. Core Inference Safety Boundary Audit

## 12. Future Practical Application Interface Audit

## 13. Final Ratings
```

## Audit Principles

1. Do not treat print output or docstrings as proof.
2. Do not treat single-case tests as universal theorems.
3. Do not treat Hypothesis passes as mathematical proof.
4. Do not treat Lean skeletons as complete Lean proofs.
5. Do not treat bounded Alloy/TLA+ checks as infinite-domain proofs.
6. When a counterexample is found, the original proposition must be explicitly demoted or refuted.
7. If a proposition has only engineering intuition and no proof artifact, label it `CONJECTURE` or `EMPIRICAL_HYPOTHESIS`.
8. If a conclusion holds only within an abstract model, write the model boundary explicitly.
