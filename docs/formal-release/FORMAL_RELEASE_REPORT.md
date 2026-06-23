# Formal Core Release Report (DRAFT -- awaiting lake build completion)

## Release ID: formal-core-v1

## Current State

| Gate | Status |
|------|--------|
| juris-calculus tests | 224 passed, 38 skipped, 0 errors |
| Theorem manifest | 75 theorems (43 core + 32 supporting) |
| Lean source scan | 0 sorry, 0 admit, 0 axiom, 0 True theorem |
| Lake build | IN PROGRESS (1621 .olean, JurisLean pending) |
| #print axioms audit | PENDING (requires lake build) |
| Clean clone verification | PENDING (requires lake build) |

## Completed Tracks

### Track A (Formal Core)
- A0-1: juris-calculus test fix (224/38/0, commit 15d9be6)
- A0-2: Theorem manifest with SHA256 digests (commit ad69df6)
- A0-3/A0-4: PENDING lake build

### Track B (Banach)
- B0: Build environment assessment + scaling isomorphism route (commit 30a3adf)

### Track C (Production Assurance)
- C0: CompletionStatus + StageResult + no_uncertainty_upgrade (commits 841cfef + ad69df6)
- C1: Independent certificate checker (Horn/IN/OUT/UNDEC) (commit 15d9be6)
- C2/C3: Horn-AAF argument/attack preservation MVM spec (commit 7a4bbeb)

### Track D (Dynamic Maintenance)
- D0-D3: Provenance dependency graph + incremental Grounded MVM spec (commit 3768901)

### Track E (Litigation Optimization)
- E0/E2: Minimal support set + minimum-cost intervention MVM spec (commit f43e273)

## Approvals Required for formal-core-v1

1. lake build completes with 0 errors
2. #print axioms audit for 6 key theorems: exists_fixpoint_le_card, fixed_at_card, grounded_is_least_fixed_point, horn_completeness, horn_result_is_minimal_model, sup_eq_zero
3. Clean clone verify: lake clean + lake build + rg scan
4. Commit tag: formal-core-v1

## Allowed Claims

- 75 Lean theorems (43 core + 32 supporting) have been formalized
- FiniteMonotoneIteration, AAF Grounded Extension, and Horn closure are proven in Lean
- juris-calculus passes 224 functional tests with 0 collection errors
- Independent certificate checker (Horn/IN/OUT/UNDEC) does not call main evaluator

## Forbidden Claims

- The entire juris-calculus has been formally verified correct by Lean
- Python implementation has been fully refinement-proved by Lean
- Horn->AAF compiler is sound and complete for all attack types
- Banach fixed-point is fully closed
- SPC OCR rules are legally correct (they only pass convergence tests)
- Differential privacy guarantees are established
- 38 constants are empirically calibrated

## Repository Map

| Repo | Branch | Final Commit |
|------|--------|-------------|
| legal-math-modeling | master | 1ae9a6d |
| juris-calculus | main | 15d9be6 |
| legal-math-modeling | track-b-banach | 30a3adf |
| legal-math-modeling | track-c-prod | f43e273 |
| deli-autoresearch | main | c759474 |
