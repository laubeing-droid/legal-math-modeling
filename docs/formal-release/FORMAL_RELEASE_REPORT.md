# Formal Core Release Report

## Release ID: formal-core-v1

## Current State

| Gate | Status |
|------|--------|
| GitHub Actions clean build | PASS (`4b415b8`, Lake Build + Scan) |
| Local `lake build` | PASS (`2954 jobs`) |
| Local `lake build +JurisLean.AxiomAudit` | PASS |
| Lean source scan | PASS (`0 sorry`, `0 admit`, `0 custom axiom`, `0 theorem : True`) |
| theorem manifest | PASS (`75` checked results with statement digests) |
| #print axioms audit | PASS (`propext`, `Classical.choice`, `Quot.sound` only) |

## Counting Policy

- `formal_core_module_theorems = 39`
  FiniteMonotoneIteration + DungFixedPoint + HornDefinitions + HornFixedPoint
- `extended_core_theorems = 43`
  Adds the checked weighted-metric and contraction bridge theorems
- `supporting_results = 32`
- `total_kernel_checked_results = 75`

The machine-readable source of truth is:
- [theorem_manifest.json](/abs/path/D:/Claude/数学证明/legal-math-modeling/docs/formal-release/theorem_manifest.json)

## Axiom Audit

Audited theorems:

1. `FiniteMonotoneSystem.exists_fixpoint_le_card`
2. `FiniteMonotoneSystem.fixed_at_card`
3. `DungAAF.grounded_is_least_fixed_point`
4. `HornSystem.horn_completeness`
5. `HornSystem.horn_result_is_minimal_model`
6. `weightedSupDist_complete`

Observed dependencies:

- `propext`
- `Classical.choice`
- `Quot.sound`

No project-defined axioms were introduced.

See:
- [axiom_audit.txt](/abs/path/D:/Claude/数学证明/legal-math-modeling/docs/formal-release/axiom_audit.txt)

## Release Boundary

Allowed release claim:

- The finite monotone core, Dung grounded fixed-point layer, and finite Horn closure layer have reproducible Lean builds and reproducible axiom audit results.
- The repository-level formal release gate is closed for `formal-core-v1`.

Not allowed:

- Claiming that the whole `juris-calculus` Python implementation is formally proved by Lean
- Claiming that Banach fixed-point closure is complete
- Claiming that empirical calibration, privacy guarantees, or litigation automation are complete

## Repository Map

| Repo | Branch | Commit |
|------|--------|--------|
| legal-math-modeling | master | `4b415b8` |
| juris-calculus | main | `15d9be6` |
| deli-autoresearch | main | `e16e95a` |
