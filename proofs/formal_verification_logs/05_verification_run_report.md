# juris-calculus Full Formal Verification Run Report

Date: 2026-06-09
Run ID: `20260609-214205-full-suite-all-verification`
Run directory: `D:\juris_calculus_verification_runs\07_report\runs\20260609-214205-full-suite-all-verification`
Status: Complete experiment suite executed. Contains pass items, refuted items, inconclusive items, and project test fixture blockers.

## 1. Baseline and Environment

Latest baseline freeze, source directory snapshot, and dependency check completed.

Key artifacts:

- `D:\juris_calculus_verification_runs\00_baseline\source_tree_hashes.json`
- `D:\juris_calculus_verification_runs\00_baseline\source_snapshot.zip`
- `D:\juris_calculus_verification_runs\00_baseline\source_snapshot.sha256`
- `D:\juris_calculus_verification_runs\00_baseline\dependency_status.json`

## 2. Results Summary

| Category | Result | Trust Label | Evidence |
| --- | --- | --- | --- |
| Python/Hypothesis property tests | PASS, 6 passed | `TESTED_PROPERTY` | `01_property_tests/pytest_core_properties_final.log` |
| Graph similarity reflexive counterexample search | FOUND | `REFUTED` for blanket strict-reflexivity claim | `01_property_tests/counterexample_graph_reflexivity.json` |
| Z3 graph range | PASS, counterexample query `unsat` | `SMT_PROVED_FINITE` / abstract real domain | `02_smt_z3/z3_core_checks.log` |
| Z3 finite Galois sanity | PASS, 0 violations | `SMT_PROVED_FINITE` / finite enumeration | `02_smt_z3/z3_core_checks.log` |
| CrossHair graph contract | INCONCLUSIVE, Not confirmed | `INCONCLUSIVE` | `03_crosshair/crosshair_graph_similarity.log` |
| TLA+ oscillation guard skeleton | PASS, No error found | `MODEL_CHECKED` / bounded skeleton | `04_tla/tlc_oscillation_guard_final.log` |
| Alloy relation disjoint skeleton | PASS, UNSAT | `MODEL_CHECKED` / bounded Alloy scope | `05_alloy/alloy_relations.log` |
| Lean Galois skeleton | PASS, exit 0 | `LEAN_PROVED_SKELETON` | `06_lean/lean_galois_skeleton_final2.log` |
| Dafny graph range | PASS, 1 verified, 0 errors | `SMT_PROVED` for Dafny model | `08_dafny/dafny_graph_similarity_range_final.log` |
| Core py_compile | PASS | `BUILD_CHECK` | `09_project_regression/py_compile_core.log` |
| Project unit tests | PASS, 32 passed | `REGRESSION_PASS` | `09_project_regression/pytest_project_unit_tests.log` |
| Project full tests | FAIL at collection | `BLOCKED_BY_MISSING_FIXTURE` | Missing `configs/en_US/rules.yaml` |

## 3. Key Findings

### 3.1 Graph Similarity Strict Reflexivity Refuted

The current implementation uses conservative empty-feature semantics: `jaccard = 0.0`. Therefore:

```text
G = (v=1, e=0, features=empty set)
sim(G, G) = 0.4
```

This refutes any strong theorem claiming `sim(G,G)=1` for all graph inputs. It is not necessarily an implementation bug, since this is a deliberate conservative empty-feature semantic chosen after audit; but the report must not declare blanket strict reflexivity.

Counterexample: `01_property_tests/counterexample_graph_reflexivity.json`

### 3.2 CrossHair Inconclusive

CrossHair returned `Not confirmed` for the graph similarity contract. This is neither failure nor proof and must be recorded as `INCONCLUSIVE`.

### 3.3 Project Full pytest Blocked by Missing Configuration

Command:

```powershell
python -m pytest tests -q
```

Result: Collection phase fails with:

```text
FileNotFoundError: configs/en_US/rules.yaml
```

The unit test subset passes: `32 passed in 2.12s`.

## 4. Algorithm and Source Code Improvement Records

Algorithm improvement record directory:

`D:\juris_calculus_verification_runs\07_report\algorithm_improvements`

Source code improvement record directory:

`D:\juris_calculus_verification_runs\07_report\source_code_improvements`

This round did not modify the JC runtime source code. Experiment scripts wrote only into the run directory.

## 5. Record Validation

Record integrity validation:

`D:\juris_calculus_verification_runs\07_report\record_validation.json`

Current result is `[]`, indicating no structural record issues were found.

## 6. Next Steps

1. Provide or fix `configs/en_US/rules.yaml` to unblock project full pytest collection.
2. Write the "empty-feature reflexivity fails" finding into the theory theorem demotion notes for graph similarity.
3. Extend the Lean skeleton into a genuine finite preorder / powerset Galois connection proof.
4. Extend the TLA+ skeleton to the full evaluator state machine.
5. Re-test the CrossHair inconclusive item with simpler contracts or convert it to a Z3 proof.
