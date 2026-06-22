# S0: Final Closure Baseline

**Date**: 2026-06-23

## Repository State

| Repo | Commit | Status |
|------|--------|--------|
| deli-autoresearch | `7bed6a7` | 22/22 tests, dirty (8 modified, 6 untracked) |
| juris-calculus | `c77de79` | 54/54 tests, clean |
| legal-math-modeling | `85e395a` | Lean 0 errors, 3/13 AAF proved |

## Environment

- Python: 3.12.5
- Lean: 4.30.0 (commit d024af099ca4)
- Lake: 5.0.0-src+d024af0
- mathlib4: v4.30.0 (commit c5ea00351c)

## AAF Theorems (DungAAF.lean)

| # | Theorem | Status |
|---|---------|--------|
| 1 | F_monotone | PROVED |
| 2 | iteration_monotone | PROVED |
| 3 | finite_termination | sorry |
| 4 | iteration_bound | sorry |
| 5 | grounded_is_fixed_point | sorry |
| 6 | grounded_is_least_fixed_point | sorry |
| 7 | grounded_is_least_complete | sorry |
| 8 | grounded_unique | sorry |
| 9 | labelling_partition | sorry |
| 10 | in_soundness | sorry |
| 11 | out_soundness | PROVED |
| 12 | undecided_characterization | sorry |
| 13 | self_attack_undecided | sorry |

## Horn Theorems

No HornCompleteness.lean exists. Horn fixed-point theorems have not been formalized in Lean.

## Key Engineering State

- G8 Horn truncation: Fixed (evaluate_horn uses derived_bound)
- SCC-DAG: Fixed (iterative DFS, 8/8 tests)
- Golden corpus: 9 cases with trust labels
- Cross-repo bridge: Deli consumes v3.0 Grounded interface
- Certificate verifier: Independent AAF certificate checker exists