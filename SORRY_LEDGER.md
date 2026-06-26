# SORRY_LEDGER.md — legal-math-modeling

> Track all `sorry` usage in Lean proofs.
>
> **Rule 1**: Every `sorry` must have a ledger entry before CI passes.
> **Rule 2**: Blocking-path theorems SHALL NOT use `sorry`.
> **Rule 3**: CI rejects blocking-path sorrys outright. Non-blocking sorrys must have a ledger entry before CI passes.

## Blocking-Path Theorems (ZERO sorry tolerance)

| # | Theorem | SPEC |
|---|---------|------|
| 1 | hornClosure_converges | 210 |
| 2 | hornStep_monotone | 210 |
| 3 | hornClosure_extensive | 210 |
| 4 | hornClosure_closed | 210 |
| 5 | hornClosure_idempotent | 210 |
| 6 | compiler_correctness | 230 |
| 7 | compileAttacks_exact | 230 |
| 8 | attack_compilation_exact | 240 |
| 9 | grounded_ext_is_complete | 240 |
| 10 | grounded_decision_matches_formal | 240 |
| 11 | decisionProjection_grounds | 240 |
| 12 | decisionProjection_completeness | 240 |
| 13 | checker_sound | 250 |
| 14 | certificate_verifies | 250 |
| 15 | safety_preservation | 270 |
| 16 | safety_no_violation | 270 |
| 17 | end_to_end_soundness | 280 |
| 18 | end_to_end_certificate | 280 |

## Non-Blocking Sorry Entries

| theorem_name | SPEC | reason | closing_task | status |
|---|---|---|---|---|

*No entries yet.*
