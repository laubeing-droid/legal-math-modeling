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

## Open Non-Blocking Sorry Entries

| theorem_name | SPEC | reason | closing_task | status |
|---|---|---|---|---|
| _none_ | _n/a_ | No open Lean `sorry` entries. | Keep `scripts/scan_lean_guards.py` and `lake build` green. | CLOSED |

## Closed Domain-Axiom Targets

| theorem_name | SPEC | closure | status |
|---|---|---|---|
| `violation_implies_norm_active` | 220 | Proved in `proofs/lean/juris_lean/JurisLean/DDLDefinitions.lean` for the four-slice minimal DDL model. | CLOSED_LEAN_PROVED |
| `permission_no_direct_violation` | 220 | Proved in `proofs/lean/juris_lean/JurisLean/DDLDefinitions.lean`; permission norms have no direct violation path in the minimal DDL model. | CLOSED_LEAN_PROVED |
| `constitutive_no_direct_violation` | 220 | Proved in `proofs/lean/juris_lean/JurisLean/DDLDefinitions.lean`; constitutive rules have no direct violation path in the minimal DDL model. | CLOSED_LEAN_PROVED |

These closures do not prove the full `juris-calculus` runtime. They only close
the formal four-slice DDL boundary required by the current Playbook.
