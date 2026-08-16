# SORRY ledger

The release guard rejects `sorry`, `admit`, custom `axiom` declarations, and
`theorem ... : True := ...` evasions in the Lean authority tree.

## Current Theorem Entries

| theorem_name | reason | status |
|---|---|---|
| _none_ | No current theorem uses a proof placeholder. | CLOSED |

The release inventory gate parses this table and rejects any named current entry
that does not exist in the generated theorem inventory. Historical placeholder
names from the pre-rewrite ledger were removed because they were never current
declarations in this source tree.

## Closed Domain Targets

| theorem_name | scope | status |
|---|---|---|
| `violation_implies_norm_active` | Four-slice minimal DDL model in `DDLDefinitions.lean`. | CLOSED_LEAN_PROVED |
| `permission_no_direct_violation` | Four-slice minimal DDL model in `DDLDefinitions.lean`. | CLOSED_LEAN_PROVED |
| `constitutive_no_direct_violation` | Four-slice minimal DDL model in `DDLDefinitions.lean`. | CLOSED_LEAN_PROVED |

These theorems do not prove the complete juris-calculus runtime.
