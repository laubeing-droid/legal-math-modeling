# Formal Core Release Report

## Release ID

`formal-core-v1`

## Public State

| Item | State |
| --- | --- |
| Public branch model | `master` only |
| Repository head | `2368c33` |
| Last full clean rebuild evidence | `2368c33` |
| GitHub Actions clean build | PASS at `2368c33` |
| Local `lake build` evidence | PASS |
| Local `lake build +JurisLean.AxiomAudit` evidence | PASS |
| Lean source guard | PASS |

Lean source guard means:

- `0 sorry`
- `0 admit`
- `0 custom axiom`
- `0 theorem : True`

## Counting Policy

- `formal_core_module_theorems = 39`
- `extended_core_theorems = 43`
- `supporting_results = 32`
- `total_kernel_checked_results = 75`

Interpretation:

- `39` is the public count for the released finite monotone core, Dung grounded
  fixed-point layer, and finite Horn closure layer.
- `43` extends that count with additional checked weighted-metric and
  contraction-bridge results that are tracked in the manifest.
- `75` is the machine-readable repository-wide checked-result count in the
  manifest.

Canonical machine-readable source:

- [`theorem_manifest.json`](theorem_manifest.json)

## Release Boundary

Released:

- finite monotone iteration kernel
- Dung grounded fixed-point layer
- finite Horn closure layer
- reproducible `AxiomAudit`
- repository-level release gate closure for `formal-core-v1`

Not released:

- full Banach fixed-point closure
- full Lean proof of the `juris-calculus` Python runtime
- empirical calibration
- privacy guarantees
- litigation automation

## Axiom Audit Boundary

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

No project-defined axioms are part of the released core boundary.

Audit artifact:

- [`axiom_audit.txt`](axiom_audit.txt)

## Banach Status

Banach is not part of `formal-core-v1`.

Current public status:

- `UNPROVED_TRACK_B`

Historical side-track references are preserved as archive tags:

- `archive/banach-track-b-d23e8f2`
- `archive/track-c-prod-f43e273`

These tags are archival only. They are not active release branches and they do
not expand the public release claim.

## Allowed Claims

- The finite monotone iteration kernel, Dung grounded fixed-point layer, and
  finite Horn closure layer are repository-level released formal artifacts.
- The core release boundary has reproducible Lean build evidence and reproducible
  axiom-audit evidence.
- Banach remains outside the released formal core.

## Forbidden Claims

- “The whole `juris-calculus` Python implementation is formally proved by Lean.”
- “Banach fixed-point closure is complete.”
- “Formal-core-v1 includes the Banach track.”
- “Privacy guarantees have already been established.”
- “Empirical calibration is complete.”

See also:

- [`FORBIDDEN_CLAIMS.md`](FORBIDDEN_CLAIMS.md)

## Cross-Repo Reference Heads

| Repo | Branch | Head |
| --- | --- | --- |
| `legal-math-modeling` | `master` | `cde13f0` |
| `juris-calculus` | `main` | `c18b478` |
| `deli-autoresearch` | `main` | `b35dbb1` |
