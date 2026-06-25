# Legal Math Modeling

Mathematical companion repository for
[`juris-calculus`](https://github.com/laubeing-droid/juris-calculus).

This repository no longer presents itself as a grab-bag of partially related
legal-AI experiments. Its public boundary is now explicit:

- `formal-core-v1` is released at the repository level.
- The released formal core is the finite monotone iteration kernel, Dung
  grounded fixed-point layer, and finite Horn closure layer.
- Banach remains outside the released core as an archived, unfinished research
  track.
- Empirical calibration, privacy guarantees, and litigation automation are not
  claimed complete here.

## Current Status

### Released

- Repository branch model: `master` only
- Repository head: `cde13f0`
- Last full GitHub clean rebuild evidence: `4b415b8`
- Lean source guard:
  `0 sorry / 0 admit / 0 custom axiom / 0 theorem : True`
- Reproducible `AxiomAudit` for the core release boundary

### Canonical Release Claim

The finite monotone core, Dung grounded fixed-point layer, and finite Horn
closure layer have reproducible Lean builds and reproducible axiom-audit
results. The repository-level formal release gate is closed for
`formal-core-v1`.

### Not Released

- Full Banach fixed-point closure
- Full proof of the `juris-calculus` Python implementation
- Privacy guarantees
- Real-data calibration of constants
- End-to-end litigation automation

## Repository Boundary

This repository is for:

- formal specifications,
- Lean proof artifacts,
- proof ledgers and theorem manifests,
- modeling papers and audit history,
- machine-checkable release evidence.

This repository is not the production runtime. Runtime behavior lives in:

- [`juris-calculus`](https://github.com/laubeing-droid/juris-calculus)
- [`deli-autoresearch`](https://github.com/laubeing-droid/deli-autoresearch)

Current cross-repo heads referenced by the release docs:

| Repo | Branch | Head |
| --- | --- | --- |
| `legal-math-modeling` | `master` | `cde13f0` |
| `juris-calculus` | `main` | `c18b478` |
| `deli-autoresearch` | `main` | `b35dbb1` |

## Released Formal Core

The released core is split into three layers:

1. Finite monotone iteration kernel
2. Dung grounded fixed-point layer
3. Finite Horn closure layer

The current machine-readable count policy is:

- `formal_core_module_theorems = 39`
- `extended_core_theorems = 43`
- `supporting_results = 32`
- `total_kernel_checked_results = 75`

The canonical source for these counts is
[`docs/formal-release/theorem_manifest.json`](docs/formal-release/theorem_manifest.json).

## Axiom Boundary

The audited core theorems are:

1. `FiniteMonotoneSystem.exists_fixpoint_le_card`
2. `FiniteMonotoneSystem.fixed_at_card`
3. `DungAAF.grounded_is_least_fixed_point`
4. `HornSystem.horn_completeness`
5. `HornSystem.horn_result_is_minimal_model`
6. `weightedSupDist_complete`

Observed dependencies in the audit:

- `propext`
- `Classical.choice`
- `Quot.sound`

No project-defined axioms are part of the released core boundary.

## Banach Status

Banach is not part of `formal-core-v1`.

What is true:

- Banach-related exploratory work was archived.
- The public repo keeps the archive as tags, not active branches.
- The current public position is `UNPROVED_TRACK_B`.

What is not true:

- Banach closure is complete
- Weighted contraction is fully closed in Lean
- Banach is part of the released formal core

Archived tag references:

- `archive/banach-track-b-d23e8f2`
- `archive/track-c-prod-f43e273`

## Repository Layout

```text
legal-math-modeling/
├── README.md
├── README_CN.md
├── paper/
├── theory/
├── proofs/
│   ├── engineering_proof_artifacts/
│   ├── strict_proof_baseline/
│   └── lean/juris_lean/
├── verification/
├── data/
└── docs/
    ├── formal-release/
    ├── final-closure/
    ├── audit/
    ├── modeling/
    └── history/
```

Key directories:

- `proofs/lean/juris_lean/`: Lean formalization workspace
- `docs/formal-release/`: canonical release-boundary documents
- `docs/final-closure/`: closure and audit summary
- `docs/audit/`: theorem matrix, proof ledger, counterexample registry
- `docs/history/`: archival notes about earlier phases and superseded claims

## Read This First

For current truth, read in this order:

1. [`docs/formal-release/FORMAL_RELEASE_REPORT.md`](docs/formal-release/FORMAL_RELEASE_REPORT.md)
2. [`docs/formal-release/FORBIDDEN_CLAIMS.md`](docs/formal-release/FORBIDDEN_CLAIMS.md)
3. [`docs/final-closure/final-report.md`](docs/final-closure/final-report.md)
4. [`docs/audit/theorem_status_matrix.md`](docs/audit/theorem_status_matrix.md)

`docs/history/` is archival. Some historical files summarize earlier states and
may describe counts or ambitions that are no longer the current release claim.

## Quick Start

```bash
git clone https://github.com/laubeing-droid/legal-math-modeling.git
cd legal-math-modeling
pip install -r requirements.txt
python verification/verification_engine.py
cd proofs/lean/juris_lean && lake build
```

For the formal release boundary specifically:

```bash
cd proofs/lean/juris_lean
lake build
lake build +JurisLean.AxiomAudit
```

## Documentation Map

- `paper/main.md`: main mathematical paper
- `docs/formal-release/`: current release boundary and allowed claims
- `docs/audit/`: audit trail and theorem ledger
- `docs/history/`: archival summaries of earlier development phases

## License

[CC BY 4.0](LICENSE)
