# External backport: `JurisLean/External/NeuralNetworkProofs/` — provenance and license

This directory holds a **cross-pin backport** of the Leshno universal-approximation
line from https://github.com/davorrunje/neural-network-proofs (Apache-2.0) at
revision `f90942517be8b66dd34574212ada69b2130a48e5`, brought in by the owner's
2026-09-28 routing decision for proof-level gap ③ (the ReLU universal-approximation
family conclusion).

| item | fact |
|---|---|
| upstream pin | Lean `v4.32.0-rc1`, mathlib `v4.32.0-rc1` |
| this repository's pin | Lean `v4.30.0`, mathlib `c5ea00351c28e24afc9f0f84379aa41082b1188f` |
| same-pin revision exists? | **No** — the repository was scaffolded on v4.32.0-rc1 (first commit 2026-06-25); this is why the port is a *backport*, not a byte-faithful copy |
| import-path surface | all 29 Mathlib modules the cone imports exist at identical paths in our pinned mathlib (checked file-by-file before writing) |
| declaration-level drift | expected; repaired edit by edit, **every edit logged** per file in `PROVENANCE.json` (`adaptations`) |

## Target

`UniversalApproximation.Leshno.leshno_dense_iff` — an `M`-class activation densely
approximates iff it is not almost everywhere a polynomial (Leshno, Lin, Pinkus,
Schocken, *Neural Networks* 6 (1993) 861–867). The instantiation to ReLU (ReLU is
in class M; ReLU is not a.e. a polynomial) is deliberately **not** part of this
port: it will be a separate repository module citing the carrier theorem, once
the carrier itself compiles green.

## What was changed at landing

Each file differs from upstream in exactly two ways: the backport header
(`NEURAL-BACKPORT-PROVENANCE-V1`) and the `import` roots rewritten
(`NeuralNetworkProofs.*` → `JurisLean.External.NeuralNetworkProofs.*`). From
there, drift repairs are appended as they happen, and `tests/spec/
test_neural_backport_provenance.py` checks that the record's `adapted` flag
always equals the reconstruct-and-compare reality, with a non-empty adaptation
log for every drifted file.

No build attestation is claimed: every module here is quarantined in
`PENDING_CI_MODULES` until a CI run whose subject contains these files builds
green.

## License

Upstream is Apache-2.0 ("Copyright (c) 2026 Davor Runje. All rights reserved."),
with a per-file header saying so and the full text in the upstream `LICENSE`,
a copy of which sits beside this file. The machine-readable record is
`PROVENANCE.json` (schema `neural-backport-provenance-v1`).
