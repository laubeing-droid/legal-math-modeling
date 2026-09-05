# Lean Formal Verification

Lean is the kernel-checked specification layer of this repository. A successful elaboration proves the exact theorem statement under its declared definitions and reported assumptions. It does not prove that Python code, source data, a legal rule, or a concrete legal conclusion is correct.

## Project

The build project is `proofs/lean/juris_lean/`. Source modules live under `JurisLean/`; the toolchain and Mathlib dependency are pinned by `lean-toolchain` and `lake-manifest.json`.

The current source includes finite monotone iteration, Dung and Horn fixed points, DDL semantics, certificate/checker contracts, temporal and translation models, runtime-refinement interfaces, and ULM01–ULM16 composition. Do not maintain a hand-copied exhaustive module or theorem list here; the workflow generates it from the subject tree.

## Execution boundary

Lean, Elan, and Lake never run locally for this repository. Local work is limited to source editing, inventory, Git inspection, Python tests, and static guards. GitHub Actions performs:

- the generated source-module matrix;
- a clean full build with failure propagation;
- base, ULM all-theorem, and ULM core-composition axiom audits;
- release-certificate binding and final verification.

Trigger the workflow with:

```bash
gh workflow run lean-build.yml --ref <commit-or-branch> -f mode=full-release
```

The latest documented snapshot is [run 33946211096](../../docs/formal-release/FINAL_FORMAL_RELEASE_REPORT.md), bound to commit `2a1d33df353a005dffc5d8b95faa591524e2636e`. Later commits require new CI evidence.

## Assumptions and claims

The documented run reports only `propext`, `Classical.choice`, and `Quot.sound` across the audited ULM declarations. A missing target, unlisted theorem, `sorryAx`, absent raw log, or failed command blocks the release claim.

See [Axiom Audit Boundary](../../docs/formal-release/axiom_audit.md), [Allowed Claims](../../docs/formal-release/ALLOWED_CLAIMS.md), and [Forbidden Claims](../../docs/formal-release/FORBIDDEN_CLAIMS.md).
