# Task Plan: Complete the 2026-08-10 Necessary Supplement Plan

## Goal

Implement and verify every unconditional construction item in
`260810_legal-math-modeling必要补充施工方案.md`; close conditional items only when
their stated consumer prerequisites are evidenced. Preserve fail-closed semantics,
produce commit- and digest-bound artifacts, and create local checkpoint commits.

## Success Criteria

- Formal release tooling, schema, generated inventory, raw gates, and independent verifier pass.
- Certificate/checker v2 rejects every required mutation; v1 cannot obtain v2 decisive status.
- Horn-to-AAF witness rejects omission, spurious-edge, and reversed-priority mutations.
- Runtime refinement uses an externally supplied actual receipt; no same-process shadow status.
- Temporal and exact-numeric contracts are implemented only if a current consumer trigger exists;
  otherwise they remain explicitly `DEFERRED` and are not wired into a formal path.
- Full Python and Lean acceptance sequence passes from clean state.
- Claims, ledger, release evidence, repository memory, and local commits match verified facts.

## Phases

| Phase | Scope | Verification | Status |
|---|---|---|---|
| 1 | Baseline, boundaries, current-state inventory, test design | clean/read-only evidence snapshot; consumer-trigger decision | complete |
| 2 | L-A formal release certificate and ledger/audit repair | generator + clean build + full tests + guard + axiom + independent verifier | in_progress |
| 3 | L-B checker v2 | Lean build; Python mutation suite; v1 compatibility boundary | implementation_complete_ci_pending |
| 4 | L-C translation witness and L-D real runtime receipt | independent mutation checks; externally supplied receipt validation | verifier_complete_external_receipt_pending |
| 5 | Conditional L-E, full review, documentation, memory, commits | complete acceptance order; digest/commit binding; claim audit | pending |

## Scope Decisions

- Do not modify proven core modules absent a counterexample or build failure.
- Do not touch lock files or environment files.
- Do not publish, tag, force-push, or create a remote release.
- Run all remaining Lean compilation only in GitHub Actions; do not resume local Lake/Lean work.
- Keep generated build logs out of Git unless the plan explicitly requires a durable source artifact.
- Treat the supplied construction plan as user-owned input and include it only if the user-authored
  document is intentionally accepted into the repository during final scope review.

## Errors Encountered

| Error | Attempt | Resolution |
|---|---:|---|
| Goal creation rejected because this task already had an active goal | 1 | Queried the active goal and continued it; did not retry creation |
| Required project-root `memory` file absent | 1 | Record absence; create/update repository memory only after verified new knowledge exists |
| `elan`, `lake`, and `lean` not found on current `PATH` | 1 | Locate the pinned toolchain under user/machine paths before treating Lean as unavailable |
| `python -m pytest` failed: active Python 3.12.10 has no pytest module | 1 | Inspect the working `pytest` shim/interpreter and use one interpreter consistently |
| Planning-file patch context mismatch | 1 | Read exact file tails and reapplied a narrower patch |
| Phase 1 checkpoint commit failed because Git identity was unset | 1 | Reuse the repository's latest author identity in local-only Git config, restage plan log, and retry |
| Combined replacement patch targeted the same paths twice | 1 | Split delete/add replacements into separate atomic patches |
| First `lake env lean JurisLean/AxiomAudit.lean` failed with unknown `JurisLean` module | 1 | Dependencies were fetched but local library objects did not exist; run `lake build` before the audit |
| Initial v2 tests failed because `asdict` preserved tuples while checker/test mutations require JSON arrays | 1 | Make `envelope_to_dict` perform a JSON round trip; keep immutable tuples inside the dataclass only |
| Local Lean source build and Mathlib cache download consumed unacceptable machine resources | 2 | User directed an immediate switch to CI; both local processes were interrupted and no Lean process remains |
| GitHub CLI initially reported invalid auth and a refused proxy | 1 | Override stale process proxy `127.0.0.1:20808` with project proxy `127.0.0.1:10808`; auth and remote access then passed |
| Guard scanner was first invoked without its required Lean-root argument | 1 | Reran with `proofs/lean/juris_lean/JurisLean`; scan passed |
| First CI run failed source inventory before Lean | 1 | Root cause was CRLF working-tree bytes versus LF Git blobs; introduced the explicit `utf-8-lf-v1` hash contract and regenerated inventories |

## Current Decision Point

Phase 1 is closed. L3/L4 remain `DEFERRED` because no real consumer trigger exists. L0-L2 and the
L5 independent receipt verifier are implemented locally; Python collection/full tests, guard scan,
and generated inventory pass. Lean compilation, axiom audit, release certificate generation, and
independent certificate verification are now CI-only. L5 remains fail-closed until the external
runtime supplies an actual receipt through its formal entrypoint.
