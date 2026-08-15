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
| 2 | L-A formal release certificate and ledger/audit repair | generator + clean build + full tests + guard + axiom + independent verifier | complete |
| 3 | L-B checker v2 | Lean build; Python mutation suite; v1 compatibility boundary | complete |
| 4 | L-C translation witness and L-D real runtime receipt | independent mutation checks; externally supplied receipt validation | runtime_receipt_in_progress |
| 5 | Conditional L-E, full review, documentation, memory, commits | complete acceptance order; digest/commit binding; claim audit | pending_final_closeout |

## Scope Decisions

- Do not modify proven core modules absent a counterexample or build failure.
- Do not touch lock files or environment files.
- Do not publish, tag, force-push, or create a remote release.
- Run all remaining Lean compilation only in GitHub Actions; do not resume local Lake/Lean work.
- Keep generated build logs out of Git unless the plan explicitly requires a durable source artifact.
- Treat the supplied construction plan as user-owned input and include it only if the user-authored
  document is intentionally accepted into the repository during final scope review.
- Keep sibling `juris-calculus` changes on a dedicated local branch and commit only task-owned files.
  Its repository rules prohibit push without current-turn authorization, so LMM must not claim the
  runtime commit is remotely published unless that authorization is later given.

## Errors Encountered

| Error | Attempt | Resolution |
|---|---:|---|
| Goal creation rejected because this task already had an active goal | 1 | Queried the active goal and continued it; did not retry creation |
| Required project-root `memory` file absent | 1 | Record absence; create/update repository memory only after verified new knowledge exists |
| `elan`, `lake`, and `lean` not found on current `PATH` | 1 | Locate the pinned toolchain under user/machine paths before treating Lean as unavailable |
| `python -m pytest` failed: active Python 3.12.10 has no pytest module | 1 | Inspect the working `pytest` shim/interpreter and use one interpreter consistently |
| Planning-file patch context mismatch | 1 | Read exact file tails and reapplied a narrower patch |
| Phase 1 checkpoint commit failed because Git identity was unset | 1 | Reuse the repository's latest author identity in local-only Git config, restage plan log, and retry |
| Combined replacement patch targeted the same paths twice | 2 | Split delete/add replacements into separate atomic patches; do not retry the combined form |
| First `lake env lean JurisLean/AxiomAudit.lean` failed with unknown `JurisLean` module | 1 | Dependencies were fetched but local library objects did not exist; run `lake build` before the audit |
| Initial v2 tests failed because `asdict` preserved tuples while checker/test mutations require JSON arrays | 1 | Make `envelope_to_dict` perform a JSON round trip; keep immutable tuples inside the dataclass only |
| Local Lean source build and Mathlib cache download consumed unacceptable machine resources | 2 | User directed an immediate switch to CI; both local processes were interrupted and no Lean process remains |
| GitHub CLI initially reported invalid auth and a refused proxy | 1 | Override stale process proxy `127.0.0.1:20808` with project proxy `127.0.0.1:10808`; auth and remote access then passed |
| Guard scanner was first invoked without its required Lean-root argument | 1 | Reran with `proofs/lean/juris_lean/JurisLean`; scan passed |
| First CI run failed source inventory before Lean | 1 | Root cause was CRLF working-tree bytes versus LF Git blobs; introduced the explicit `utf-8-lf-v1` hash contract and regenerated inventories |
| Second CI run failed `CertificateChecker.lean` after 2965/2969 targets | 1 | Replace heartbeat-heavy simplification with a direct Bool case split; explicitly right-associate content prerequisites so theorem projections match |
| Independent verifier flagged `UNKNOWN_*` mutation test names as UNKNOWN outcomes | 1 | Match fail-closed markers only as complete tokens and add a regression test distinguishing identifiers from outcome values |
| Third CI preflight reported unknown `JurisLean` module prefix | 1 | Direct Lean cannot import unbuilt project objects; use `lake build JurisLean.<Module>` targets so Lake builds dependencies first |
| Fourth through seventh CI preflights exposed proof-body/instance/syntax errors | 4 | Fixed the exact Boolean branch proof, explicit `Decidable` instance, and closed backend discriminator without weakening statements |
| Eighth CI passed 2969/2969 but AxiomAudit lacked `HornFixedPoint.olean` | 1 | Default root build was not full inventory coverage; derive explicit Lake targets for the root and all 33 inventory modules |
| Strict inventory build initially failed two stale scratch modules | 2 | Migrated API probes to pinned Mathlib 4.30.0 declarations; no proven core module changed |
| Clean gate discarded the restored Mathlib cache and caused 50-minute dependency rebuilds | 1 | Added a recorded post-clean `mathlib_cache_restore` gate; clean project compilation now completes in minutes |
| Session catch-up rendered Chinese context as mojibake | 1 | Treat planning files and current Git state as authoritative; do not reconstruct facts from the damaged console rendering |
| Planned legacy fixture path `runtime/legal_math_four_slice_differential.json` is absent | 1 | Locate the implemented expected-only fixture and update the final plan status to its authoritative path; do not invent the legacy file |
| Targeted search included nonexistent top-level `cli.py` and `jc.py` paths | 1 | Use the discovered authority path `compiler_core/cli.py`; do not repeat the stale path assumptions |
| Receipt-v2 red test reported 6 failures | 1 | Implemented v2 embedded semantic validation; the same target now passes 11/11 |
| JC producer red test cannot import `compiler_core.runtime_refinement` | 1 | Implemented the producer through audit verify/replay only; target now passes 6/6 |
| Fixture manifest digest command had an unterminated quoted Python expression | 1 | Use a PowerShell single-quoted `python -c` program with Python double-quoted literals |
| First fixed-fixture run lacked strict checker config files | 1 | Added minimal fixture-owned `core_ontology.yaml` and `L0_overrides_hk.yaml`, bound both hashes in the synthetic pack manifest |
| Ten-case all-aligned assertion failed on 3 canonical JC results | 1 | Preserve LMM expected statuses; freeze actual runtime outputs and require LMM to report a valid receipt with `RESULT_MISMATCH` |

## Current Decision Point

Phases 1-3 and the L-C part of phase 4 are closed. L3/L4 remain `DEFERRED` because no real consumer
trigger exists. Final-head GitHub Actions run `31850513493` produced and independently verified a
FormalReleaseCertificate for PR merge subject `dbc44415c2d763f1575c51482ad90eb2a69e1106`:
33 Lean files, 141 theorem declarations, 8509/8509 strict build jobs, eight gates PASS. The remaining
work is L5: make the external runtime formal entrypoint produce an actual, content-bound receipt,
then validate it independently in LMM before the final claim/document/memory close-out.
