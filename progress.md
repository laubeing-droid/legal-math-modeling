# Progress Log

## 2026-08-15

- Continued the already-active goal for the supplied construction plan.
- Loaded `planning-with-files` and `karpathy-guidelines` completely.
- Ran session catch-up; no prior planning state was present.
- Inspected Git baseline and read the construction plan in full.
- Confirmed absence of project-root memory and forbidden-expression files.
- Created persistent plan, findings, and progress files.
- Inventoried all files in the planned scope and searched for implementation symbols.
- Read the current Python certificate/Horn/runtime specifications, tests, Lean checker boundary,
  end-to-end examples, Horn/AAF contract, operational refinement note, and axiom audit.
- Began baseline toolchain and guard checks; recorded missing-PATH and Python environment errors.
- Located the working pytest interpreter, collected the complete baseline suite, and ran it.
- Audited L0 scripts, workflow, manifests, ledger, axiom document, and scoped specification docs.
- Searched current spec/runtime paths for temporal/numeric consumer triggers; none found.
- Located sibling runtime repositories and began current-entrypoint revalidation from a memory lead.
- Verified that JC has a formal audit-bundle CLI but its current LMM comparison remains a lower-level
  shadow harness, not an external actual-receipt producer.
- Confirmed the sibling repository is dirty; reserved it as read-only unless a non-overlapping,
  explicitly necessary integration artifact can be added safely.
- Searched `D:\Codex` for existing Lean executables; none found.
- Added pre-implementation tests for v2 certificate mutations, translation-witness edge mutations,
  runtime receipt binding/status failures, and generated Lean source inventory.
- Removed the old test that treated same-process shadow statuses as a green runtime differential.
- Ran collection to prove the new tests fail for the intended missing implementations.
- Phase 1 checkpoint commit was initially blocked because this checkout had no Git author identity;
  the latest repository author identity will be reused in repository-local config only.

## Tests and Commands

| Command | Result |
|---|---|
| `git status --short --branch` | `main` aligned with `origin/main`; construction plan untracked |
| `git log -5 --oneline --decorate` | HEAD `a3a0159` |
| planning session catch-up | no prior report/output |
| project rule-file search | only `AGENTS.md`; no memory or forbidden-expression file |
| planned-symbol search | v2/release/witness/temporal/numeric implementations absent |
| static theorem inventory | 126 declarations across current Lean source files |
| forbidden Lean token scans | no matches; command composite exited 1 due to expected `rg` no-match/tool lookup failures |
| `python -m pytest --collect-only -q` | failed: active Python has no pytest module |
| Hermes venv `python -m pytest --collect-only -q` | 12 tests collected |
| Hermes venv `python -m pytest -q -ra` | 12 passed in 0.22s |
| post-test-design collection | expected failure: 4 missing implementation imports; 11 legacy tests collected |

## Files Added

- `task_plan.md`
- `findings.md`
- `progress.md`
- `tests/spec/test_certificate_v2.py`
- `tests/spec/test_translation_witness.py`
- `tests/spec/test_runtime_refinement_receipt.py`
- `tests/test_formal_release_inventory.py`

## 2026-08-16

Theory-absorption construction started on branch `codex/lmm-theory-absorption-plan`
(HEAD `348e471`, baseline plan commit `f521b5b`).

- M0 baseline re-verified: worktree clean; local `.lake` artifacts stay git-ignored
  and are never used as evidence; Lean execution remains forbidden locally.
- Collection manifest: 4 red modules, all failing for missing implementations only
  (`certificate_schema` v2 API, `translation_witness`, `runtime_differential` receipt
  API, `scripts.generate_formal_release_certificate`); 11 legacy tests green.
- Implemented `theory/spec/translation_witness.py`: omission/spurious/direction
  checks bound to input witnesses and priority pairs.
- Extended `theory/spec/certificate_schema.py` with `CertificateEnvelopeV2` and an
  independent checker that recomputes digests, rejects v1 decisive status, empty
  trace, candidate evidence, duplicates, unstable sequences, and stale snapshots.
- Extended `theory/spec/runtime_differential.py` with expected-only fixtures and an
  external actual-receipt verifier (missing receipt, commit/digest mismatch,
  execution failure, unknown status mapping all fail-closed).
- Added `scripts/generate_formal_release_certificate.py` (source/theorem inventory
  plus fail-closed release assembler) and `scripts/verify_formal_release_certificate.py`
  (independent verifier, no shared implementation).
- Added root `conftest.py` so repo-root packages import under any CI invocation.
- Full local suite: 36 passed. Guard scan: passed. Both are provisional local
  results; CI on the subject commit is the release authority.
- Marked `260810_legal-math-modeling必要补充施工方案.md` as SUPERSEDED INPUT.
- Rewrote `task_plan.md` for the M0-M10 wave structure; added authority map under
  `docs/remediation/authority_map.md`; updated AGENTS.md Lean workflow to the
  CI-only authority convention.

| Command | Result |
|---|---|
| `git status` | branch `codex/lmm-theory-absorption-plan`, clean |
| `python -m pytest tests/ -q` (pre-implementation) | 11 passed, 4 collection errors |
| `python -m pytest tests/ -q` (post-implementation) | 36 passed |
| `python scripts/scan_lean_guards.py proofs/lean/juris_lean/JurisLean` | Lean guard scan passed (provisional) |

## 2026-08-16 (construction waves M1-M10)

- M1: FailureStatus, LegalIds, LegalModelV2, LegalWellFormed,
  CanonicalSerialization (Lean); canonical_v2 package with manifest and
  v1 migration loss reports (Python).
- M2: SourceBundleSpec, SourcePathSpec, TemporalApplicability (Lean);
  source_bundle/source_path/temporal_applicability references with
  tamper/broken-link/future-information mutations.
- M3: FactAdmissionSpec, TaintNoninterference, ReceiptAuthority (Lean);
  fact_admission/receipt_authority references; replay/revocation/laundering
  fail closed.
- M4: TypedAttack, DefeasiblePriority, PermissionConflict,
  ArgumentCompilerSpec, ArgumentSemanticsRegistry (Lean); grounded
  labelling oracle with cycle/self-attack fixtures.
- M5: ExactNumericContract, TemporalArithmetic, BackendContract,
  ASPWitness, SMTWitness, SolverRouting (Lean); exact numeric and backend
  routing references; UNKNOWN/TIMEOUT never decisive.
- M6: LegalSpec, LegalIVL, well-formedness, normalize, LegalSpecToIVL,
  IVLToHorn/AAF/ASP/SMT, TranslationWitness, TranslationRefinement (Lean);
  dual_ir pipeline producing checker-verified witnesses. Full-chain
  soundness and incremental-compilation obligations registered UNPROVED.
- M7: AuthorityLattice, ProposalEnvelopeSpec, HumanResearchReceiptSpec,
  ProposalNoninterference (Lean); proposal_envelope reference.
- M8: CertificateV2, CertificateCheckerV2 (Lean); checker acceptance
  implies recomputed well-formedness; v1 never decisive; boundary doc
  updated.
- M9: runtime/refinement_cases fixtures, receipt schema, materialize and
  independent verifier CLIs; TAINTED accepted as canonical actual status.
- M10: lean-build.yml reconstructed as the sole Lean authority with module
  matrix, full clean build, axiom audit, Python gates, certificate
  generation, independent verifier, claim audit, fail-closed final gate;
  scripts/ci helpers; CERTIFICATE_SCHEMA_V2 doc; AGENTS.md source list
  updated to 72 files.

| Command | Result |
|---|---|
| `python -m pytest tests/ -q` | 130 passed (provisional local) |
| `python scripts/scan_lean_guards.py proofs/lean/juris_lean/JurisLean` | passed (provisional) |
| `python scripts/ci/changed_lean_modules.py --all` | 72-module matrix emitted |
| `python scripts/ci/build_run_identity.py` | NOT_CI_LOCAL_PLACEHOLDER, exit 1 (fail-closed) |

Lean build evidence for all 40 wave-added modules remains `CI_NOT_RUN`:
no Lean/Elan/Lake was executed locally. The next step requires user
authorization to push a `ci/**` branch or dispatch the workflow.

## 2026-08-16 CI debugging

- Pushed to `ci/theory-absorption-20260816` (run #45): all 72 module matrix
  builds succeeded (including 40 new modules); `lean-full-clean-build` failed
  at step 7 (module loop) in ~1 second — exact error was gated behind login.
- Run #46: serial loop variant ran for ~3 hours before failing (line 1526);
  BanachScratch module timed out at 240 minutes.
- Runs #47/#48/#49 were stuck in `pending` due to concurrency group deadlock:
  `lean-${{ github.ref }}-${{ github.run_attempt }}` caused all ci/ branch pushes
  to share the same group, queueing new runs behind old zombie runs.
- Fix: removed concurrency group entirely. Pushed to `ci/absorption-v2` (run #50,
  sha 5ba14bc) — workflow entered `queued` status, ready for runner allocation.
- Added per-module `::error::` annotations, df diagnostics, and parallelized loop
  (xargs -P3) to the full-clean-build job for faster diagnosis.
- Key Lean evidence: all 40 new modules compiled successfully in CI module matrix
  jobs (runs #45/#46). The root build (lake clean && lake build) also succeeded.
- Remaining blocker: full-release job's per-module loop (step 7) failure —
  root cause still under investigation via run #50 annotations.

| Command | Result |
|---|---|
| CI module matrix (run #45, 72 modules) | 72/72 success |
| CI root build (run #45, step 6) | success |
| CI full-clean-build step 7 (run #45) | failure (~1s, error gated) |
| CI full-clean-build step 7 (run #46) | failure (~3h, line 1526) |
| shields badge | `build: failing` (latest completed run) |
