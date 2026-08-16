# Findings

## Baseline

- Active goal already exists for completing the named construction plan.
- Current branch: `main`; HEAD `a3a0159`; `main` matches `origin/main` at inspection time.
- Initial worktree change: only the user-supplied, untracked construction plan.
- No project-root `memory`/`MEMORY` file exists.
- No `禁用表达.md` or similarly named repository file was found; apply the explicit AGENTS.md
  anti-AI wording rules directly.
- No prior planning-with-files state existed.

## Plan Boundary

- Unconditional priorities: L0 formal release certificate, L1 checker v2, L2 translation witness,
  L5 real runtime refinement receipt.
- L3 temporal applicability and L4 exact numeric contract are expressly conditional on evidence
  of a real consumer exposing those fields or branches.
- FormalReleaseCertificate and RuntimeRefinementReceipt must remain separate artifacts.
- A digest proves content binding only; it does not prove source authority, translation fidelity,
  runtime correctness, or legal correctness.

## Evidence Still Needed

- Current source/test/document inventory and whether parts of L0-L5 already exist.
- Actual theorem count and current Lean build health.
- Current Python collection and full-suite health.
- Availability of Lean/Elan/Lake/Python toolchains.
- Evidence of a stable external runtime entry point and receipt producer.
- Evidence that a real consumer triggers temporal or numeric integration.

## Current Implementation Inventory

- None of the planned v2/release/witness/temporal/numeric schema or module names currently exist.
- Python `certificate_schema.py` is v1 and checks a transport payload; it does not bind source,
  rule-pack, semantics, checker version, expected obligations, or a non-empty trace digest.
- Lean `Certificate` stores producer-reported `wellFormed`, `requiredFactsPresent`, and
  `proofObligationsPresent`; `readyCertificate` uses `emptyTrace` while reporting all three true.
- Current Horn/AAF validation checks closure support and endpoint existence but cannot establish
  expected-edge completeness, reject all unwitnessed edges, or validate priority direction.
- `runtime_differential.py` and its JSON fixture contain `jc_shadow_status`; the reference-side
  process supplies both compared statuses, so current output is not cross-implementation evidence.
- `AxiomAudit.lean` imports only four core modules and prints a small fixed theorem subset.
- `JurisLean.lean` does not yet import any planned v2/witness/temporal/numeric module.
- Lean toolchain and Mathlib are both pinned at 4.30.0; the manifest records exact dependency commits.
- `.gitignore` already excludes `.lake/`, Lean object artifacts, `build-logs/`, and generated run folders.

## Initial Design Constraint

The smallest compliant path is versioned additive contracts: keep v1 names/readers for compatibility,
add v2 data and independent validation alongside them, then migrate the positive examples to v2.
Do not weaken or rewrite the existing fixed-point core.

## L0 Gaps

- CI performs clean Lean build and guard scan only; it does not collect/run Python tests, generate
  manifests/certificate, persist raw axiom output, or independently verify a certificate artifact.
- The external-build recorder binds only exit code, commit, timestamps, and build-log digest; it
  omits tree/dirty state, toolchain/dependencies, source digests, tests, guard, axiom audit, and limits.
- `theorem_manifest.json`, `lean_manifest.json`, and `proof_ledger.json` are hand-maintained
  inventories with stale version labels and no per-source digest/line-level theorem records.
- `axiom_audit.txt` is narrative Markdown, not command output.
- `SORRY_LEDGER.md` lists 18 blocking theorem names that do not exist in current Lean source; the
  three closed DDL theorem names do exist and remain valid within their stated four-slice boundary.

## Conditional Consumer Check

- No current spec/runtime/test/Lean path uses the proposed temporal applicability fields or exact
  numeric unit/scale/rounding/overflow contract. Existing research modules do not by themselves
  establish the plan's real-consumer trigger.
- The sibling `juris-calculus` and `deli-autoresearch` repositories exist, but the expected
  cross-repo root environment variables are unset.
- No local `.lake` workspace or user/system Lean executable was found in the first targeted paths.

## Memory-Derived Lead Requiring Live Verification

- Prior memory describes juris-calculus as a deterministic formal kernel with MCP as an adapter and
  warns that mock/LLM paths are not real integration evidence. That note applies to another checkout
  and explicitly requires current-entrypoint revalidation, so it is only a search lead here.

## External Runtime Revalidation

- The current sibling JC repository has a formal `evaluate` CLI that writes and verifies replayable
  audit bundles, but it does not expose a RuntimeRefinementReceipt contract or producer.
- Its existing `spec_shadow_harness.py` directly constructs shadow fixtures, runs lower-level JC
  evaluator components, imports LMM reference modules, and compares both sides in one process. It is
  explicitly classified as shadow and is not the formal `evaluate` entrypoint required by L5.
- The sibling repository is currently dirty in four core contract/type/rule files and has its own
  untracked construction plan. These are user changes; LMM work must not overwrite or bundle them.
- The sibling JC construction plan states that LMM/Deli are optional validation services and keeps
  unproved IR/differential paths in shadow. It does not promise the missing receipt producer.
- No existing `elan.exe` or `lake.exe` was found under `D:\Codex`; Lean installation is required for
  real local proof gates unless another explicit executable path is discovered.

## Baseline Tool Discovery

- Git 2.54.0, Python 3.12.10, and a `pytest 9.1.1` command are visible.
- The active `python.exe` cannot import pytest. The working interpreter is the Hermes agent venv
  Python; it imports this checkout and runs the suite successfully, but certificate metadata must
  record its exact path.
- `elan`, `lake`, and `lean` are not on the current PowerShell `PATH`; this is not yet evidence that
  the toolchain is absent.
- Static per-file theorem counts sum to the documented 126 declarations.
- The guard searches returned no forbidden proof-closing token or `theorem : True` match; the
  aggregate command exit code was 1 because `rg` uses 1 for no matches and tools were not found.
- Baseline collection is only 12 tests, all in `tests/spec/test_spec_transition.py`; all 12 pass.

## 2026-08-16 Theory Absorption (M0 close, red-test close)

- Branch `codex/lmm-theory-absorption-plan` carries three plan commits on top of
  baseline `f521b5b`; worktree clean at construction start.
- All four red test modules failed for missing implementations only (no import-path,
  environment, or test-self errors): v2 certificate API, translation witness module,
  runtime receipt API, and the release inventory script.
- After implementation the full local suite is 36 passed; guard scan clean.
  These remain provisional local results until CI runs on the subject commit.
- `theory/spec/translation_witness.py` checks edge omission, spurious edges,
  direction reversal, witness binding, and semantics registry per hop.
- `certificate_schema.py` v2 checker recomputes content digests, rejects empty trace,
  candidate evidence, duplicates, unstable sequences, unknown semantics/checker,
  stale snapshots, and v1 decisive claims; producer booleans are not consulted.
- `runtime_differential.py` receipt verifier classifies missing receipt, commit/digest
  mismatch, execution failure, and unknown status mapping as fail-closed; expected
  fixtures are content-addressed by digest.
- `scripts/generate_formal_release_certificate.py` derives the Lean inventory from
  source (path, sha256, theorem name/line) and refuses release without CI evidence.
- `scripts/verify_formal_release_certificate.py` re-derives inventory independently
  and matches CI artifact digests; no shared implementation with the generator.
- Lean build evidence status: `CI_NOT_RUN`. No Lean/Elan/Lake was executed locally.
  The pre-existing local `.lake` directory stays git-ignored and is not evidence.
- Authority map recorded in `docs/remediation/authority_map.md`.
- Old plan `260810...施工方案.md` marked SUPERSEDED INPUT; its stop-early scope
  limits are void per the 2026-08-15 construction plan.

## 2026-08-16 Theory Absorption (M1-M10 close, awaiting CI)

- All M1-M10 source deliverables are authored locally: 40 new Lean modules
  (72 total), canonical v2 package, source/path/temporal/admission/taint/
  argumentation/numeric/backend/dual-IR/authority/certificate references,
  refinement fixtures, and the CI-authority workflow.
- Full local suite: 130 passed; guard scan clean; both provisional.
- UNPROVED obligations (kept as Prop targets, never closed by axiom):
  full-chain translation soundness/completeness beyond the supported
  fragment, and incremental-vs-clean compilation equivalence
  (`TranslationRefinement.lean`).
- Root build (lake clean && lake build) succeeded: 2968 jobs, 0 errors, Mathlib fully compiled.
- Module matrix: 72/72 modules compiled successfully in CI (all 40 new modules green).
- lean-full-clean-build failure root cause: `AxiomAudit.lean` imports `HornFixedPoint`,
  `WeightedSupNorm` etc. which are NOT in the root's transitive dependencies;
  `lake clean && lake build` doesn't produce their `.olean` files.
  Fix: `lake build JurisLean.AxiomAudit` before running the audit.
- New run (sha 530da4f, run 31928479252) queued with the fix.
- Risk note: the 40 new Lean modules were authored without local Lean
  execution (forbidden). Their proofs follow conservative patterns but the
  first CI module matrix run is the authoritative compile check; any CI
  failure must be fixed without weakening theorem statements.
- New modules are not imported by the root `JurisLean.lean`, so the
  historical full clean build surface is unchanged until CI evidence exists.
