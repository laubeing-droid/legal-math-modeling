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

## Current Construction State

- The content-bound Python and Lean v2 contracts are implemented side-by-side with v1. Python
  mutation tests reject empty traces, coverage omissions, unknown arguments, digest mutations,
  unknown semantics/checker versions, candidate evidence, duplicate IDs, unstable order, and stale
  source replay.
- The exact finite translation witness is implemented in Python and Lean. The Python checker rejects
  expected-edge omission, spurious edges, and priority direction reversal.
- `RuntimeRefinementReceipt` has a schema and independent LMM verifier. No current external runtime
  entrypoint produces the actual receipt, so no cross-implementation agreement claim is available.
- Current generated inventory records 33 Lean files and 141 theorem declarations. This remains a
  source inventory by itself. GitHub Actions separately produced and independently verified a
  commit-bound `FormalReleaseCertificate` for the successful PR merge subject.
- User required all remaining Lean work to run in GitHub Actions. Local Lean build/download activity
  is stopped and will not be used as release evidence.
- The old default `lake build` did not compile every `.lean` file under the authority tree. Strict
  release verification must build the root plus explicit targets derived from all 33 inventory paths.
- The strict CI build completed 8509/8509 jobs. AxiomAudit passed and reported only the declared
  trusted basis: `propext`, `Classical.choice`, and `Quot.sound`.
- The successful certificate has digest
  `8a67357e0905d712071b45a429b615fb963acb03d8325ef324776b96694ee82b` and source inventory digest
  `7019af4490a75e758db271879536565c86316e0c0ae7dd4a8c63e4861de93247`.
- L5 is still not cross-implementation evidence: the current external formal runtime entrypoint does
  not produce an actual `RuntimeRefinementReceipt`. The LMM verifier must remain fail-closed.
- The plan makes the producer boundary explicit: LMM owns the content-addressed expected fixture and
  independent verifier; `juris-calculus` must execute its formal chain and emit the actual receipt.
  A scheduler or same-process LMM helper cannot satisfy this requirement.
- Final-head CI run `31850513493` independently verified the LMM release gates. Its evidence closes
  L0-L2 only; it does not reduce or substitute the remaining L5 external-producer requirement.
- The current receipt verifier is already content-bound at both envelope and case-output levels. A
  compliant producer must copy only LMM-owned bindings from the supplied expected fixture, derive
  actual statuses from JC's formal execution output, bind the exact JC commit, and compute its own
  canonical output/receipt digests.
- The plan names a historical differential path that is absent from the current tree. Final evidence
  must cite the actual expected-only fixture path and must not recreate a stale same-process fixture.
- The authoritative tracked template is
  `runtime/refinement_cases/four_slice_expected.template.json`; it declares ten case IDs and statuses
  but intentionally contains no commits or digests.
- Receipt v1 currently hashes only `case_id` and the producer-supplied mapped status. That is not
  enough to establish provenance from a JC run. JC audit bundles already expose independently
  verifiable `result_digest`, `bundle_digest`, formal/checker flags, pack digest, run ID, claims, and
  risk/taint state; the receipt contract should bind and validate those fields.
- A dedicated producer should consume completed JC audit runs only after `verify_audit_bundle`, then
  derive the LMM status from canonical semantic fields. It must not import the LMM checker, accept a
  caller-supplied `actual_status`, or use `spec_shadow_harness`.
- JC's architecture gate permits only `evaluate_case` and `evaluate_to_audit_bundle` as canonical
  entrypoints and forbids parallel evaluator construction. The receipt producer must verify/replay
  existing audit bundles or call the canonical audit entrypoint; it cannot create another evaluator.
- JC's canonical digest algorithm removes non-semantic timestamp/path/digest fields and hashes sorted
  compact JSON. LMM can implement this small algorithm independently to recheck an embedded
  `SemanticResult.result_digest` without importing JC.
- A test-only official pack can pass the real registry, source-anchor, application, independent
  checker, audit-bundle, and replay gates without becoming a production legal corpus. Its synthetic
  identity and claim boundary must remain explicit in the receipt evidence.
- Status projection is now explicitly owned by the expected fixture: each case binds one focus claim
  and a sorted refuter set. The runtime may report canonical semantic output, but cannot choose the
  projection that turns that output into PROVED/REFUTED/UNDECIDED/TAINTED.
- The first real ten-case formal run completed all audit/replay paths and produced 7 aligned and 3
  divergent statuses. Divergences are `license::priority-off` (expected REFUTED, actual UNDECIDED),
  `permission::conflict` (expected UNDECIDED, actual PROVED), and `priority::active` (expected PROVED,
  actual UNDECIDED). Expected values must remain unchanged under the plan's rollback rule.
- These divergences are not receipt corruption: every case had completed canonical output and a valid
  independent checker receipt. The correct release state is a structurally valid external receipt
  plus fail-closed `RESULT_MISMATCH`, not a cross-runtime agreement claim.
- The LMM materializer can derive HEAD safely by rejecting tracked changes while ignoring unrelated
  untracked files. The independent verifier maps valid divergence to `INCONCLUSIVE` and structural
  or provenance failure to `BLOCKED`; only full validity plus alignment maps to `PASS`.
- JC's complete 419-test collection completed as 391 pass and 28 documented heavy-dependency skips;
  the external receipt additions introduced no Python regression or canonical-entrypoint violation.
- Import-based tests do not prove a repository script can run from an arbitrary working directory.
  Both refinement CLIs now bootstrap the repository root explicitly, and direct `--help` subprocess
  tests run from the parent directory to preserve that boundary.
