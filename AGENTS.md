# AGENTS.md -- legal-math-modeling project rules

> Loaded automatically at session start. Every AI agent MUST follow.

## Trust Rules (NON-NEGOTIABLE)

- NEVER use `sorry`, `admit`, or custom `axiom` to close a goal.
- NEVER define `theorem ... : True := by trivial`. If unproven, declare as `Prop` target with `UNPROVED` status.
- NEVER put a target conclusion into a premise.
- When original proposition is false, preserve machine counterexample and revise theorem contract.
- SMT / Hypothesis / Python regression do NOT substitute for Lean theorem.
- Fixed regression tests prove backend health only, never the current claim.
- UNKNOWN / TIMEOUT / SKIP / NOT_RUN / BACKEND_UNAVAILABLE / ERROR are ALL fail-closed.

## Change Rules

- Proven core modules (FiniteMonotoneIteration, DungFixedPoint, HornFixedPoint, WeightedSupNorm): do NOT rewrite without counterexample or build failure.
- Single Lean file: single writer at a time. Parallel writes use separate worktrees.
- NEVER commit `.olean`, `.ilean`, Lake build directories, or machine build caches.
- NEVER auto force-push, publish release, or create remote tag without confirmation.
- Create local checkpoint commit at each phase boundary.

## Repository Identity

- Owner: laubeing-droid
- Remote: https://github.com/laubeing-droid/legal-math-modeling
- Primary language: Lean 4.30.0 (Mathlib4 v4.30.0)
- Secondary: Python 3.12 (refinement bridge, tests)
- Total verified results: historical snapshot 126 (42 core + 84 supporting); current counts ONLY from the generated source inventory, never from this line.
- Build: historical snapshot `lake build JurisLean` -> 2961 jobs, 0 error, 0 sorry; current build status ONLY from GitHub Actions on the subject commit.

## Lean Execution Boundary

- Lean/Elan/Lake are NEVER installed or executed on the local machine.
- Local work is limited to: source edits, static inventory, text guard pre-checks, Python contract tests, and Git inspection. Local results are labelled provisional and are never a Lean PASS.
- GitHub Actions is the sole Lean authority: module matrix checks, `lake clean && lake build`, axiom audit, guards, and certificate generation all run in CI bound to the subject commit/tree.
- Without per-round push/dispatch authorization, Lean build status stays `CI_NOT_RUN` (fail-closed).

## Lean Proof Rules

1. NEVER use `sorry`, `admit`, or `axiom` to close a goal.
2. NEVER define a theorem as `theorem ... : True := by trivial`. If unproven, declare as `def` target or `Prop` statement with `UNPROVED` status.
3. After writing any helper lemma, immediately trigger the CI module check: push an authorized `ci/**` branch or dispatch `mode=changed-module` for the existing remote SHA; never compile locally.
4. Before using an unfamiliar Mathlib API, confirm its signature in the pinned Mathlib source (`lake-manifest.json` commit) by text search; never guess.
5. NEVER weaken a theorem statement to pass the CI build. If stuck, mark it as a partial target and report the blocker.
6. Theorem count is determined by `rg "^theorem " --no-filename --count`, not by any report or memory.
7. Build artifacts: NEVER commit `.olean`, `.ilean`, `.trace`, `.hash`, or `.lake/` directories.

## Lean Source Files (72 actual)

The following 72 `.lean` files exist in `proofs/lean/juris_lean/JurisLean/`
(32 historical + 40 added by the 2026-08-15 theory-absorption waves; current
list is always re-derived from the generated inventory, never copied):

`ArgumentCompilerSpec.lean`, `ArgumentSemanticsRegistry.lean`, `ASPWitness.lean`, `AttackDecision.lean`, `AuthorityLattice.lean`, `AxiomAudit.lean`, `BackendContract.lean`, `BanachCertificate.lean`, `BanachComplete.lean`, `BanachContraction.lean`, `BanachEffectiveNodes.lean`, `BanachFixedPoint.lean`, `BanachScratch.lean`, `BanachWeightedNorm.lean`, `Basic.lean`, `CanonicalSerialization.lean`, `CertificateChecker.lean`, `CertificateCheckerV2.lean`, `CertificateV2.lean`, `ContractionCondition.lean`, `DDLDefinitions.lean`, `DefeasiblePriority.lean`, `DungAAF.lean`, `DungDefinitions.lean`, `DungFixedPoint.lean`, `EndToEnd.lean`, `ExactNumericContract.lean`, `FactAdmissionSpec.lean`, `FailureStatus.lean`, `FiniteGaloisAdjunction.lean`, `FiniteMonotoneIteration.lean`, `FiniteRosetta.lean`, `HornAAFContract.lean`, `HornDefinitions.lean`, `HornFixedPoint.lean`, `HornOperationalRefinement.lean`, `HumanResearchReceiptSpec.lean`, `IVLToAAF.lean`, `IVLToASP.lean`, `IVLToHorn.lean`, `IVLToSMT.lean`, `JC_Formalization.lean`, `LegalIds.lean`, `LegalIVL.lean`, `LegalIVLWellFormed.lean`, `LegalModelV2.lean`, `LegalSpec.lean`, `LegalSpecNormalize.lean`, `LegalSpecToIVL.lean`, `LegalSpecWellFormed.lean`, `LegalSyntax.lean`, `LegalWellFormed.lean`, `PermissionConflict.lean`, `ProposalEnvelopeSpec.lean`, `ProposalNoninterference.lean`, `ReceiptAuthority.lean`, `SafetyTheorems.lean`, `ScratchApi.lean`, `SMTWitness.lean`, `SolverRouting.lean`, `SourceBundleSpec.lean`, `SourcePathSpec.lean`, `SupZeroLemma.lean`, `TaintNoninterference.lean`, `TemporalApplicability.lean`, `TemporalArithmetic.lean`, `TemporalKripke.lean`, `TranslationRefinement.lean`, `TranslationWitness.lean`, `TypedAttack.lean`, `UnifiedModel.lean`, `WeightedSupNorm.lean`

The 40 wave-added modules are authored but `CI_NOT_RUN`: they join release
claims only after the GitHub Actions module matrix and full clean build pass
on the subject commit. They are intentionally not imported by the root
`JurisLean.lean` until that CI evidence exists.

**Ghost files (DO NOT reference as existing):** `argmin_polytime.lean`, `HornCanonical.lean`, `ArgumentCompiler.lean`, `LegalModel.lean`

## Core Theorem Map

| File | Core Count | Key Theorems |
|------|-----------|-------------|
| DungFixedPoint.lean | 16 | `F_monotone`, `finite_termination`, `iteration_bound`, `groundedSpec_is_fixed_point`, `grounded_is_fixed_point`, `groundedSpec_is_least_fixed_point`, `grounded_is_least_fixed_point`, `grounded_is_least_complete`, `groundedSpec_unique_least_fixed_point`, `labelling_partition`, `in_soundness`, `out_soundness`, `undecided_characterization`, `self_attack_precise_theorem`, `self_attack_not_in_grounded` |
| HornFixedPoint.lean | 10 | `horn_operator_subset_univ`, `horn_operator_monotone`, `horn_iteration_monotone`, `horn_finite_termination`, `horn_iteration_bound`, `horn_result_fixed_point`, `horn_result_least_fixed_point`, `horn_soundness`, `horn_completeness`, `horn_result_is_minimal_model` |
| FiniteMonotoneIteration.lean | 9 | `iter_succ`, `iter_subset_univ`, `iter_mono`, `iter_stable`, `iter_ssubset_of_ne`, `iter_card_lt_of_ne`, `iter_card_le_univ`, `exists_fixpoint_le_card`, `fixed_at_card` |
| WeightedSupNorm.lean | 4 | `weightedSupDist_nonneg`, `weightedSupDist_triangle`, `weightedSupDist_symm`, `weightedSupDist_complete` |
| HornDefinitions.lean | 2 | `TH_monotone`, `TH_subset_univ` |
| ContractionCondition.lean | 1 | `lipschitz_coupling_implies_weighted_contraction` |

## Build Commands (CI authority convention)

Lean commands run ONLY inside GitHub Actions (`.github/workflows/lean-build.yml`).
Locally, agents trigger and verify CI; they never run Lean themselves.

```bash
# Trigger a module-matrix CI run (requires per-round user authorization):
git push origin HEAD:ci/<wave>-<date>      # or workflow_dispatch mode=changed-module

# Full release evidence (requires per-round user authorization):
# workflow_dispatch mode=full-release on the subject SHA

# Local provisional pre-checks (NOT Lean evidence):
python scripts/scan_lean_guards.py proofs/lean/juris_lean/JurisLean
python scripts/generate_formal_release_certificate.py --output <path>
python -m pytest tests/ -q -ra

# Verify downloaded CI artifacts (never recompiles Lean):
python scripts/verify_formal_release_certificate.py --certificate <path> --ci-evidence-dir <dir>

# Cross-repo Python tests (juris-calculus refinement)
cd <juris-calculus-root>
pytest tests/ -q -ra
```

## Lean Workflow

- After completing any helper lemma, trigger the CI module matrix for that module and its reverse dependencies (with authorization); otherwise keep status `CI_NOT_RUN`.
- NEVER guess a Mathlib declaration from memory; confirm against the pinned Mathlib commit source text.
- Final CI execution order: checkout subject SHA -> inventory -> `lake clean && lake build` -> AxiomAudit -> guard scan -> Python full tests -> mutation/refinement -> certificate -> independent verifier.
- New modules join the root `JurisLean.lean` only after a CI module build passes for them.

## Python Workflow

- Run `pytest --collect-only -q` and save the collection manifest.
- Run `pytest -q -ra` for full results.
- NEVER run only a subset and report as full test pass.
- Cross-repo bridge: validate schema, commit, digest, status.
- Certificate checker MUST NOT call the main evaluator implementation.
- `canonical_semantics.py` is the v1 compatibility entry for the 11 canonical types; `theory/spec/canonical_v2/` is the decisive v2 universe; v1 never gains v2 decisive status.

## Done Means

A task is complete ONLY when ALL six conditions hold:
1. Precise specification written
2. Code or proof implemented
3. Independent verification test passes
4. Failure modes are fail-closed
5. Output artifact bound to a commit and digest
6. Limitations and forbidden claims recorded

## Prohibited Claims

- "The entire juris-calculus has been formally verified correct by Lean"
- "Python implementation has been fully refinement-proved by Lean"
- "Horn->AAF compiler omits no edges or creates no spurious attacks"
- "Production proof traces have independent sound checker"
- "Incremental Grounded has been proved equal to full recomputation in general"
- "Banach fixed-point existence, uniqueness, convergence, and error bounds are all closed"
- "SPC OCR rules passing convergence test implies correct legal extraction"
- "Graph similarity is a metric or kernel"
- "Differential privacy guarantees are established"
- "38 constants have been empirically calibrated"
- "JC formally proved" (the complete system)
- "Banach complete" (as part of formal-core-v1)
- "Privacy established"

## Closed DDL Targets

3 former domain-axiom targets are now Lean theorems in `DDLDefinitions.lean`:
- `violation_implies_norm_active`
- `permission_no_direct_violation`
- `constitutive_no_direct_violation`

JC may cite these exact Lean theorem names as proved inside the four-slice
minimal DDL model, but must not claim full runtime correctness from them.

## Spec-First Transition Gates

| Gate | Status |
|------|--------|
| M1: Canonical Schema | CLOSED_FOR_FOUR_SLICES |
| M2: DDL Minimal Core | CLOSED_FOR_FOUR_SLICES |
| M3: Horn-to-AAF Contract | CLOSED_FOR_FOUR_SLICES |
| M4: Certificate/Checker Boundary | CLOSED_FOR_FOUR_SLICES |
| M5: Unified Stopping Statement | CLOSED |

## Canonical Types (11)

`LegalFact`, `LegalRule`, `LegalNorm`, `LegalClaim`, `Argument`, `Attack`, `Priority`, `Violation`, `Reparation`, `DecisionStatus`, `ProofTrace`

## DDL Modalities

4 modalities: OBLIGATION, PROHIBITION, PERMISSION, CONSTITUTIVE.
4 repair modes. 3 exception classes.

## Repository Layout

```
legal-math-modeling/
  proofs/lean/juris_lean/JurisLean/   -- Lean source (32 files, THE truth)
  proofs/engineering_proof_artifacts/  -- Python certs, test vectors
  docs/formal-release/                 -- Release reports, manifests
  docs/remediation/                    -- Audit close-out artifacts
  program/                             -- Night-run control directory
  theory/                              -- 59 Python theory modules
  verification/                        -- Cross-validation scripts
```

## Cross-Repo Rules

- juris-calculus (`$JURIS_CALCULUS_ROOT` or `<juris-calculus-root>`) consumes Lean theorems via refinement bridge.
- deli-autoresearch (`$DELI_AUTORESEARCH_ROOT` or `<deli-autoresearch-root>`) runs autonomous exploration over juris-calculus.
- Any change to a Lean theorem statement MUST trigger cross-repo verification.
- Fail-closed: UNKNOWN / TIMEOUT / TRUNCATED results propagate as errors, never as success.

## Communication

- Chinese with user; English in code, comments, and commit messages.
- Conclusions first, reasons after.
- Uncertain = say uncertain. Do not fabricate.
- Git operations: confirm with user before destructive actions.

## Red Lines

1. axiom != proof
2. Proxy data != real empirical data
3. Correlation != causation
4. Stratified computation; reject mixed inference
5. Downgrade proof hallucinations before writing new proofs
