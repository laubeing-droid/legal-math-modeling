# Pre-release Audit Report - legal-math-modeling

Date: 2026-07-01

Scope: `legal-math-modeling` local pre-release audit using the `pre-release-auditor` L1-L4 gate model.

## Repository State

- Repo: `<legal-math-modeling-root>`
- Branch at report time: `master`
- Local HEAD at report time: `702b5a498b93d18603f0c8723f6b512900c83b70`
- HEAD summary: `702b5a4 Harden legal-math pre-release L2 cleanup`
- Git state after cleanup commit: `master...origin/master [ahead 4]`
- Dirty/untracked process state before report file: clean; `git clean -ndX` and `git clean -ndx` produced no removal candidates.
- Push/tag/release: not performed.

## L1 - Supply Chain

Status: BLOCKED / fail-closed.

Evidence:

- `requirements.txt` remains range-based: `numpy>=1.24.0`, `pyyaml>=6.0`, `hypothesis>=6.0.0`, `z3-solver>=4.12.0`, `sympy>=1.12.0`.
- Temporary venv dependency install was attempted with `HTTP_PROXY` and `HTTPS_PROXY` set to `<local-proxy>`; dependency resolution timed out against PyPI and ended with `OSError: [Errno 22] Invalid argument` during `numpy` handling.
- `pip-audit` was installed in a temporary venv and the temp venv was removed afterward, but `pip-audit -r requirements.txt --progress-spinner off` failed while resolving `numpy>=1.24.0` due repeated PyPI read timeouts. No vulnerability pass can be claimed.
- `python -m pip check` in the ambient Python environment reported conflicts in unrelated globally installed packages: `googleapis-common-protos`/`protobuf`, `kubernetes`/`pyyaml`, and `opentelemetry-proto`/`protobuf`.

Release decision: do not release until dependency resolution and vulnerability audit complete in a controlled environment.

## L2 - Sanitization

Status: PASS locally after cleanup commit `702b5a4`.

Changes made:

- Removed tracked process files: `_restore.py`, `build-logs/20260624-204838/*`, `build-logs/20260624-210317/*`.
- Removed generated binary figure with embedded local-path scan hit: `reports/mdl_fp/mdl_fp_scatter.png`.
- Added ignore rules for regenerated process outputs: `artifacts/`, `build-logs/`, `program/runs/`, `program/reports/`.
- Replaced local/private paths in `AGENTS.md`, `CLAUDE.md`, `docs/audit/codex_audit_report_20260619.md`, `program/PLANS.md`, `proofs/formal_verification_logs/*.md`, and `proofs/lean/juris_lean/JurisLean/HornOperationalRefinement.lean`.
- Reworked external/private input scripts to require explicit inputs and fail closed:
  - `LEGAL_MATH_T85_T94_SOURCE_ROOT`
  - `LEGAL_MATH_REAL_CLAIM_MAPPING_CSV`
  - `JURIS_CALCULUS_RULES_YAML`

Verification:

- Local-path/proxy scan:
  - `rg -n --pcre2 '<local-path-or-local-proxy-pattern>' .`
  - Result: no matches.
- Secret-token scan:
  - `rg -n --pcre2 '(AKIA[0-9A-Z]{16}|-----BEGIN (RSA |DSA |EC |OPENSSH |)PRIVATE KEY-----|ghp_[A-Za-z0-9_]{20,}|github_pat_[A-Za-z0-9_]{20,}|sk-[A-Za-z0-9]{20,})' .`
  - Result: no matches.
- External input fail-closed checks:
  - `python proofs\engineering_proof_artifacts\rosetta\t85_t94_data_extractor.py` => exit 1, missing `LEGAL_MATH_T85_T94_SOURCE_ROOT`.
  - `python proofs\strict_proof_baseline\p0a_category\real_data_insufficiency_witness.py` => exit 1, missing `LEGAL_MATH_REAL_CLAIM_MAPPING_CSV`.
  - `python theory\k3_empirical_analysis.py` => exit 1, missing path argument or `JURIS_CALCULUS_RULES_YAML`.

## L3 - Semantic And Lean Guard

Status: PASS locally.

Verification:

- `python scripts/scan_lean_guards.py proofs/lean/juris_lean/JurisLean` => `Lean guard scan passed.`
- `rg -n --pcre2 '\b(sorry|admit)\b|^\s*axiom\b|theorem\s+[^:\n]+:\s*True\s*:=\s*by\s*trivial' proofs/lean/juris_lean/JurisLean` => no matches.
- `docs/formal-release/theorem_manifest.json` exists and parses as JSON.
- Stale narrative scan found only a cautious historical statement in `proofs/formal_verification_logs/07_logic_audit_report.md` saying strictly fully verified proof entries are small; this is not an over-claim.

No changes were made to Lean theorem statements, `DecisionStatus`, checker acceptance criteria, `verified_fact` gates, or attack/exception/priority semantics.

## L4 - Runtime And CI

Status: PARTIAL PASS / release-blocking CI gap.

Local verification:

- `python -m pytest -q` => `12 passed`.
- `python -m compileall -q scripts theory tests verification proofs/engineering_proof_artifacts proofs/strict_proof_baseline` => exit 0; existing warnings only in `theory\rough_set_discretionary.py` docstrings for invalid escape sequences.
- `python -m json.tool docs\formal-release\theorem_manifest.json` => OK.
- `python -m json.tool proofs\engineering_proof_artifacts\proof_run_results.json` => OK.

GitHub Actions evidence:

- Current local HEAD `702b5a498b93d18603f0c8723f6b512900c83b70`: GitHub API query returned `NO_RUNS_FOR_CURRENT_HEAD`.
- Workflow states:
  - `Banach Proof Build (Track B)` at `.github/workflows/banach-build.yml`: active.
  - `Lake Build + Scan` at `.github/workflows/lean-build.yml`: `disabled_manually`.
- Prior remote SHA `2ab6cda38f2392cd048bc0643e56fb5f9fc46708` has successful Banach CI:
  - Run: https://github.com/laubeing-droid/legal-math-modeling/actions/runs/28465952314
  - Job: `banach`, status `completed`, conclusion `success`.
  - Steps included successful `Lake build (incremental)`, `Build Banach target specifically`, and `Scan for sorry/axiom`.

Release decision: the prior Banach run is useful historical evidence, but it is not evidence for current local HEAD `702b5a4`; release remains blocked until current HEAD has remote Lean CI evidence.

## Commit Evidence

- Cleanup commit: `702b5a498b93d18603f0c8723f6b512900c83b70`
- Commit message records:
  - changed files and removed process artifacts,
  - root cause,
  - new project knowledge,
  - impact boundary,
  - verification commands,
  - remaining risk.

## Blocked Items

Unique minimal blocking task:

Run the full release gate for current HEAD in an environment that can resolve Python packages and execute Lean CI: push/dispatch current HEAD to an active CI path that runs dependency audit plus `lake build`/Lean guard scan, or re-enable `Lake Build + Scan` and run it on current HEAD.

Blocking evidence:

- `NO_RUNS_FOR_CURRENT_HEAD` for `702b5a498b93d18603f0c8723f6b512900c83b70`.
- `Lake Build + Scan` is `disabled_manually`.
- `pip-audit` could not resolve `numpy>=1.24.0` because PyPI reads timed out through proxy.

Next smallest executable task: run the above current-HEAD release gate. Until then, pre-release status is fail-closed.
