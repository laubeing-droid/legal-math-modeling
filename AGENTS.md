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

- Proven `FiniteMonotoneIteration`, Dung, Horn core modules: do NOT rewrite without counterexample or build failure.
- Single Lean file: single writer at a time. Parallel writes use separate worktrees.
- NEVER commit `.olean`, `.ilean`, Lake build directories, or machine build caches.
- NEVER auto force-push, publish release, or create remote tag without confirmation.
- Create local checkpoint commit at each phase boundary.

## Repository Identity

- Owner: laubeing-droid
- Remote: https://github.com/laubeing-droid/legal-math-modeling
- Primary language: Lean 4.30.0 (Mathlib4 v4.30.0)
- Secondary: Python 3.12 (refinement bridge, tests)

## Lean Proof Rules

1. NEVER use `sorry`, `admit`, or `axiom` to close a goal.
2. NEVER define a theorem as `theorem ... : True := by trivial`. If unproven, declare as `def` target or `Prop` statement with `UNPROVED` status.
3. After writing any helper lemma, immediately compile: `lake build` or `lake env lean <file>`.
4. Before using an unfamiliar Mathlib API, run `#check` in a scratch file first. Then `rg` the API name in `proofs/lean/juris_lean/.lake/packages/mathlib` to confirm signature.
5. NEVER weaken a theorem statement to pass `lake build`. If stuck, mark it as a partial target and report the blocker.
6. Theorem count is determined by `rg "^theorem " --no-filename --count`, not by any report or memory.
7. Build artifacts: NEVER commit `.olean`, `.ilean`, `.trace`, `.hash`, or `.lake/` directories.

## Build Commands

```
# Full build (core modules, no Analysis)
cd proofs/lean/juris_lean
lake build

# Single module check
lake env lean JurisLean/FiniteMonotoneIteration.lean

# Scan for forbidden tokens
rg -n "\bsorry\b|\badmit\b|\baxiom\b" proofs/lean/juris_lean/JurisLean/

# Axiom audit
lake env lean JurisLean/AxiomAudit.lean

# Cross-repo Python tests (juris-calculus refinement)
cd D:\Codex\juris-calculus
pytest tests/ -q -ra
```

## Lean Workflow

- After completing any helper lemma, immediately build target file.
- When unsure about an API, run `#check` first, then search locally.
- NEVER guess a Mathlib declaration from memory.
- Final execution order: `lake clean` -> `lake build` -> AxiomAudit -> scan for sorry/admit/axiom/True theorem.

## Python Workflow

- Run `pytest --collect-only -q` and save the collection manifest.
- Run `pytest -q -ra` for full results.
- NEVER run only a subset and report as full test pass.
- Cross-repo bridge: validate schema, commit, digest, status.
- Certificate checker MUST NOT call the main evaluator implementation.

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

## Repository Layout

```
legal-math-modeling/
  proofs/lean/juris_lean/JurisLean/   -- Lean source (THE truth)
  proofs/engineering_proof_artifacts/  -- Python certs, test vectors
  docs/formal-release/                 -- Release reports, manifests
  docs/remediation/                    -- Audit close-out artifacts
  program/                             -- Night-run control directory
  theory/                              -- Original mathematical theory
  verification/                        -- Cross-validation scripts
```

## Cross-Repo Rules

- juris-calculus (D:\Codex\juris-calculus) consumes Lean theorems via refinement bridge.
- deli-autoresearch (D:\Claude\数学证明自动研究) runs autonomous exploration over juris-calculus.
- Any change to a Lean theorem statement MUST trigger cross-repo verification.
- Fail-closed: UNKNOWN / TIMEOUT / TRUNCATED results propagate as errors, never as success.

## Communication

- Chinese with user; English in code, comments, and commit messages.
- Conclusions first, reasons after.
- Uncertain = say uncertain. Do not fabricate.
- Git operations: confirm with user before destructive actions.
