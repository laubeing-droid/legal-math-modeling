# AGENTS.md -- legal-math-modeling project rules

> Loaded automatically at session start. Every AI agent MUST follow.

## Repository Identity

- Owner: laubeing-droid
- Remote: https://github.com/laubeing-droid/legal-math-modeling
- Primary language: Lean 4.30.0 (Mathlib4 v4.30.0)
- Secondary: Python 3.12 (refinement bridge, tests)

## Lean Proof Rules (NON-NEGOTIABLE)

1. NEVER use `sorry`, `admit`, or `axiom` to close a goal.
2. NEVER define a theorem as `theorem ... : True := by trivial`. If a proposition is not yet proved, declare it as `def` target or `Prop` statement with `UNPROVED` status.
3. After writing any helper lemma, immediately compile: `lake build` or `lake env lean <file>`.
4. Before using an unfamiliar Mathlib API, run `#check` in a scratch file first. Then `rg` the API name in `proofs/lean/juris_lean/.lake/packages/mathlib` to confirm signature.
5. NEVER weaken a theorem statement to pass `lake build`. If stuck, mark it as a partial target and report the blocker.
6. Theorem count is determined by `rg '^theorem ' --no-filename --count`, not by any report or memory.
7. Build artifacts: NEVER commit `.olean`, `.ilean`, `.trace`, `.hash`, or `.lake/` directories.

## Build Commands

```powershell
# Full build (core modules, no Analysis)
cd proofs/lean/juris_lean
lake build

# Single module check
lake env lean JurisLean/FiniteMonotoneIteration.lean

# Scan for forbidden tokens
rg -n "\bsorry\b|\badmit\b|\baxiom\b" proofs/lean/juris_lean/JurisLean/

# Axiom audit for a specific theorem
lake env lean JurisLean/AxiomAudit.lean

# Cross-repo Python tests (juris-calculus refinement)
cd D:\Codex\juris-calculus
pytest tests/ -q -ra
```

## Repository Layout

```
legal-math-modeling/
  proofs/lean/juris_lean/JurisLean/   -- Lean source (THE truth)
  proofs/engineering_proof_artifacts/  -- Python certs, test vectors
  docs/formal-release/                 -- Release reports, manifests
  docs/remediation/                    -- Audit close-out artifacts
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
