# CLAUDE.md -- legal-math-modeling project rules

Status: rewritten on 2026-07-01.

## Non-negotiable Rules

- Formal statements are controlled by Lean source under `proofs/lean/juris_lean/JurisLean/`.
- Do not close proof obligations with placeholder proof terms or custom proof assumptions.
- Do not define vacuous theorem targets to simulate progress.
- Do not weaken theorem statements to satisfy a build.
- Unknown, timeout, skipped, unavailable, and error states are fail-closed.
- Do not change `DecisionStatus`, checker acceptance criteria, verified-fact gates, or attack/exception/priority semantics from documentation work.
- LLM output is candidate material only and is not reasoning-eligible until source-bound verification succeeds.

## Repository Role

This repository is the upstream mathematical specification boundary for selected legal-reasoning slices. It is not the production runtime and does not publish customer data, commercial legal rule libraries, lawyer workflows, litigation strategy, or private benchmarks.

## Current Source Inventory

- Lean source directory: `proofs/lean/juris_lean/JurisLean/`
- Lean source files at rewrite time: 32
- Theorem declarations at rewrite time: 126
- Canonical types: LegalFact, LegalRule, LegalNorm, LegalClaim, Argument, Attack, Priority, Violation, Reparation, DecisionStatus, ProofTrace
- DDL modalities: OBLIGATION, PROHIBITION, PERMISSION, CONSTITUTIVE
- Public slices: contract breach, license, permission, priority

These are inventory facts, not a current-head release certificate.

## Verification Commands

```bash
python -m pytest -q
python scripts/scan_lean_guards.py proofs/lean/juris_lean/JurisLean
cd proofs/lean/juris_lean && lake build
```

Run the checks on the commit being claimed. A stale report is not evidence for a new commit.

## Documentation Rules

- Documentation may explain source-bound facts; it must not create new semantics.
- Reports and papers are explanatory artifacts, not proof certificates.
- Every release statement must name the evidence and residual risk.
- Keep generated caches, build outputs, and local paths out of tracked files.

## Git Rules

- Local commits are allowed for closed verification units.
- Do not force-push, tag, release, or change repository visibility without explicit user instruction.
