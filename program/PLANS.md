# Execution Plan -- legal-formal-assurance-v2

## Program

- program_id: legal-formal-assurance-v2
- current_track: A2 / C1
- current_task: Lean-to-Python refinement baseline + independent checker gate
- program_status: FORMAL_CORE_RELEASED

## Repository heads

- legal-math-modeling: 4b415b8
- juris-calculus: 15d9be6
- deli-autoresearch: e16e95a

## Completed

- [x] Phase 0: AGENTS.md (all 3 repos) + PLANS scaffold + .gitignore olean + Track B worktree
- [x] Phase 0.5: program/ control directory + MEGA_GOAL.md + PROGRAM_STATE.json + run-night.ps1 + schemas/
- [x] A0 test-count and clean-build audit
- [x] A1 formal-core release gate
- [ ] A2 executable refinement baseline
- [ ] B0 weighted metric completion
- [ ] B1 ContractingWith bridge
- [ ] B2 fixed-point and error bounds
- [ ] B3 BanachCertificate
- [ ] C0 pipeline no-upgrade
- [ ] C1 certificate soundness
- [ ] C2 argument preservation
- [ ] C3 attack preservation
- [ ] C4 compile certificate integration
- [ ] D0 provenance graph
- [ ] D1 safe rule-change impact
- [ ] D2 affected-region theorem
- [ ] D3 incremental equals full
- [ ] E0 minimal support
- [ ] E1 minimal rebuttal
- [ ] E2 minimum-cost intervention
- [ ] E3 minimality certificate

## Formal-core release snapshot

- release_id: formal-core-v1
- theorem manifest: 75 checked results = 43 extended-core + 32 supporting
- formal core modules: 39 theorems across FiniteMonotoneIteration / DungFixedPoint / HornFixedPoint (+ HornDefinitions)
- clean build truth source: GitHub Actions + local `lake build`
- axiom audit: reproducible via `lake build +JurisLean.AxiomAudit`

## Blocked

| Task | Reason | Minimal reproduction | Next route |
|---|---|---|---|
| Track B complete Banach closure | Complete-space + ContractingWith bridge not yet formalized | `legal-math-banach` worktree | Continue weighted metric route |

## Active worktrees

| Worktree | Track | Owner | Files owned |
|---|---|---|---|
| D:/Claude/数学证明/legal-math-modeling | A/C/D/E | main | master |
| D:/Claude/数学证明/legal-math-banach | B | Banach | track-b-banach |
| D:/Claude/数学证明/legal-math-prod | C | Prod Assurance | track-c-prod |

## Last verified commands

```text
# legal-math-modeling
cd D:\Claude\数学证明\legal-math-modeling\proofs\lean\juris_lean
lake build
lake build +JurisLean.AxiomAudit

cd D:\Claude\数学证明\legal-math-modeling
python scripts/scan_lean_guards.py proofs/lean/juris_lean/JurisLean

# juris-calculus
cd D:\Codex\juris-calculus
pytest -q

# deli-autoresearch
cd D:\Claude\数学证明自动研究
pytest -q
```

## Next runnable tasks

1. A2/C1: unify canonical fixtures, certificate payload, and independent checker registry
2. C0: enforce no-uncertainty-upgrade gate on grounded verification results
3. D1/D3: formalize impact analysis + incremental grounded fallback/full recompute equivalence
4. B0-B3: continue Banach worktree without blocking released formal core

## Legal final states

- NIGHT_RUN_COMPLETE
- NIGHT_RUN_PARTIAL
- FORMAL_CORE_RELEASED_BANACH_BLOCKED
- PRODUCTION_ASSURANCE_BLOCKED
- FAILED
