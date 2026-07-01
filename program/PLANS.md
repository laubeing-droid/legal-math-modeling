# Execution Plan — legal-formal-assurance-v2

## Program

- program_id: legal-formal-assurance-v2
- current_track: A2 / C1
- current_task: Lean-to-Python refinement baseline + independent checker gate
- program_status: FORMAL_CORE_RELEASED

## Current Metrics

| Metric | Value |
|--------|-------|
| Lean theorems | 94 (43 core + 51 supporting) |
| sorry | 0 |
| Build jobs | 2954 |
| Lean files | 25 |
| Python modules | 59 |
| Spec types | 11 |

## Lean File Inventory (25 files)

AxiomAudit.lean, BanachCertificate.lean, BanachComplete.lean, BanachContraction.lean, BanachEffectiveNodes.lean, BanachFixedPoint.lean, BanachScratch.lean, BanachWeightedNorm.lean, Basic.lean, ContractionCondition.lean, DungAAF.lean, DungDefinitions.lean, DungFixedPoint.lean, FiniteGaloisAdjunction.lean, FiniteMonotoneIteration.lean, FiniteRosetta.lean, HornDefinitions.lean, HornFixedPoint.lean, HornOperationalRefinement.lean, JC_Formalization.lean, ScratchApi.lean, SupZeroLemma.lean, TemporalKripke.lean, UnifiedModel.lean, WeightedSupNorm.lean

## Completed

- [x] Phase 0: AGENTS.md (all 3 repos) + PLANS scaffold + .gitignore olean + Track B worktree
- [x] Phase 0.5: program/ control directory + MEGA_GOAL.md + PROGRAM_STATE.json + run-night.ps1 + schemas/
- [x] A0 test-count and clean-build audit
- [x] A1 formal-core release gate
- [x] Formal core: 94 theorems, 0 sorry, 2954 jobs

## In Progress

- [ ] A2 executable refinement baseline
- [ ] C0 pipeline no-upgrade gate
- [ ] C1 certificate soundness

## Blocked

| Task | Reason | Next Route |
|------|--------|------------|
| Track B complete Banach closure | Complete-space + ContractingWith bridge not yet formalized | Continue weighted metric route in `legal-math-banach` worktree |

## Pending

- [ ] B0 weighted metric completion
- [ ] B1 ContractingWith bridge
- [ ] B2 fixed-point and error bounds
- [ ] B3 BanachCertificate
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

## Active Worktrees

| Worktree | Track | Owner |
|----------|-------|-------|
| <legal-math-modeling-root> | A/C/D/E | main |
| <legal-math-banach-root> | B | Banach |

## Last Verified Commands

```bash
# Lean build
cd proofs/lean/juris_lean && lake build JurisLean

# Axiom audit
lake build +JurisLean.AxiomAudit

# Ghost file scan
python scripts/scan_lean_guards.py proofs/lean/juris_lean/JurisLean

# Python verification
python -m compileall -q theory/
python -m theory --summary
```

## Next Runnable Tasks

1. A2/C1: unify canonical fixtures, certificate payload, and independent checker registry
2. C0: enforce no-uncertainty-upgrade gate on grounded verification results
3. D1/D3: formalize impact analysis + incremental grounded fallback/full recompute equivalence
4. B0-B3: continue Banach worktree without blocking released formal core

## Legal Final States

- NIGHT_RUN_COMPLETE
- NIGHT_RUN_PARTIAL
- FORMAL_CORE_RELEASED_BANACH_BLOCKED
- PRODUCTION_ASSURANCE_BLOCKED
- FAILED
