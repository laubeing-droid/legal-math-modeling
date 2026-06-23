# Execution Plan -- legal-formal-assurance-v2

## Program

- program_id: legal-formal-assurance-v2
- run_id:
- started_at:
- current_track:
- current_task:
- program_status: INFRA_READY

## Repository heads

- legal-math-modeling: 105120a
- juris-calculus: e73e635
- deli-autoresearch: c759474

## Completed

- [x] Phase 0: AGENTS.md (all 3 repos) + PLANS.md scaffold + .gitignore olean + Track B worktree
- [x] Phase 0.5: program/ control directory + MEGA_GOAL.md + PROGRAM_STATE.json + run-night.ps1 + schemas/
- [ ] A0 test-count and clean-build audit
- [ ] A1 formal-core release gate
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

## Blocked

| Task | Reason | Minimal reproduction | Next route |
|---|---|---|---|
| (none yet) | | | |

## Active worktrees

| Worktree | Track | Owner | Files owned |
|---|---|---|---|
| D:/Claude/数学证明/legal-math-modeling | A/C/D/E | main | master |
| D:/Claude/数学证明/legal-math-banach | B | Banach | track-b-banach |
| D:/Claude/数学证明/legal-math-prod | C | Prod Assurance | track-c-prod |

## Last verified commands

```text
# legal-math-modeling
cd D:\Claude\数学证明\legal-math-modeling
lake build  # 0 errors
rg -n "\bsorry\b|\badmit\b|\baxiom\b" proofs/lean/juris_lean/JurisLean/

# juris-calculus
cd D:\Codex\juris-calculus
pytest --collect-only -q  # 262 collected, 4 errors

# deli-autoresearch
cd D:\Claude\数学证明自动研究
pytest -q  # 65 collected
```

## Next runnable tasks

1. A0: Fix juris-calculus 4 collection errors, run full 262-test suite
2. A0: Clean build + axiom audit + theorem manifest
3. C0: Define CompletionStatus enum + StageResult + no-uncertainty-upgrade contract
4. B0 (parallel worktree): Build environment setup for Banach Analysis imports

## Legal final states

- NIGHT_RUN_COMPLETE
- NIGHT_RUN_PARTIAL
- FORMAL_CORE_RELEASED_BANACH_BLOCKED
- PRODUCTION_ASSURANCE_BLOCKED
- FAILED
