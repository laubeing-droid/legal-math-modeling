# History Archive Guide

`docs/history/` is an archive of the project's development history, not the current release boundary.

## Purpose

Use this directory for:

- Phase summaries and development logs
- Earlier modeling assumptions and their evolution
- Methodology notes on machine provability
- Historical Socratic audit snapshots

Do not use this directory as the source of current release claims.

## Current Truth Sources

For current status, read these instead:

1. `docs/modeling/02_逆向工程审计.md` — Lean audit results
2. `docs/modeling/06_第四阶段验证_cn.md` — Verification results
3. `program/PLANS.md` — Current program state

## Archive Files

| File | Content |
|------|---------|
| `development_log_20260523_0614.md` | Early-phase modeling and audit archive (May-June 2026) |
| `development_log_20260616_0617.md` | Repository creation and first-release archive |
| `llm_machine_provability.md` | Historical methodology note on machine-provability assumptions |
| `socratic_200_rounds.md` | First 200-round Socratic audit summary archive |
| `socratic_200_rounds_deep.md` | Second 200-round deep audit summary archive |

## Project Timeline

| Period | Key Events |
|--------|------------|
| 2026-05-23 ~ 2026-06-14 | Initial legal math modeling, first theorem/counterexample structures, early alignment attempts |
| 2026-06-16 ~ 2026-06-17 | Repository creation from experimental materials, first README and release structure |
| 2026-06-17+ | Formal core development: 94 theorems, 0 sorry, 25 Lean files, 59 Python modules |
| 2026-06-28 | Current: FORMAL_CORE_RELEASED status |

## Staleness Rule

Historical files may contain:

- Older theorem counts (before final audit settled on 94)
- Earlier Banach assumptions (before formalization)
- Pre-release branch references
- Ambitions later downgraded by audit

Those statements are preserved as historical context only.

## Current Project Metrics

| Metric | Value |
|--------|-------|
| Lean theorems | 94 (43 core + 51 supporting) |
| sorry | 0 |
| Build jobs | 2954 |
| Lean files | 25 |
| Python modules | 59 |
| Spec types | 11 |
