# Documentation Index

This index is the authoritative map of current repository documentation. Reports under `reports/` and deleted historical templates remain available through Git history but are not current evidence.

## Authority order

When documents disagree, use this order:

1. source code and machine-readable schemas;
2. CI artifacts bound to an exact subject commit and tree;
3. current release and specification documents linked below;
4. papers and explanatory prose;
5. archived reports and Git history.

No narrative document can upgrade `UNKNOWN`, `SKIP`, `TIMEOUT`, stale evidence, or a subject mismatch into PASS.

The `master-plan/` construction ledger organizes work and freezes design baselines at the narrative level. It does not override the authority order above: source code, machine-readable schemas, and CI artifacts remain authoritative over it.

## Start here

| Reader | Documents |
|---|---|
| Repository user | [English README](../README.md), [中文 README](../README_CN.md), [public/private boundary](disclosure/PUBLIC_PRIVATE_BOUNDARY.md) |
| Release reviewer | [immutable evidence snapshot](formal-release/FINAL_FORMAL_RELEASE_REPORT.md), [release protocol](formal-release/FORMAL_RELEASE_REPORT.md), [certificate schema](formal-release/CERTIFICATE_SCHEMA_V2.md), [axiom boundary](formal-release/axiom_audit.md) |
| Claim reviewer | [allowed claims](formal-release/ALLOWED_CLAIMS.md), [forbidden claims](formal-release/FORBIDDEN_CLAIMS.md) |
| Model implementer | [canonical schema](spec/canonical_legal_schema.md), [DDL core](spec/ddl_minimal_core.md), [Horn-to-AAF contract](spec/horn_to_aaf_contract.md), [certificate checker](spec/certificate_checker_boundary.md) |
| Cross-repository integrator | [authority map](remediation/authority_map.md), [runtime refinement evidence](remediation/runtime-refinement/evidence.md) |
| Research reader | [paper corpus](../paper/README.md), [rewrite handoff](paper-rewrite/HANDOFF.md) |
| Paper rewrite contributor | [progress ledger](paper-rewrite/PROGRESS.md), [Chinese manuscript](paper-rewrite/paper_cn.md), [English manuscript](paper-rewrite/paper_en.md) |
| Construction executor | [master plan](master-plan/00_施工总纲.md)（施工总纲·冻结基线）, [numbered ledger](master-plan/01_编号台账.md)（编号台账） |
| Contributor | [proof artifacts](../proofs/README.md), [Lean boundary](../proofs/lean/README.md), [executable specs](../theory/spec/README.md), [data boundary](../data/README.md), [program plan](../program/PLANS.md) |

## Current document inventory

| Path | Role | Evidence class |
|---|---|---|
| `formal-release/SEVEN_AXIS_LANDING_REPORT_20260911.md` | Exact snapshot for run 34669383636 (current head) | Immutable-run report |
| `formal-release/FINAL_FORMAL_RELEASE_REPORT.md` | Exact snapshot for run 33946211096 (prior subject) | Immutable-run report |
| `formal-release/FORMAL_RELEASE_REPORT.md` | Stable release pipeline and interpretation | Process contract |
| `formal-release/CERTIFICATE_SCHEMA_V2.md` | Certificate fields and gate rule | Schema contract |
| `formal-release/axiom_audit.md` | Permitted Lean foundation dependencies | Formal boundary |
| `formal-release/ALLOWED_CLAIMS.md` | Claims supported by named evidence | Claim policy |
| `formal-release/FORBIDDEN_CLAIMS.md` | Overclaims the repository rejects | Claim policy |
| `spec/canonical_legal_schema.md` | v1/v2 type universe | Model specification |
| `spec/ddl_minimal_core.md` | Four-modality DDL semantics | Model specification |
| `spec/horn_to_aaf_contract.md` | Bounded translation witness | Model specification |
| `spec/certificate_checker_boundary.md` | Certificate/checker separation | Verification specification |
| `remediation/authority_map.md` | Which artifact decides each question | Governance contract |
| `remediation/runtime-refinement/evidence.md` | Current three-fixture cross-repo evidence | Engineering evidence |
| `disclosure/PUBLIC_PRIVATE_BOUNDARY.md` | Repository disclosure boundary | Scope contract |
| `paper-rewrite/HANDOFF.md` | Rewrite execution package and claim ceiling | Working contract |
| `paper-rewrite/PROGRESS.md` | Rewrite progress, audit corrections, external evidence pointers | Dynamic ledger |
| `paper-rewrite/paper_cn.md` | Rewrite manuscript, Chinese (sections 1–3 of 9) | Working manuscript |
| `paper-rewrite/paper_en.md` | Rewrite manuscript, English (sections 1–3 of 9) | Working manuscript |
| `ontology/core_ontology.yaml` | Public boundary of the legal core ontology (11 v1 types; input-admission rules) | Model specification |
| `history/` | Archived superseded docs: v2.1 spec, 20260701 rewrite record, full-math originals | Historical only |
| `history/evidence-archive/` | Debate & evidence archive migrated from the retired cloud folder: four-reports, 20-round debates, distillation audits, wave4 book evidence, concept genealogy v1/v2, baseline copies | Historical evidence (sources for master-plan baselines) |
| `master-plan/00_施工总纲.md` | Construction master plan; frozen baseline = object definition v3 + 7-layer skeleton | Working contract (construction ledger) |
| `master-plan/01_编号台账.md` | Numbered construction ledger (TY/RC/EV/PR/RT/NN/AC/ON/LH pools) | Working contract (construction ledger) |
| `master-plan/基线/对象定义v3_冻结版_20260925.md` | Frozen legal-semantic-core object definition (5-round audit, R5 verdict: 收束) | Working contract (baseline) |
| `master-plan/基线/法律统一概念体系全量方案_v1.md` | Full concept system: 131 concepts, 16 requirement families, 37 defined terms | Working contract (baseline) |
| `master-plan/基线/法律概念谱系总录_v2.md` | Concept genealogy v2.1 with household rules and audit corrections | Reference (source for ON pool) |
| `history/documentation_rewrite_20260701.md` | Prior rewrite record | Historical only |

The 2026-07-01 audit record is retained to explain provenance. It does not describe the current document tree and cannot override this index.
