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

## Start here

| Reader | Documents |
|---|---|
| Repository user | [English README](../README.md), [中文 README](../README_CN.md), [public/private boundary](disclosure/PUBLIC_PRIVATE_BOUNDARY.md) |
| Release reviewer | [immutable evidence snapshot](formal-release/FINAL_FORMAL_RELEASE_REPORT.md), [release protocol](formal-release/FORMAL_RELEASE_REPORT.md), [certificate schema](formal-release/CERTIFICATE_SCHEMA_V2.md), [axiom boundary](formal-release/axiom_audit.md) |
| Claim reviewer | [allowed claims](formal-release/ALLOWED_CLAIMS.md), [forbidden claims](formal-release/FORBIDDEN_CLAIMS.md) |
| Model implementer | [canonical schema](spec/canonical_legal_schema.md), [DDL core](spec/ddl_minimal_core.md), [Horn-to-AAF contract](spec/horn_to_aaf_contract.md), [certificate checker](spec/certificate_checker_boundary.md) |
| Cross-repository integrator | [authority map](remediation/authority_map.md), [runtime refinement evidence](remediation/runtime-refinement/evidence.md) |
| Research reader | [paper corpus](../paper/README.md) |
| Contributor | [proof artifacts](../proofs/README.md), [Lean boundary](../proofs/lean/README.md), [executable specs](../theory/spec/README.md), [data boundary](../data/README.md), [program plan](../program/PLANS.md) |

## Current document inventory

| Path | Role | Evidence class |
|---|---|---|
| `formal-release/FINAL_FORMAL_RELEASE_REPORT.md` | Exact snapshot for run 33946211096 | Immutable-run report |
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
| `audit/documentation_rewrite_20260701.md` | Prior rewrite record | Historical only |

The 2026-07-01 audit record is retained to explain provenance. It does not describe the current document tree and cannot override this index.
