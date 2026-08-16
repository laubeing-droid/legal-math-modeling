# Authority Map (M0)

Status: M0 baseline artifact, 2026-08-16. Bound to branch
`codex/lmm-theory-absorption-plan` at planning HEAD `348e471`.

This map fixes which artifact is authoritative for which claim. When two
sources disagree, the higher-ranked source wins. Anything not listed here
has no authority and must be treated as explanatory.

## Execution Authority

| Domain | Authority | Notes |
|---|---|---|
| Lean build, module checks, axiom audit | GitHub Actions on the exact subject commit/tree | Local Lean/Elan/Lake execution is forbidden; local static results are provisional only |
| Python contract/mutation tests | CI full suite; local runs are provisional pre-checks | Collection manifest plus full log must be CI artifacts |
| Formal release certificate | CI-generated `formal-release-certificate.json` + independent verifier report | Never self-signed by the same commit without CI evidence |

## Formal Semantics Authority

| Subject | Authority | Scope |
|---|---|---|
| Canonical semantic vocabulary | `theory/spec/canonical_semantics.py` (v1 compat) and `theory/spec/canonical_v2/` (decisive) | v1 never gains v2 decisive status |
| Four-slice DDL statements | `proofs/lean/juris_lean/JurisLean/DDLDefinitions.lean` | four-slice minimal DDL model only |
| Dung grounded fixed point | `JurisLean/DungFixedPoint.lean` | proven core; rewrite only on counterexample or build failure |
| Horn least fixed point | `JurisLean/HornFixedPoint.lean` | proven core |
| Finite monotone iteration | `JurisLean/FiniteMonotoneIteration.lean` | proven core |
| Weighted sup norm | `JurisLean/WeightedSupNorm.lean` | proven core |
| Certificate/checker boundary | `theory/spec/certificate_schema.py` v2 + planned `CertificateCheckerV2.lean` | v1 payload parseable, never decisive |
| Translation witness contract | `theory/spec/translation_witness.py` + planned `TranslationWitness.lean` | per-hop omission/spurious/direction |
| Runtime refinement verdict | `theory/spec/runtime_differential.py` receipt verifier | external actual receipts only |

## Provenance Authority

| Claim type | Source of truth |
|---|---|
| Lean source/theorem counts | Generated inventory (`scripts/generate_formal_release_certificate.py`) at the subject commit; never copied from reports or memory |
| Forbidden-token guard | `scripts/scan_lean_guards.py` output in CI |
| Toolchain/deployment pins | `lean-toolchain`, `lake-manifest.json`, workflow digests inside the release certificate |
| Allowed/forbidden claims | `docs/formal-release/ALLOWED_CLAIMS.md`, `docs/formal-release/FORBIDDEN_CLAIMS.md` |

## Non-Authority (explanatory only)

- Papers, `paper/`, `docs/history/`, and narrative reports.
- `proofs/engineering_proof_artifacts/` Python demonstrations: backend health only,
  never a substitute for Lean theorems.
- Local `.lake` directories, local object files, and local build caches: acceptance
  contamination if produced locally; they exist in this checkout from pre-boundary
  sessions, remain git-ignored, and are never evidence.
- Superseded plan `260810_legal-math-modeling必要补充施工方案.md`: historical input only.

## Fail-Closed Rule

UNKNOWN, TIMEOUT, SKIP, NOT_RUN, BACKEND_UNAVAILABLE, ERROR, and CI_NOT_RUN all
block the dependent Gate. No status may be promoted by narrative, confidence,
consensus, or repeated runs.
