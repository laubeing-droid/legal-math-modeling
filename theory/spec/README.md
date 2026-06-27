# Architectural Specifications

Files in this directory are model specifications and architectural catalogs, not standalone proofs.

## Purpose

These files stabilize semantics before `juris-calculus` implements them. They are intentionally not a production runtime.

## Specification Files

| File | Purpose |
|------|---------|
| `canonical_semantics.py` | Canonical semantic vocabulary shared by formal specifications, reference semantics, and downstream runtime bridges |
| `reference_semantics.py` | Transparent oracle-style evaluator for early vertical slices |
| `ddl_core.py` | Minimal deontic core covering modality, violation, reparation, exception, and burden-of-proof semantics |
| `horn_aaf_contract.py` | Machine-testable contract for the Horn to AAF boundary |
| `certificate_schema.py` | Certificate payload and independent checker boundary |

## Relationship to Lean Formalization

The 11 spec types defined here connect to the Lean formalization:

| Spec Type | Lean Module |
|-----------|-------------|
| LegalFact | HornDefinitions.lean |
| LegalRule | HornDefinitions.lean |
| LegalNorm | UnifiedModel.lean |
| LegalClaim | JC_Formalization.lean |
| Argument | DungDefinitions.lean |
| Attack | DungDefinitions.lean |
| Priority | DungAAF.lean |
| Violation | UnifiedModel.lean |
| Reparation | UnifiedModel.lean |
| DecisionStatus | JC_Formalization.lean |
| ProofTrace | AxiomAudit.lean |

## Formal Baseline

The Lean formalization provides the verified mathematical core:

- 94 theorems (43 core + 51 supporting), 0 sorry
- 25 Lean files, 2954 build jobs
- AxiomAudit ensures no sorry and no custom axioms

## Rules

- Specifications here are architectural catalogs, not proofs
- Do not cite spec files as formal verification
- Implementation must be validated against the Lean formalization
