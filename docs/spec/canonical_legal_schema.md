# Canonical Legal Schema

**Date:** 2026-07-01
**Status:** CLOSED_FOR_FOUR_SLICES
**Gate M1:** CLOSED_FOR_FOUR_SLICES
**Authority:** `legal-math-modeling`

## Purpose

This document records the canonical semantic vocabulary shared by the Lean
four-slice formal model, Python reference semantics, and downstream
`juris-calculus` shadow fixtures.

The scope is deliberately narrow: contract breach, license, permission, and
priority. It is not a full legal ontology and it is not a proof of the complete
Python runtime.

## Lean Canonical Types

`proofs/lean/juris_lean/JurisLean/LegalSyntax.lean` defines the canonical Lean
types required by the four-slice Playbook:

| Required type | Lean artifact |
|---|---|
| `FactId` | `LegalSyntax.lean` |
| `RuleId` | `LegalSyntax.lean` |
| `Party` | `LegalSyntax.lean` |
| `Claim` | `LegalSyntax.lean` |
| `Evidence` | `LegalSyntax.lean` |
| `Norm` | `LegalSyntax.lean` |
| `Obligation` | `LegalSyntax.lean` |
| `Permission` | `LegalSyntax.lean` |
| `Prohibition` | `LegalSyntax.lean` |
| `Defense` | `LegalSyntax.lean` |
| `Exception` | `LegalSyntax.lean` |
| `Priority` | `LegalSyntax.lean` |
| `Argument` | `LegalSyntax.lean` |
| `Attack` | `LegalSyntax.lean` |
| `DecisionStatus` | `LegalSyntax.lean` |
| `Certificate` | `LegalSyntax.lean` |
| `TrustLabel` | `LegalSyntax.lean` |

## Python Canonical Types

The Python reference layer remains in `theory/spec/canonical_semantics.py`:

| Python type | Purpose |
|---|---|
| `CanonicalFact` | Atomic fact with stable `key` projection |
| `CanonicalRule` | Horn/exception/priority/constitutive rule |
| `CanonicalNorm` | Deontic norm with modality and violation payload |
| `CanonicalClaim` | Claim submitted to the argumentation layer |
| `CanonicalArgument` | Argument produced from rule and support facts |
| `CanonicalAttack` | Directed rebuttal/exception/priority defeat |
| `CanonicalPriority` | Priority relation |
| `CanonicalViolation` | Violation consequence |
| `CanonicalReparation` | Remedy payload |
| `DecisionStatus` | `PROVED`, `REFUTED`, `UNDECIDED`, `TAINTED` |
| `CanonicalProofTrace` | Auditable trace container |

## Proven Lean Schema Properties

`LegalSyntax.lean` proves:

- `fact_serialization_key_stable`
- `rule_serialization_key_stable`
- `decisionStatus_runtimeKey_injective`
- `trust_label_cannot_promote_status`
- `candidate_evidence_not_auditable`

These theorems close the Playbook requirements for stable serialization keys,
DecisionStatus/runtime one-to-one mapping, and trust-label non-promotion within
the four-slice formal model.

## Boundary

- `UnifiedModel.lean` still contains an independent Nat-based `Argument` for a
  research composition proof. It is not the canonical production `Argument`.
- LLM/source candidates remain candidates until a backend, source-span, or
  human-review evidence path verifies them.
- Trust labels restrict disclosure or trigger review; they do not promote legal
  conclusions.

## Verification

```powershell
cd proofs/lean/juris_lean
lake build JurisLean

cd ..\..\..
python -m pytest tests\spec\test_spec_transition.py -q
```
