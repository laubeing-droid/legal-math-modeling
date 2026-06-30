# Horn -> AAF Contract

**Date:** 2026-07-01
**Status:** CLOSED_FOR_FOUR_SLICES
**Gate M3:** CLOSED_FOR_FOUR_SLICES
**Authority:** `legal-math-modeling`

## Purpose

This document records the contract from Horn derivations to AAF arguments and
attacks for the four vertical slices: contract breach, license, permission, and
priority.

The contract does not claim a full Lean proof of the Python runtime. It states
the semantic boundary that runtime shadow fixtures must preserve.

## Lean Artifacts

`proofs/lean/juris_lean/JurisLean/HornAAFContract.lean` defines:

- `HornDerivation`
- `compileHornArgument`
- `compileExceptionAttack`
- `compilePriorityDefeat`
- `checkerAcceptsArgument`

It proves:

- `horn_derivation_to_argument_conclusion`
- `horn_derivation_to_argument_supported`
- `exception_fact_to_attack_kind`
- `priority_defeat_to_attack_kind`
- `no_unsupported_argument_accepted`

`AttackDecision.lean` proves priority-specific safety properties:

- `priority_defeat_requires_active`
- `priority_defeat_requires_evidence`
- `missing_priority_evidence_no_defeat`
- `self_attack_not_priority_defeat`
- `priority_cycle_symmetric`

## Existing Core Foundation

The general Horn and Dung fixed-point layers remain the core mathematical
foundation:

| Layer | Lean files |
|---|---|
| Horn closure | `HornDefinitions.lean`, `HornFixedPoint.lean` |
| Dung grounded extension | `DungDefinitions.lean`, `DungFixedPoint.lean` |
| finite monotone iteration | `FiniteMonotoneIteration.lean` |

## Python Contract

`theory/spec/horn_aaf_contract.py` checks:

- all arguments trace to closure facts,
- all attacks refer to known argument ids,
- exception attacks carry an explicit defeat direction,
- exception and rebuttal are distinguishable when both appear,
- priority defeat is explicit in the AAF attack layer,
- accepted ids are bounded by constructed arguments.

`theory/spec/reference_semantics.py` uses this contract in the four-slice
reference evaluators.

## Four-Slice Closure

| Slice | Horn -> AAF contract evidence |
|---|---|
| contract breach | breach argument exists; force-majeure exception attack can defeat it |
| license | license permission argument and unauthorized-use argument are separated; priority defeat is explicit |
| permission | permission does not become obligation; unresolved conflict can remain `UNDECIDED` |
| priority | missing evidence, cycle, and self-attack do not default to a winner |

## Runtime Differential Evidence

`runtime/legal_math_four_slice_differential.json` records the local reference
and same-name JC shadow fixture expectations. The JC repo must consume these
fixture names in its real runtime shadow stage.

## Boundary

- Horn closure does not resolve legal conflict.
- Exception and priority become AAF attacks, not Horn facts.
- Unsupported arguments cannot be accepted by the checker.
- Priority evidence is required before a priority defeat can decide a result.
- This file does not prove the complete runtime implementation.

## Verification

```powershell
cd proofs/lean/juris_lean
lake build JurisLean

cd ..\..\..
python -m pytest tests\spec\test_spec_transition.py -q
python -m theory.spec.runtime_differential --output runtime\legal_math_four_slice_differential.json
```
