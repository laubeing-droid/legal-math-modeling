# Certificate / Checker Boundary

**Date:** 2026-07-01
**Status:** CLOSED_FOR_FOUR_SLICES
**Gate M4:** CLOSED_FOR_FOUR_SLICES
**Authority:** `legal-math-modeling`

## Purpose

This document records the certificate/checker boundary for the four vertical
slices. The checker must fail closed on malformed, tainted, candidate-only, or
obligation-missing certificates.

This is a specification boundary, not a proof that the full `juris-calculus`
runtime is correct.

## Lean Artifacts

`proofs/lean/juris_lean/JurisLean/CertificateChecker.lean` defines:

- `CheckVerdict.accept`
- `CheckVerdict.reject`
- `CheckVerdict.undecided`
- `Certificate.hasStrongEvidence`
- `checkCertificate`

`proofs/lean/juris_lean/JurisLean/SafetyTheorems.lean` and
`proofs/lean/juris_lean/JurisLean/EndToEnd.lean` connect the checker to the
four vertical slices.

## Proven Fail-Closed Properties

`CertificateChecker.lean` proves:

- `malformed_certificate_rejected`
- `tainted_certificate_rejected`
- `candidate_evidence_not_accepted`
- `missing_required_facts_rejected`
- `missing_obligations_rejected`
- `checker_acceptance_requires_obligations`
- `checker_acceptance_requires_required_facts`
- `checker_acceptance_requires_non_candidate`

`SafetyTheorems.lean` proves:

- `candidate_cannot_enter_verified_fact_gate`
- `tainted_not_accepted_as_proved`
- `accepted_certificate_has_required_payload`
- `priority_missing_evidence_certificate_not_accepted`
- `priority_cycle_certificate_fail_closed`
- `license_outside_scope_not_permitted`
- `permission_conflict_not_forced_proved`

`EndToEnd.lean` proves per-slice acceptance/fail-closed theorems for contract
breach, license, permission, and priority.

## Python Checker Boundary

`theory/spec/certificate_schema.py` remains the transport/reference payload
checker. It validates:

- required payload fields,
- valid `DecisionStatus`,
- `TAINTED` fail-closed reason,
- decisive payloads carrying constructed arguments,
- accepted ids bounded by constructed arguments,
- priority defeat requiring attack records.

## Candidate Gate

LLM/source candidates cannot be upgraded into verified facts by the checker.
Candidate evidence is rejected at the Lean checker boundary and remains
non-auditable until a backend/source/human evidence path verifies it.

## Runtime Differential Evidence

`runtime/legal_math_four_slice_differential.json` records the local four-slice
reference/shadow fixture outcomes. JC must run its real runtime shadow harness
against the same fixture names in the JC stage.

## Verification

```powershell
cd proofs/lean/juris_lean
lake build JurisLean

cd ..\..\..
python -m pytest tests\spec\test_spec_transition.py -q
python -m theory.spec.runtime_differential --output runtime\legal_math_four_slice_differential.json
```
