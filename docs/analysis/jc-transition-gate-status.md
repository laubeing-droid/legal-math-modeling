# Jc Transition Gate Status

Status: rewritten on 2026-07-01 as a release-bounded repository document.

## Purpose

This file is a public documentation artifact for the `legal-math-modeling` repository. It records the current specification boundary, audit posture, or historical context for the `analysis` area without expanding the formal claim surface.

## Authority

Use this order of authority when resolving conflicts:

1. Lean source under `proofs/lean/juris_lean/JurisLean/` for formal statements.
2. Python tests and certificate fixtures for engineering regression evidence.
3. Machine-readable manifests under `docs/formal-release/` and `docs/audit/` for release bookkeeping.
4. Papers, reports, and history files for explanation only.

## Current Boundary

The repository is a mathematical companion and specification boundary. It supports the contract-breach, license, permission, and priority slices through canonical types, a minimal DDL core, a Horn-to-AAF contract, and a certificate/checker boundary. The documentation does not assert full runtime correctness.

## Allowed Claims

- This repository defines a specification and proof boundary for selected legal-reasoning structures.
- The four current slices are closed only within their canonical schema, DDL core, Horn-to-AAF contract, and certificate-checker boundary.
- Lean source files are the authority for formal statements; runtime correctness needs separate evidence.
- Reports and papers are explanatory artifacts, not proof certificates.
- Unknown, skipped, timed-out, or unavailable verification remains fail-closed.

## Prohibited Claims

- Do not claim that the full runtime is formally proved by Lean.
- Do not turn an LLM candidate into a verified fact without source-bound verification.
- Do not treat Python tests, sampled enumeration, or AI audit text as a Lean proof.
- Do not change DecisionStatus, checker acceptance, verified_fact gates, or attack/exception/priority semantics from documentation.
- Do not present stale reports as current release evidence.

## Verification Rule

A claim is current only if it can be traced to a source file, a machine-readable manifest, and a local or CI command that ran on the relevant commit. If evidence is missing, stale, skipped, timed out, or unavailable, the status is fail-closed.

## Maintenance Notes

- Keep this file source-bounded.
- Do not import private client data or commercial workflow details.
- Do not use this file to alter formal semantics.
- Update this file after source, manifest, or release-gate changes.
