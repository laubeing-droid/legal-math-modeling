# FORBIDDEN CLAIMS

**Date:** 2026-06-28
**Authority:** `legal-math-modeling` (this repo)

---

The following statements are currently FALSE and MUST NOT appear in README,
release notes, paper abstracts, repository introductions, or any public
communication.

---

## 1. Explicitly Forbidden

1. "The entire `juris-calculus` Python implementation has been formally proven by Lean."
2. "The four-stage pipeline composition correctness is fully formally closed."
3. "Banach fixed-point closure is complete and merged into formal core."
4. "Differential privacy guarantees have been established."
5. "The 38 constants have been calibrated with real data."
6. "Litigation automation and research automation have been completed by this repository."
7. "Archive tags represent active release branches."
8. "`UnifiedModel.lean` equals production end-to-end correctness theorem."
9. "The unified mathematical model is fully closed to Banach/DP/all future layers."
10. "Simply adding more theorems brings the project closer to product success."

---

## 2. Precise Replacement Language

### For `legal-math-modeling`

Write instead:

> The formal core of the finite monotone iteration system, Dung grounded
> fixed-point layer, and finite Horn closure layer has completed repository-level
> formal release closure. Banach remains an independent unproved research track.

### For the Engineering Layer

Write instead:

> Lean has proven the mathematical specification boundary. The Python engineering
> implementation continues to converge via testing, certificate verification, and
> refinement baselines, but has NOT been formally proven by this repository as a whole.

### For Banach

Write instead:

> Banach-related work is retained only as an archived research track.
> It is NOT part of `formal-core-v1`.

### For UnifiedModel

Write instead:

> `UnifiedModel.lean` is an independent composition proof (Kripke -> Horn -> AAF -> Banach).
> It is NOT on the blocking path. It does NOT represent production end-to-end correctness.
> It is currently imported by `JurisLean.lean` (umbrella build), but its `Argument` type
> (Nat-based) is NOT the canonical `Argument` (which uses ArgumentId-based semantics
> defined in `canonical_semantics.py`).

### For the Mathematical Endpoint

Write instead:

> The current mathematical endpoint is `spec-first-transition-ready`, not
> "all math is done." Subsequent mathematical work flows back as "support for
> JC new capabilities" and is no longer mainline research expansion.

---

## 3. Branch and Archive Policy

Current public branch model:

- Only `master` is retained as a public branch

Archive tags:

- `archive/banach-track-b-d23e8f2`
- `archive/track-c-prod-f43e273`

These tags exist for traceability only. They do NOT expand the current release claim.

---

## 4. Why These Claims Are Forbidden

| Claim | Why Forbidden |
|-------|--------------|
| "juris-calculus fully proven" | Only the mathematical specification layer is Lean-proven. The Python runtime is NOT formally proven end-to-end. |
| "Four-stage composition proven" | Each stage has separate proofs (or Python verification). The pipeline composition is an engineering contract, not a Lean theorem. |
| "Banach complete" | Banach files exist in the repo but are in archived research status. `BanachFixedPoint.lean` theorems depend on deferred proofs. |
| "UnifiedModel = production" | `UnifiedModel.lean` defines its own `Argument` (Nat-based), not the canonical type. It is a standalone research composition, not a production artifact. |
| "Adding theorems = closer to product" | Mathematical completeness and product readiness are orthogonal. The repo can be mathematically complete without being a product. |

---

## 5. Enforcement

- Any PR that introduces a forbidden claim in README, release notes, or
  public docs MUST be blocked.
- The `FORBIDDEN_CLAIMS.md` file is checked during the spec-first transition
  gate (M5: Unified Stopping Statement).
- If a new forbidden claim pattern is identified, it MUST be added to this
  document before the next release.
