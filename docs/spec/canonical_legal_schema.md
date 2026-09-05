# Canonical Legal Schema

## Two explicit layers

The schema has a v1 compatibility surface and a decisive v2 universe. They are related but not interchangeable.

The 11 v1 names are:

`LegalFact`, `LegalRule`, `LegalNorm`, `LegalClaim`, `Argument`, `Attack`, `Priority`, `Violation`, `Reparation`, `DecisionStatus`, and `ProofTrace`.

The v2 registry contains 48 distinct types divided into four layers:

- identity: stable identifiers and versioned references;
- source: source snapshots, provenance, authority, and temporal records;
- reasoning: facts, rules, norms, claims, arguments, attacks, priorities, exceptions, violations, and reparations;
- compilation: proposals, witnesses, certificates, traces, and checker-facing envelopes.

The exact type list and layer membership are executable in `theory/spec/canonical_v2/manifest.py` and mirrored in `proofs/lean/juris_lean/JurisLean/LegalModelV2.lean`. The Lean module proves registry coverage, preservation of v1 names, distinctness, and registry size. Documentation must not duplicate the full registry as a second authority.

## Status discipline

The schema distinguishes accepted, rejected, candidate, disputed, unknown, degraded, and failure states. A v1 payload may remain parseable for compatibility, but it does not acquire v2 decisive status merely by parsing.

Runtime metadata—such as used fact keys, rule identifiers, source snapshots, taint, downgrade reasons, conflict certificates, and review packets—explains a decision path. It does not become an additional canonical legal type and cannot promote unverified evidence.

## Boundary

- The schema supplies typed identities and contracts, not legal authority.
- Registry coverage is not proof that every real-world legal concept is represented.
- A stable identifier or digest proves binding, not truth.
- Downstream semantic changes must return to this repository rather than being introduced through documentation or runtime-only metadata.

The immutable CI evidence for the current documented snapshot is recorded in [Final Formal Release Report](../formal-release/FINAL_FORMAL_RELEASE_REPORT.md).
