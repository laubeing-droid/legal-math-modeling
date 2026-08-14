# Certificate Checker Boundary

## Version boundary

`spec-cert-v1` remains parseable for historical consumers. It cannot obtain a v2
decisive verdict. `spec-cert-v2` is the only content-bound decisive envelope.

The v2 producer supplies content, identifiers, and claimed digests. The independent
checker recomputes:

- expected facts are a subset of used facts;
- expected obligations are a subset of discharged obligations;
- accepted arguments exist in the constructed argument set;
- argument rules and support facts exist in the bound payload;
- every source snapshot, rule pack, trace, and full certificate digest matches;
- identifiers and serialization order are unique and deterministic;
- semantics and checker versions are known;
- evidence is verified and not a candidate;
- the trace is non-empty and indexed consecutively.

Unknown schema/semantics/checker versions, empty traces, stale source snapshots,
digest mismatches, missing facts or obligations, duplicate identifiers, unstable
ordering, candidate evidence, and malformed attacks return `UNDECIDED` or `TAINTED`.
They never produce a decisive acceptance.

## Lean boundary

Lean models digest obligations as equality between expected and observed digest
identifiers. Lean theorems establish implications from checker acceptance to those
content-binding premises. They do not prove SHA-256, Python serialization, a producer,
an external runtime, source authority, or a substantive legal conclusion.

## Claim limit

A verified certificate proves that the named checker accepted the bound payload under
the named schema and semantics. It does not prove the complete juris-calculus runtime,
translation completeness outside the declared fixture language, or legal correctness.
