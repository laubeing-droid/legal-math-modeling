# Executable Specification Modules

This package contains Python representations and checkers for the repository's typed specification boundary.

Key areas include:

- `canonical_v2/`: the 48-type layered registry, migrations, and type definitions;
- `canonical_semantics.py`: v1 compatibility for the 11 public names;
- `ddl_core.py`: executable bounded deontic behavior;
- `horn_aaf_contract.py`: Horn-to-AAF witness validation;
- `certificate_schema.py`: certificate envelopes and independently recomputed predicates;
- source, temporal, proposal, receipt, translation, numeric, and backend contracts.

The Python modules are executable specifications and checker implementations. Their tests establish bounded engineering behavior; they are not Lean proofs. Corresponding Lean statements, when present, remain authoritative for formal claims.

Start with [Canonical Legal Schema](../../docs/spec/canonical_legal_schema.md), [Certificate Checker Boundary](../../docs/spec/certificate_checker_boundary.md), and the full Python tests. Unknown versions, missing evidence, unstable identifiers, invalid digests, and unsupported status transitions fail closed.
