# Architectural Specifications

Files in this directory are model specifications and architectural catalogs, not
standalone proofs.

Current specification-side anchors:

- `canonical_semantics.py`: canonical semantic vocabulary shared by formal
  specifications, reference semantics, and downstream runtime bridges. The
  implementation names use a `Canonical*` prefix to avoid collisions with older
  theory modules.
- `reference_semantics.py`: transparent oracle-style evaluator for early
  vertical slices
- `ddl_core.py`: minimal deontic core covering modality, violation,
  reparation, exception, and burden-of-proof semantics
- `horn_aaf_contract.py`: machine-testable contract for the Horn -> AAF
  boundary
- `certificate_schema.py`: certificate payload and independent checker boundary

These files are intentionally not a production runtime. Their purpose is to
stabilize semantics before `juris-calculus` implements them.
