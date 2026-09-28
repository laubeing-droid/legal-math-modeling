/-
External port (EXTERNAL-PORT-PROVENANCE-V1).
Upstream: https://github.com/elazarg/fixed-point-theorems-lean4
Revision: 42d4b401f7b6a6520e3bac3a76b8538d7f47ba3e
Upstream file: FixedPointTheorems.lean
License: MIT (see JurisLean/External/PROVENANCE.md for the notice).

This copy differs from the revision above in exactly two ways: this
header block, and `import` module paths rewritten to the
`JurisLean.External.*` roots. Statements and proofs are unchanged;
tests/spec/test_external_port_provenance.py re-derives the upstream
bytes from this file and checks the recorded sha256.
No build attestation is claimed here: the first compile of this port
is booked in PENDING_CI_MODULES (scripts/ci/check_import_reachability.py)
and only a green CI run of a commit containing this file can attest it.
-/
-- This module serves as the root of the `FixedPointTheorems` library.
-- Import modules here that should be built as part of the library.
import JurisLean.External.FixedPointTheorems.brouwer
import JurisLean.External.FixedPointTheorems.kakutani
