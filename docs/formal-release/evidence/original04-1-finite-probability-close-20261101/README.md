# Original question 04.1 finite probability instances — evidence package

This package records the new named source module for frozen original-question 04.1 (L89, L91, L93). The row is a candidate C update in the handoff record; full-record PR acceptance is pending.

## Scope and source

The changed-module run `41257289665` (attempt 1, job `124703062623`) compiled the audit driver on subject `7b5a13729386ec30c3ad3c19441951c4f6c9b1fe`, tree `b5c8b211b2beb154bbff84b62044d44185f5e953`. It audited nine named declarations in `U04_1OriginalProbabilityInstances20261101`; all report only `propext`, `Classical.choice`, and `Quot.sound`, with no `sorryAx` or other axiom. The full actual log is preserved byte-for-byte in `axiom-audit.raw.txt`; hashes, artifact identity and source pins are in `verification.json`.

The declarations map to the frozen clauses as follows:

- **L89:** `two_couplings_same_marginals` and `two_couplings_different_joints` construct two couplings on the same finite space.
- **L91:** `probability_one_constraints_incompatible` applies the previously accepted `three_event_bounds` theorem to the stated inconsistent constraints.
- **L93:** `fixed_atom_measure_is_probability`, `fixed_atom_measure_singleton`, `fixed_atom_measure_injective`, `fixed_atom_measure_unique`, and `fixed_atom_measure_surjective` provide the fixed-label rational-weight/probability-measure bridge and its uniqueness. `normalized_scores_do_not_identify_target` shows that normalized scores alone do not identify the target law.

## Evidence boundary

This is successful changed-module evidence only. Full-record PR acceptance, exact-subject full release, certificate/reference reconciliation, independent verifier, merge and post-merge checks are pending. The package does not claim real-world dependence identification, uniqueness across different label representations, actual consumer wiring, or completion of other legal-mathematics obligations. The two earlier failed module runs remain recorded as failures in `verification.json`; this successful run is the later repaired source-module result. U50 archive accounting, the six designated cuts, engineering requirement states, and global discharges/Step 2/math_flip remain unchanged.
