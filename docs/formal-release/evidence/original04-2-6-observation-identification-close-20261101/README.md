# Original questions 04.2 and 04.6 — observation and identification evidence

This shared package records module-level source evidence for frozen original-question rows 04.2 (L97/L99/L101) and 04.6 (L129/L131/L133). The handoff rows are candidate `COVERED` updates; this is not full-record acceptance.

## Actual changed-module run

Run `41264181836`, attempt 1, job `124723412599`, built subject `de4f05017b9123ee8c8dd7a3adba5e2aa3245c84` / tree `657504126b47f58a5939a9cc9f4bae008346feba`. Artifact `changed-module-only-41264181836-1` was 4,249 bytes with SHA256 `faa544eebbbd18c413d6864ab807f76e9fdef1b1b70de540ecfb182e4400c6e4`. The actual plan scope is `CURRENT_AND_REVERSE_DEPENDENTS_NOT_PROOF_ACCEPTANCE`; its requested audit driver has 15 `#check` and 15 `#print axioms` outputs: 12 new declarations and 3 reused declarations. All 15 axiom blocks list only `propext`, `Classical.choice`, and `Quot.sound`; no `sorryAx` or errors. Other full-release jobs were skipped. The complete actual build log is copied byte-for-byte to `axiom-audit.raw.txt`; exact hashes and declaration line maps are in `verification.json`.

The release-root source-core is `4bfc276d7f20adcdec6e323c53c46d93664c61b0` / tree `c02837471cd0ea2a4dea510a09a87edc472391ef`; it only admits these three modules through the generated root imports. The module evidence itself remains bound to the earlier changed-module subject/tree above.

## Frozen-clause mapping

- **04.2 L97:** The existing observation-unit/source contract is kept distinct from file count. Source identity, target, mechanism, and unit semantics remain external premises; a row label or duplicate file does not prove them.
- **04.2 L99:** `ten_copies_of_declared_marginal` proves the stated ten-copy event has likelihood `theta` from its declared marginal. `ten_independent_of_declared_marginals` proves `theta^10` only from the explicit `iIndepFun` and each-coordinate marginal premises. The concrete copy, Pi-law, and shared-Bool-cause results are finite instances; distinct identifiers do not establish real-world independence.
- **04.2 L101:** The three reused declarations preserve generated sigma-information, conditional expectations up to a.e. equality, and unchanged deterministic-copy likelihood. They do not say new measurements carry no information.
- **04.6 L129:** The existing continuous-uniform source is instantiated with `[0,1]` and `(0,1]`: both have probability one, but the endpoint makes the universal statement differ.
- **04.6 L131:** `Function.FactorsThrough` gives the fixed-observation-law/target definition. The copied-versus-independent law result addresses mechanism mismatch; the reused original04.4 endpoints address distinct targets under the same observation law. The quarter-parameter finite example separates structural identification from nonzero one-sample error. Candidate mechanisms may vary; no shared-mechanism premise is added.
- **04.6 L133:** The existing six-question and local-premise analysis is retained with these named results. Existing Beta, selection, contamination, and sharp-bound results are cited only under their original stated premises; this package does not reprove them or infer likelihood from counts.

## Evidence boundary

The package records named module results and source-module CI only. Exact-subject full-release PR checks, certificate/reference byte reconciliation, independent repository verifier, merge, and post-merge checks remain pending. It does not certify real-world source identity, sampling mechanism, independence, legal truth, actual consumer execution, or broader theoretical completion. U50 remains `50 wiring / 0 narrow / 0 open`; global discharges, Step 2, and math_flip remain false.
