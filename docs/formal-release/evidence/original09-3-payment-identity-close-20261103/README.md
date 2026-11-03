# Original 09.3: source-controlled payment identity and single use

**Disposition:** Candidate source evidence maps frozen 09.3 clauses U02.2/U09.1 (L155–160, including L157 and L159) to the named source-key bridge, single-use trace theorem, and three finite ledger cases. Full PR acceptance and the same-C verifier remain pending.

## Source evidence

The changed-module build is bound to source checkpoint `2c07cdb41bd317bed458589265e2a30a5e747597` / tree `ce5ae4c3043c60f5f371fc934b94d9b465074937`, run `41636538195:1`, job `125919056100`, Artifact `changed-module-only-41636538195-1`, ID `13230991770`. The artifact's API digest, ZIP, raw log, module plan, member bytes, and nine source pins are recorded in `verification.json`; the raw log and plan are included byte-for-byte. This is a changed-module source result, not full-PR acceptance.

The frozen contract supplies the payment identity mapping. `source_request_keeps_actual_key_payload_and_identity` shows that the actual source request carries its bound payment key, payload, and interpreted identity. `u09_1_actual_trace_at_most_once` supplies at-most-once behavior for repeated committed effects under the same key and valid trace path. `u09_writeU_on_committed_applicable` gives the exact used-set insertion in its second result; `consume_committed_origin` connects the committed outcome to the actual ledger post. These results instantiate the stated identity contract; they do not discover or verify real-world aliases.

The two new source results are `sourced_calls_with_same_payment_id_are_at_most_once` and `finite_payment_identity_and_retry_outcomes`, alongside 15 named reused results. The finite examples use a synthetic token-to-PaymentId map only:

- For one token with its canonical PaymentId, a later table request with a different key but the same interpreted payment remains pending with `identityUnknown`; post and used set are unchanged.
- Two distinct synthetic PaymentIds sharing a cash event identifier are rejected as `duplicateCash`; post and used set are unchanged. This is not a replay case.
- A changed attempt with the same key and payload replays the original receipt; it does not commit again or change post/used set.

Unknown identity/applicability remain pending under the existing contracts. An unknown commit result has no determined post; it is not evidence that the payment did not occur. The examples do not claim that every real payment succeeds, that physical aliases can be recognized, or that external source identity is truthful.

## Failure history and boundaries

R1 run `41635146188:1` / Artifact `changed-module-only-41635146188-1`, ID `13229893478` is retained as failed history only. Its parser/type errors and recovery `sorryAx` are listed in `verification.json`; R1 is not a successful source binding. R2 is the sole successful source binding here.

The local import/collision prechecks are recorded as `TOOL_RETURN_ONLY`; they are not independent stream-hash receipts. No local Lean run was performed. Full PR CI, same-C verification, and post-merge checks are `NOT_RUN` at this stage. This package does not establish legal discharge or replace the external identity contract.

## Inventory and derived outputs

The official theorem inventory was regenerated with `--require-bound` at source checkpoint `2c07cdb41bd317bed458589265e2a30a5e747597` / tree `ce5ae4c3043c60f5f371fc934b94d9b465074937`. It records 581 tracked Lean files, 6286 theorems and 146 lemmas across the tracked Lean tree, with 0 audit targets lacking declarations. The JurisLean package records 566 files, 6274 theorems and 139 lemmas. The exact inventory digest and generated derived-output pins are in `verification.json`. These are source inventory counts, not full-model acceptance.
