# U09.2 original-scope cash-conservation close

## Exact scope and evidence

The frozen manuscript’s U09.2 statement (L364) assumes each event’s cash-increment vector sums to zero over a closed account set, then concludes that every finite event sequence has total increment zero by rearranging finite sums. It explicitly requires fees and boundary flows to be included and says this does not prove a debt claim or procedure valid. The original residual is retained verbatim in `verification.json`, including that actual event occurrence and boundary-account completeness are external premises.

The original question fixes debt amount and payment amount fields in `ℚ` (09, L91-L93). Its 09.8 cash paragraph asks for same-unit increments over a closed account set with per-event sum zero and the finite-sequence conservation result (L204-L206). The two existing `Ledger` declarations already prove the finite event sum and per-account cash sum for `List (A → ℚ)`, under `[Fintype A]` and the per-event balance premise. The independent changed-module run audited both theorem types and standard axioms and checked `cashVector`’s object type. No new cash-flow model or accounting interface was introduced.

This evidence leaves the frozen premises intact: actual cash events must be established externally, and fees or boundary accounts must be included in the closed set or named as boundary flow. A transfer alone does not establish lawful discharge. `Ledger.lean` was not changed.

## Original-question mapping

This package closes only the cash-conservation subparagraph of 09.8. Other 09.8 requirements about refund stages, identity, debt decomposition, and the strongest combined conditional theorem remain outside this close; U09.3 also remains separate. The progress row stays `PARTIAL_SOURCE_AND_MODULE_EVIDENCE_MAPPED`. No actual-call change is made to any of the 15 consumer edges.

## Independent audit

The original two theorem targets and the `cashVector` object check were emitted by changed-module run `41065859816`, attempt 1, job `124096972537`. `verification.json` binds the audited source commit and tree, artifact bytes, source hashes, original residual, and raw five-block output. This is independent module evidence, not PR/full-release/merge evidence.

Artifact `changed-module-only-41065859816-1`, ID `12982083685`; ZIP 985 bytes, SHA-256 `6b584289dac1cfbc781c57f3d6d4e6c8a6ef8b9b75f77719c3ae16c779e9c514`.
