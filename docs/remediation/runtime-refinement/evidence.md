# Runtime Refinement Evidence — 2026-08-15

## Decision

`INCONCLUSIVE / RESULT_MISMATCH`

The external receipt is structurally and cryptographically valid. Ten fixed synthetic conformance
cases were compared: seven align and three differ. This evidence does not support a cross-runtime
agreement claim.

## Subjects and bindings

| Field | Value |
|---|---|
| LMM specification commit | `b9925428ca1c8663c8dbca236c1d5d2f231097af` |
| JC runtime commit | `be60fc2f5aebf76c909d8ff81e269c969664435a` |
| Expected fixture digest | `2d1e5c83c8f2f31d8312b3be3813b5b5dba4a63ace4182938d5e67d774ce16c2` |
| Source snapshot digest | `4d2cd59d42e6392b78721960beff8d8cdfc5df4939cd98da12ba2a4e215f4d24` |
| Rule-pack digest | `3879c3e2c520ecd55f5714d60ae962b60c2cce73767cfae6749512ce4674fe5a` |
| Runtime receipt digest | `02c590b20c5ba60c077cd12d7d9bdb55e1afebe0ebe9b07cb746c4761bcea397` |
| Semantics | `grounded@1` |
| Producer | `juris-calculus` |

## Portable artifacts

| Artifact | File SHA-256 |
|---|---|
| `expected-b9925428.json` | `59ae0e9d79f14bf53b82098210c503b3190569d44dfa075d97bfe71f59707d93` |
| `run-bindings-be60fc2f.json` | `0cf703180c40546b39283806b6ecc9915ce0592210c9c6a0e1cb18c362b688ac` |
| `runtime-receipt-b9925428-be60fc2f.json` | `76be9ad2b8cbf1110bb36118fba49fd6ff9edb7661ed0e2f308e2fff6b52771a` |

The receipt embeds each canonical semantic result, result digest, audit-bundle digest, derived status,
case output digest, and whole-receipt digest. The bindings contain run IDs only and do not self-report
statuses.

## Divergences

| Case | Expected | Actual |
|---|---|---|
| `license::priority-off` | `REFUTED` | `UNDECIDED` |
| `permission::conflict` | `UNDECIDED` | `PROVED` |
| `priority::active` | `PROVED` | `UNDECIDED` |

Independent LMM verifier output:

```json
{"aligned":false,"blocked":true,"compared_case_ids":["contract::force-majeure","contract::plain","license::priority-off","license::priority-on","permission::condition-missing","permission::conflict","priority::active","priority::cycle","priority::missing","priority::self-attack"],"error_codes":["RESULT_MISMATCH"],"passed":false,"receipt_valid":true,"status":"INCONCLUSIVE"}
```

Exit code `1` is intentional for `INCONCLUSIVE`; only aligned valid evidence exits `0`.

## Verification record

- LMM receipt target: 18 passed, including tracked external-evidence revalidation.
- LMM full Python suite: 51 passed.
- JC receipt target: 7 passed.
- JC canonical-entrypoint/audit/pack target: 31 passed.
- JC full Python suite: 391 passed, 28 documented heavy-dependency skips.
- JC MCP in-process smoke: status `ok`, readiness not claimed.
- Local Lean: not run. All Lean acceptance remains GitHub Actions-only.

## Limits

- The fixed pack is synthetic conformance data and has no legal authority.
- This is a `RuntimeRefinementReceipt`, not a `FormalReleaseCertificate`.
- A valid receipt proves traceability and exposes divergence; it does not prove agreement here.
- It does not prove full JC refinement, Python correctness, legal correctness, or corpus readiness.
- The JC commit is a local checkpoint and has not been pushed; pushing that repository requires
  separate current-turn authorization.
