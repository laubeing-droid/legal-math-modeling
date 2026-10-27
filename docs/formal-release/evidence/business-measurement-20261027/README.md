# Business measurement from actual poststates

Original 11.1, S11, E11 and original 04 edge 10. Independent subject `6923d4bbb07d305ab9087bd49fea3680d461e8a4`, [run40453954728](https://github.com/laubeing-droid/legal-math-modeling/actions/runs/40453954728), [job122022821909](https://github.com/laubeing-droid/legal-math-modeling/actions/runs/40453954728/job/122022821909): 14 exact type/axiom targets and 18 guarded executions PASS. Raw type/axiom messages are retained verbatim after stripping only the timestamp and source-location prefix. Both LF-normalized sources are bound to that subject; axioms are audited separately.

## Original obligations and actual consumption

- The measurement dictionary distinguishes case, stage, opportunity, outcome EventId, MeasurementId and output RecordId. Full Gamma, target version, full-instant window, timezone and clock-conversion version are bound. External observation rows have separate event and record identities.
- Procedure choice compares the recorded actor/action; filing compares the full external instant with the declared closed deadline; timely positive-value performance looks up actual poststate payment receipts and sums their allocated values within the window, checking relation, parties, amount tag, norm version, cash identity/source and cash-event membership. Cash amount, surplus, accrual and allocation are not conflated. Zero-value legal transactions remain allowed by the ledger; this positive-threshold behavioral construct does not measure them.
- Positive results consume the actual computed total. Negative labels require an independent catalog entry asserting completeness of this exact dictionary and row list after the entire window closes. An empty queried database alone is not completeness. Missing/foreign/unattested rows do not become negative labels.
- Duplicate real event identities are refused before summation, including different document RecordIds for the same event. The consumer requires event reconciliation rather than counting duplicate documents as independent cases.
- A reviewed-defect finding is a separate externally attested construct. Revocation cannot supply that finding. The original 100-case example yields 10% only with the toy truth supplied, 40% among appeals and naive 8%; with unreviewed labels unknown, every binary completion has rate in [8%,88%], both endpoints are attained, and the same visible counts cannot identify both endpoint worlds.
- `measureTrajectory` calls the actual payment/refresh interpreter and consumes its reported poststate. UnknownCommit returns no poststate and no behavioral label. A measured output inherits the actual trace invariant and used-key monotonicity; measurement does not mutate the ledger.

## Evidence scope

The 18 executions include two 7-unit payments with allocation 10/cash14/surplus4, actual replay, an incomplete early window, a complete negative window, unknown commit, duplicate documents, absent receipts, late payment, false source, procedure/actor mismatch, exact deadline filing, late filing, revocation/defect separation, a cross-case mismatch and the original appeal endpoints. The arbitrary-input proofs are separate from these executions.

First draft `9913206b7e339820c38fad42a3bd32777a26672e`, run40453513600/job122021434343 FAILED in proof elimination/Boolean decomposition; it is not current success. Repairs preserve all declarations and checks. External identity, source truth, complete-window coverage, clock interpretation and legal meaning remain premises. Unique events do not establish iid. Policy advice, RSI flow and full U00 are subsequent consumers, not claimed complete here.

OPEN=20; closes_debt=false; no discharges change; frozen pin subject21862d9b/Authority40274167574/named61 unchanged. No local Lean/Lake/Elan.

