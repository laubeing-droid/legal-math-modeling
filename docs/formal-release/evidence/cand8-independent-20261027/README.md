# CAND8 v1.1 independent expanded axiom audit

This receipt adds the eight CAND8 targets to the prior 61-name audit, without
replacing the frozen live pin or promoting FormalTail into the release root.
The source module is byte-identical to merged PR #25 at
`ba9f6b784cdd9f831b2c34f51449157b77d6ea50`.

The independent driver `JurisLean.Candidates.FormalTailCAND8AxiomAudit20261027`
uses `#check` and `#print axioms` for all 69 exact names. GitHub Actions
[run 40356561660, job 121690497738](https://github.com/laubeing-droid/legal-math-modeling/actions/runs/40356561660/job/121690497738)
compiled it at `d26bf26022c94abbb61f45be437af514ba73dedd`. The saved raw text
contains the kernel's type and axiom output, extracted from that job log;
installation/environment output is not part of the receipt.

`verification.json` records the source identity, exact named set and the result
of the existing `check_axiom_audit_log.py` parser. The tests bind this output to
both source commits, all 69 declarations and both commands in the audit driver.
No target depends on `sorryAx` or an axiom outside `propext`, `Classical.choice`,
and `Quot.sound`.

Scope: `PASS_NAMED_AXIOMS`. This is not a claim of full branch CI or completion
of the manuscript's positive theorems. The live pin remains subject
`21862d9bdd94bfa15e5da39079538b5eb30ff235`, Authority `40274167574`, named=61.
OPEN remains 20, `closes_debt=false`, `discharges_archived_manuscript_gaps=false`.
CAND8 stays at eight and outside `PROVE_CANDIDATES`; U01 remains a separate
original-theory obligation.
