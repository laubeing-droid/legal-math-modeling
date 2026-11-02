# Original 07.7: finite four-stage compatible witness

**Disposition:** candidate C, pending full-record PR acceptance. The changed-module source build succeeds for the named audit target; this package records the finite L295 witness and its limits.

## Frozen obligation and proof result

The frozen question is original 07.7, source lines 293–296, with the four-stage obligation at L295 (source SHA256 `1bf38abdd67bbacde464bc47814a672220a223d4a553f3cebf8812b066b3458a`). The row asks for a finite four-stage common model and a counterexample to treating equal relations as equal complete states.

The new theorem `JurisLean.Candidates.SourceStages20261027.finite_stage_compatible_counterexample` proves one closed existential over the existing `SourceFrame` and `runStageView stageView` fixture. It establishes that the run succeeds; the before-formation and after-formation relation lists differ; the after-first and after-second relation lists are equal and satisfy the same `forms` predicate for every relation; their debt amount values are 3 and 0; and the complete ledger states differ. The proof obtains the existing successful fixture, uses kernel reduction (`decide +kernel`) for the finite data, then derives the relation predicate and complete-state inequality. It is a theorem, not an `#eval` claim.

The earlier declarations supply the complementary generic pieces: actual previous-output threading, adjacent formation projection, complete nonquantity-field preservation, scalar/item projection, the two-payment balance/cash result, conservation, and fixed-background preservation of old contracts. Together these explain the finite witness while retaining the existing generic scope. A difference in the amount projection proves the whole states differ; the scalar equality alone is not treated as identity of every state field.

## Exact build evidence

The passing source-only attempt is Run ID 41443123829, attempt 1, Job 125269641272 (`changed-modules`), event `workflow_dispatch`, at source commit `af0dab242cc4518e7b51264eb8ae76613ceb51b7` and tree `6e836bfaf93c8af5d18a73fd9e50d4c458600a03`. Its Artifact `changed-module-only-41443123829-1`, ID 13140849372; `changed-module.log` is copied byte-for-byte from that artifact, with the exact requested module plan in `module-plan.json`. The nine selected targets and their `#check` / `#print axioms` raw-log lines are listed in `verification.json`. The new theorem appears at raw log lines 667–677, with its axiom output at 678–680: `[propext, Classical.choice, Quot.sound]`. The successful log has zero `error:` and zero `sorryAx` occurrences.

The first source attempt was Run ID 41441275833, attempt 1, Job 125263468945 (`changed-modules`), on commit `0a893ccb9d72b58ce6f5d58256589c821e653d52`; its Artifact `changed-module-only-41441275833-1`, ID 13140446360. It failed at the initial `by decide` in the finite computation. Its original log and module plan are retained under `history/`; that log contains the compiler's recovery output including `sorryAx`, and is explicitly not passing evidence. The sole source repair changed that tactic to `by decide +kernel`, using kernel reduction and introducing no new axiom, native proof, sorry, or weaker conclusion. The second changed-module run is the passing evidence. Both attempts and their separate source subjects, jobs, artifacts, plans, and outcomes are recorded in `verification.json`.

## Scope limits

This closes only the finite four-stage L295 mathematical mapping as a candidate C. It does not establish arbitrary stage systems, real-source truth or legal force, runtime Pipeline wiring, or completion of other original-07 rows and engineering/consumer obligations. The package is not full-record PR acceptance and does not close global archive gaps.
