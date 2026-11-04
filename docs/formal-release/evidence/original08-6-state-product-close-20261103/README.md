# Original 08.6: judgment, procedure, and finite branch products

**Disposition:** Frozen 08.6 L133/L135 is mapped as **COVERED** by existing declarations from the independently compiled `ProcedureClosureAudit20261027` module and the previously accepted finite-family theorem. This package records source-module evidence only; full-record PR validation is pending.

## Frozen source and scope

Source: `08_规范时间证据与程序终局.md`, lines 131–136; subparagraphs L133 and L135; clause `U08.3`. The frozen source hash is recorded in `verification.json`.

- **L133, product outcomes and finality:** `four_judgment_process_products_are_distinct` gives four finite examples of judgment/process pairs: supported/open, insufficient/closedLawfully, incompatible/open, and insufficient/blocked. Each uses the existing one-element required/policy domain `[1]`; these examples do not enumerate every legal process state. `final_undetermined_exact` states the exact Boolean equivalence: the product is final-undetermined iff its judgment is insufficient and its process is closed lawfully.
- **L135, inspection and process closure:** `inspect` maps budget `0` to `.unknown .checkIncomplete`; that is an incomplete check, not normative authority or terminality. At positive budget, `successful_inspection_reads_actual_process_result` ties a successful inspection to the actual `checkProcess` result. `finite_inspection_does_not_end_retry_execution` gives a finite insufficient/open result alongside a continuing retry path. `same_current_record_has_different_future_extensions` and `current_record_does_not_imply_future_impossibility` separate the present record from possible future evidence. `branch_inspection_does_not_drop_open_results` maps every supplied branch to its own result, including non-closed outcomes.
- **Finite family reuse:** `FiniteLegalValidation20261027.family_retains_each_branch_including_failures` is reused from accepted 08.4 source run `41541346784`, not printed by this 08.6 run. It preserves the result for every branch supplied to the finite `validateFamily` input. It does not establish that an external branch set is complete, lawful, or exhaustive.

The current source module prints 20 declarations in total. The seven declarations listed above are the 08.6 mapping targets; no proof, definition, or Audit file was added or changed for this round. This run is changed-module evidence, not a full PR or release acceptance.

## Source-only evidence

Source checkpoint: `df9fa5a94c4f62cd234c7200227b2a0d90eb6513`, tree `a7176fc34a0067815143e09c58d82e4e223907f8`, parent `9384a42ce44852f1bf55a931c8a3b49c94e73adf`, branch `formal/close-original08-6-state-product-20261103`. Workflow-dispatch run `41578958684`, attempt 1, job `125729011414` (`changed-modules`) succeeded for `JurisLean.Candidates.ProcedureClosureAudit20261027`. Its only selected module is shown in the byte-exact `module-plan.json`; the raw log ends with a successful 8,478-job build and reports zero errors and zero `sorryAx` hits. The seven skipped workflow jobs are module-only scope, not full-chain successes.

The API snapshot, ZIP digest, expanded member hashes, declaration locations, and source pins are bound in `verification.json`. The current ProcedureClosure, FiniteLegalValidation, and related source pins match the accepted 08.5 pins. The reused FiniteLegalValidation source and Audit pins also match accepted 08.4; that package records run `41541346784` and `family_retains_each_branch_including_failures` at Audit lines 57–58, with the theorem declaration at source line 620.

## U00 producer boundary

This package adds producer-side evidence relevant to the existing U00 edge 5, “规范/证据→Harness”. The old caller and edge rating are unchanged. The finite `inspectBranches` theorem preserves supplied branch results, and the 08.4 `validateFamily` theorem preserves the results of supplied finite-family entries. `LegalActionDomain20261027` contains the existing `validateFamily` call at line 238; recording that code path does not add a runtime Harness connection. These declarations do not prove that all legally relevant branches were supplied or establish external authorization, source truth, or real-world legal validity.

The broader original-08 engineering review and U00 consumer/runtime work remain in their existing scopes. Global discharges, Step 2, `math_flip`, and the existing U50 classifications are not changed by this source-only package.
