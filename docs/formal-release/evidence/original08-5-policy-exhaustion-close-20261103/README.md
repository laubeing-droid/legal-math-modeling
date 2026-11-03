# Original 08.5: executable opportunities and independent policy closure

**Disposition:** The frozen 08.5 L127/L129 obligations are mapped as COVERED by one finite countermodel, one actual-bound conditional validity/exhaustion theorem, and the listed existing declarations. This package records source-module evidence; full-record PR acceptance remains pending.

## Frozen source and scope

Source: `08_规范时间证据与程序终局.md`, lines 125–130; subparagraphs L127 and L129; clauses `U08.2` and `U08.3`. The frozen source SHA256 is recorded in `verification.json`.

- **L127, declared finality versus executable opportunity:** Reuse `TerminalPolicy`, `rounds`, `finalUndetermined`, `FullyExhausted`, and `exhaustionOf` from `Seams.AdjudicationBridge`. The finite `counterPolicy` has a singleton claim and empty admissible support and all four rule sets empty; the induction proves every round remains `(∅, ∅)`, hence the claim is final-undetermined and the old declared exhaustion predicate holds. Separately, `counterRequired = [1]` and the explicit `counterExecution false` has exactly one executable step, at operation 1. Thus declared finality can hold while an independently required executable opportunity remains. The older `ProcedureClosure.Audit.badPolicy` example uses `EvidenceProcedure.ProcessInput`; it is a different type and is retained only as its existing counterexample, not treated as the same policy object or a general compatibility theorem.
- **L129, validity and actual bound:** `ValidPolicy` records the complete `Gamma × Result Nat`, independent `ProcessPolicy` and `RawProcess`, context/version equality with the actual `selectVersion` result, primitive policy checks, and completed dependency records. Its primitive checks cover the declared scope, coverage, uniqueness and registries; they do not assert exhaustion or a final outcome. `actual_bound_valid_policy_exhaustion` instantiates this policy at the actual `BoundData` and actual selector. Given `ValidPolicy` and the separate fact that the bound's actual `RawProcess` is exhausted, the existing checked-closure theorem yields `.closedLawfully` and the independent required operations are terminal. It does not claim the old opaque kernel exhaustion propositions imply this process-level `RawProcess.exhausted` fact.
- The source's normative policy and the actual material/process are separate inputs. A successful source binding or list of source records does not itself establish external authorization, actual-world truth, legal applicability, or a real execution/waiver. Closing a blocked or unavailable channel still requires the specified effective execution or waiver, final closure, and dependency conditions; the policy's blocked fallback is not an AI-only refusal rule.

No definitions in the frozen source or old modules changed. The two new declarations use the standard axiom subset shown in the raw output; no new axiom is introduced.

## Source-only evidence

The source checkpoint is `bd1830aaec052822f07aefe8826c1c1361128ae9` (tree `84854b05512e34e91c72c2a0a957d9f5e6a7195d`, parent `0fa0dea7a71c3187d645e5aa724ad1e592874dfb`). Successful changed-module run `41559151149`, attempt 1, job `125665263921`, compiled `JurisLean.Candidates.SourcePolicyExhaustionAudit20261103`; its artifact is ID `13196147073`, name `changed-module-only-41559151149-1`. The artifact API digest, raw log, module plan, source pins, target list, axioms and diagnostics are bound in `verification.json`.

The raw log reports nine theorem declarations via paired `#check` / `#print axioms` outputs and four type-only checks. It ends with `Build completed successfully (8512 jobs)`, zero errors and zero `sorryAx` hits. The source run is module evidence, not full PR/release acceptance.

Run `41557640550`, attempt 1, is retained as failed history only. Its compiler output had three errors: an induction simplification left the successor-round goal unsolved, and two calls passed `RuleUse` where `List RuleUse` was required. Recovery output included `sorryAx`; it is not success evidence. The repaired source was separately compiled by run `41559151149`; the first run does not count toward the passing target set.

## U00 producer boundary

This package adds producer-side evidence for the existing U00 edge 5, “规范/证据→Harness”. For an actual bound, it connects an explicit valid policy and actual process exhaustion to the inspected lawful-closure result and terminality of each independent required operation. It does not change the existing caller or runtime flow, raise edge ratings, establish external authorization/source truth, or claim every allowed domain was newly generated.