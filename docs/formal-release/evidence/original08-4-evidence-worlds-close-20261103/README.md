# Original 08.4: evidence states and legal-world sets

**Disposition:** Frozen 08.4 L121/L123 is mapped as COVERED by the selected existing declarations and source-module outputs. Full-record PR acceptance remains pending. The canceled first dispatch is retained as nonpassing history and is not counted as source success.

## Frozen source and scope

Source: `08_规范时间证据与程序终局.md`, lines 119–124; subparagraphs L121 and L123; clause `U08.3`. Frozen source SHA256: `eeaa6e20a4a475ff81dd25b77b36ffa28a27cdcf0e2b554f31b5710da9f6db0c`.

- **L121:** Reuse `EvidenceProcedure.u08_3_evidence_four_states`, `usable`, and `judgment` for the evidence-level distinctions. Reuse the constrained legal-world model and the four world classifications. Empty worlds characterize incompatibility; supported and opposed states require the corresponding nonempty universal condition; insufficient means both truth possibilities remain. The unknown-only example follows by applying `world_insufficient_iff_both_possibilities` to `[false, true]`. The old guarded output reports the evidence judgment, not this additional world-label field, so the two judgments are not stated as unconditionally equivalent.
- **L123:** Reuse the one-atom/two-evidence example `adding_credible_evidence_can_destroy_determinacy`. Reuse `derivation_trace_does_not_prove_actual_source_truth` with facts `[1]`, rule `[1] → 2`, and fuel `2`; at the same triple, `generated_trace_passes_separate_checker` shows the trace can pass a separate checker without establishing actual source truth. This is not a claim that the whole validator passes.
- **Conditional reliability:** `full_horn_worlds_keep_actual_truth_conditionally` requires its actual source-facts and selected active-rules model premises, actual-world coverage, and evidence-fidelity conditions before deriving actual-world membership and world truth. Its conclusion is not assumed as a premise.
- **Information order:** `adding_evidence_is_monotone_in_information_bits` concerns the information order on evidence bits. The legal-world construction filters explicitly allowed pairs; it does not infer a Cartesian product or use voting.

`P` here denotes proof rules, not the separate `Procedure` check. The independent process gate remains separate. `sourceFaithfulFacts` and `sourceFaithfulRules` are external premises named by frozen L97; successful compilation does not establish them. No real-world source truth, law applicability, caller wiring, or whole-validation PASS is claimed.

## Source-only evidence

The source checkpoint is `049de44b7d8b196e75f45b6ff4ef11e88a2e1299` (tree `e3160487d3999d9be2b4a966803ab592d3ee9bab`, parent `280f249d4a4d4e28d4988802b0282476de7b9788`). Two serialized changed-module runs succeeded on that subject: FiniteLegalValidation run `41541346784` (Artifact ID `13186313322`); EvidenceWorlds run `41541957382` (Artifact ID `13187396930`). The initial EvidenceWorlds dispatch `41541322871` was canceled and is retained only as nonpassing history. Exact artifact digests, plans, raw logs, selected target lists, source pins, and line mappings are in `verification.json`.

The EvidenceWorlds raw log contains 20 selected target outputs. The FiniteLegalValidation raw log contains 47 axiom-print outputs, of which 33 are the previously selected named outputs for this audit; the remaining outputs are transitive dependency output and are separately identified in the verification record. Neither source-only build represents full-record acceptance.

## U00 consumer boundary

This package adds producer-side evidence relevant to U00 edge 3 only. It does not change callers, runtime flow, ratings, consumer acceptance, external truth assumptions, or the broader engineering work.
