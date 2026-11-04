# Original 07.8: static source and exact quantity bridge

**Disposition:** mathematical mapping COVERED; candidate C pending full-record PR acceptance. The source-only changed-module build passes for the new bridge audit. This package does not record full-chain or mainline acceptance.

## Frozen obligation

The frozen manuscript is `D:\Codex\1.法律工作区\legal-math-modeling工作区\20261021挺进统一法律数学模型\理论统稿与ZCode施工包_v003补齐来源版_20261021T091138Z_fd4965\题单\07_法律对象共同模型与表示.md`, lines 297–300, SHA256 `1bf38abdd67bbacde464bc47814a672220a223d4a553f3cebf8812b066b3458a`. L299 says:

> 给 encodeQty、readAmount、unit 及定义域 D，要求 qtyDenote(encodeQty(q))=some(readAmount(q),unit(q))，或者明确给近似误差。证明无除整值片段不能覆盖金额 1/2；选择限制金额域或扩展表达式语法，并阐明选择所需的新假设。别把 Nat→ℚ 的精确嵌入当成任意数量表达式桥。最后收束一条包含 μ/来源视图/记录观察/共同模型/阶段读数/数量解释的静态条件定理，逐项说明为健全性还是完备性服务；给非空见证并对不可删假设提供反例。不得把结论本身重复当作前提。

## Quantity bridge

For `D = Final20261021.Amount`, `encodeQty` is the existing `SourceRepresentation20261027.encodeQuantity` into `RationalQty`; the reading is `Amount.value`, and `unit` is `Amount.tag.unit`. The reused theorem `all_rational_amounts_have_exact_tagged_encoding` proves `quantityDenote (encodeQuantity amount) = some amount`, preserving the complete tagged amount. Applying `Option.map` to select `(value, tag.unit)` gives the requested pair observation. The old division-free `QtyAst` counterexample is exactly scoped to expressions satisfying `divFree expression = true`: `old_division_free_syntax_cannot_represent_half` shows that such an expression cannot denote `1/2`. It is not a claim about arbitrary `QtyAst` expressions or every possible encoding.

The separate old finite history counterexample remains a different example: histories `[10]` and `[4, 3, 3]` have the same terminal balance but are distinct lists. It illustrates loss of history under that observation; it is not the source-model fixture below.

## Final conditional theorem and finite witness

The new `source_model_joint_semantic_quantity` takes an accepted `sourceModel ... = .ok out` and an explicit `resolveFaithful` condition for `μ`. It combines the existing `actual_source_has_joint_object` result with the selected `ExtractedView`, the observed-relation interpretation by `μ`, equality of the complete `CaseRecord` with the decoded record, the actual second stage equal to `payStage` on the first stage and bound second payment, and exact tagged quantity interpretation of the final debt amount. The full `Amount` roundtrip and its `(value, unit)` projection are both stated. These clauses are conditional soundness evidence for this accepted output and declared interpretation; they do not prove that a real source is true or that a production `μ` is faithful.

The new `source_model_joint_bridge_nonempty_and_faithfulness_needed` reuses `nonempty_source_stage_fixture`. It checks that this same finite fixture has a known legacy amount, constructs the existing `modelOf` result, and reuses the existing joint-object theorem. A `μ` defined by successful `resolve` witnesses the stated faithfulness condition. The constant-`none` mapping on the same successful output fails to identify its observed relation, giving the requested counterexample to deleting that condition. This is one fixture, not a universal guarantee for all materials or catalogs.

The result distinguishes preservation from reflection. Exact encoding preserves the full `Amount`; projected equality only concerns the declared `(value, unit)` observation. The reused adequacy/separation results state the conditions needed to move from observation equality to object equality. Neither this package nor the finite example claims arbitrary representations separate every state, arbitrary source truth, or runtime consumer connection.

## Build evidence and target accounting

The corrected source checkpoint is commit `b0f153e7dbb90c3965a46abdeb3102d5f09f3de3`, tree `841c45c1395d9ecca744fd218dcbe68dc87c40e1`, parent `252eb9ea0c68eeeddc55f042aecc58f981757ed1`. The current source-only run is [41474329740](https://github.com/laubeing-droid/legal-math-modeling/actions/runs/41474329740), attempt 1, changed-module job `125375808733`, on that commit and the source branch. Its actual artifact is `changed-module-only-41474329740-1`, ID `13156906754`; `changed-module.log` and `module-plan.json` are copied byte-for-byte from that ZIP. The plan requests only `JurisLean.Candidates.SourceFinalBridgeAudit20261102`.

The new driver emits two targets: `source_model_joint_semantic_quantity` at raw `#check`/axiom lines 116–117, and `source_model_joint_bridge_nonempty_and_faithfulness_needed` at lines 118–119. Each depends only on `[propext, Classical.choice, Quot.sound]`. The 14 reused named outputs are separately mapped in `verification.json`: eight selected SourceRepresentation results, five selected SourceStages results, and the existing joint-object result. Those are selected references, not a claim that the new driver itself has 16 targets. The old SourceStages and SourceRepresentation audit drivers remain their own 28- and 15-target dependencies; the joint-object declaration is also reused, not newly proved here.

R1, run `41473046523:1`, failed parsing the second theorem at source line 59 (`unexpected token '('`) on `∃ out (mu : ...)`; subsequent unknown-name errors were parser fallout. The precise syntax correction changed it to `∃ out, ∃ mu : ...`, without changing the theorem meaning. The R1 failed raw log and plan are retained under `history/`; they are not passing evidence. R2 is the successful build evidence. This module-only pass is not a full-release, PR, or merged-main result.

## Scope limits

This package maps only original 07.8 L299's declared quantity and static conditional source bridge. Its positive witness is one existing finite source-stage fixture; the older `[10]` / `[4, 3, 3]` history counterexample is separate. Faithfulness of `μ`, truth of real source material, legal admissibility, arbitrary extractor behavior, whole-theory completion, and runtime consumer wiring remain outside this evidence. Full-record PR acceptance is pending.