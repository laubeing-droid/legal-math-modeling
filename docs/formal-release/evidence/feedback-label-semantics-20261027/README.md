# Fixed-target feedback semantics and correction of wrong labels

This addresses the explicit fixed-target/reliable-label condition and the specified two-point self-label counterexample in original question 14.1 and correction S14. It uses the executable event-feedback implementation from PR37; it does not replace that producer with a new abstract transition relation.

`Reliable` names an external interpretation premise for the registered confirmations. `StoreMeaning` says each actual active cell carries the label of the same target, case, event and feature. General proofs transport that condition through observations, conflicts, retractions, corrections and any finite update sequence. Scope and the external registry are preserved by the actual functions. The training-sample theorem traces each row actually read by the fitter to its target-correct cell. The composition theorem binds this guarantee to the actual poststate and candidate returned by `processAndFit`, rather than an independently supplied snapshot.

A separate recovery theorem permits the replaced old label to be wrong. It requires the new external label to be correct, exact prior/effective-time/authorization gates to pass, and only untouched events to retain their meanings. It does not assume all historical confirmations were correct. This distinction is necessary for the original late-correction example.

The two-point counterexample uses the actual finite fitter: pseudo labels (1,0) cause selection of [1,0] from [[0,0],[1,0]], lowering training error from 1/2 to 0 while true labels (0,1) raise actual error from 1/2 to 1. Exact rational kernel proof and guarded executions are included. This does not assert that the legitimate ingestion gate accepts suggestions.

Independent module CI succeeded on subject `1ed7eae9d690f99278b0d4b1a3ef8a519c89ad8b`, [run 40429431857](https://github.com/laubeing-droid/legal-math-modeling/actions/runs/40429431857), [job 121943232612](https://github.com/laubeing-droid/legal-math-modeling/actions/runs/40429431857/job/121943232612): 13 exact type/axiom targets and two guarded executions, standard axioms only. Both source files match that successful subject; `verification.json` and `axiom-audit.raw.txt` preserve the binding and original output. The preceding 12-target version on `9b659637f2a9eef3371fb491a9f16a5fd73aa499` passed [run 40429049593](https://github.com/laubeing-droid/legal-math-modeling/actions/runs/40429049593), but does not replace the composition theorem's new receipt. The first draft `f7e2a062b31f21d2ae9fe5dfde11146ad036d1df` failed [run 40427982018](https://github.com/laubeing-droid/legal-math-modeling/actions/runs/40427982018) on Boolean API usage, match simplification and closed reduction. The second draft `ce648e8d342e668ba8559bc9f14ce498f16bcf41` failed [run 40428619349](https://github.com/laubeing-droid/legal-math-modeling/actions/runs/40428619349) because a repair lemma inferred the old cell instead of the actual corrected cell. These proof errors were repaired without weakening the original targets; neither failed run supplies successful evidence.

Real label reliability, event interpretation and normative authority are explicit external premises, not inferred from fields or this CI. These statements are not iid/generalization claims, candidate-validation guarantees, actual service loading or all of topic 14/U00. OPEN=20, closes_debt=false, CAND8=8 outside PROVE_CANDIDATES, discharges and the frozen tip pin remain unchanged. The implementation entered the root only after independent success; the audit driver remains standalone. Full final-head acceptance is required separately.

## 原题 14.1 标签来源与目标保持 · 2026-11-06

冻结题单 L89、L91 与补正 S14 L226 分别规定最小标签合同、两个实例和固定目标的保持条件。以下 E 指 `JurisLean.Candidates.EventFeedbackConsumer20261027`，S 指 `JurisLean.Candidates.FeedbackLabelSemantics20261027`。

### L89 最小标签生成合同

| 原对象 | 已有类型中的位置与证据 |
|---|---|
| 系统建议 | `E.Origin.suggestion` 标识建议的来源类别。`E.suggestions_do_not_enter_training` 证明建议来源的输入无法写入训练样本。 |
| 律师采纳行为 | `E.LabelMeaning.adoption` 指采纳观测，需本目标下的独立外部确认。 |
| 真实行为后果 | `E.LabelMeaning.behavior` 指已观测行为后果，保留实际测量、目标和外部来源。 |
| 诉讼程序结果 | `E.LabelMeaning.procedure` 指程序上的外部结果，保留对应案件、事件和版本。 |
| 规范上应有结果 | `E.LabelMeaning.normative` 指另外给定的规范目标，依赖有据的解释和确认。 |

`E.Observation` 保留完整 scope、案件及事件身份、测量及记录身份、特征、标签、来源与时间。写入需通过完整 scope 匹配、时间条件和同记录精确外部确认。未确认输入由 `E.unconfirmed_labels_do_not_enter_training` 排除。来源类别和合同比较的成立依赖给定外部材料，来源真实性和规范解释另依各自证据。

用同一对等权点，真实标签 Y=(0,1)，原预测 (0,0)。把系统建议 (1,0) 错当外部训练真值后，实际 `fitTable` 在候选 (0,0)、(1,0) 中选 (1,0)。`S.suggestions_fit_better_but_true_risk_worsens` 给出伪标签训练风险 1/2→0、真实风险 1/2→1。该实例的训练输入是绕开合同后的伪标签，正常接入检查沿用上一段。

延迟更正取同一事件 μ，t₁ 观测记录标签 0，t₂ 具名外部复核给 1，并引用当前被更正记录的 supersedes 身份。 `E.observed_history_is_append_only` 与 `E.corrected_history_is_append_only` 保证旧历史为前缀，`E.approved_correction_replaces_exact_prior` 核验当前 cell、更正关系、生效条件与精确许可。现有 `EventFeedbackConsumerAudit20261027.lean` 的实际实例给出授权更正后历史长度 2、拟合表 [1]。撤回后历史长度同为 2，而当前样本视图为空，拟合返回 `unknown .missingEvidence`。 `E.Cell.toSample` 与 `E.trainingRows` 只从 active cells 取样。拒绝的操作可保留原历史，append-only 允许此前缀等于全部后历史。

### L91 固定目标与标签更正

固定目标 Target 并给外部可靠性 `Reliable s target` 及现有当前视图的 `StoreMeaning s target`。`S.confirmed_observation_has_fixed_target` 绑定实际确认记录和该目标。`S.observation_updates_preserve_target` 及 `S.finite_feedback_preserves_fixed_target` 保持固定目标、scope 和 confirmations。 `S.actual_fitted_sample_is_target_correct` 与 `S.actual_returned_candidate_preserves_label_target` 把性质接到实际 `processAndFit` 的 poststate 和返回候选。各成立条件含可靠外部标签，统计改进需要单独证据。

授权更正允许旧标签错误。`S.approved_correction_repairs_target` 使用符合固定目标的新外部标签、未受影响事件的语义及 fresh、exact-prior、valid、allowed 条件，得到更正后实际 StoreMeaning。这里保留旧记录，也保留其作为被替换值的事实。

将实际胜诉目标 Y_win 换成采纳目标 Y_adopt 时，经验风险函数随目标和标签版本改变，数值不再是同目标下的前后比较。现有审计实例拒绝把旧 behavior scope 下的观测直接改写为 adoption 后塞回旧 Store。另一个实际实例改变 target version 后，`fitFromStore` 返回 `unknown .targetMismatch`。前一处来自完整 observation scope 核验，后一处来自 fit 协议中的 target/labelVersion 等字段。两处分别对应语义与版本边界。

本归引沿用 event-feedback-consumer、feedback-label-semantics 两个已验收源包、PR38 及后续同源 Authority 类型输出。原调用方和外部确认合同沿原证据验收。
