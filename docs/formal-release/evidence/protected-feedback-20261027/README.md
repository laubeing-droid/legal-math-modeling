# Actual protected-domain feedback validation

Scope: original 14.2/14.3, 13/S14 and E14. The implementation computes every declared domain's old/new loss from the actual validation rows, requires complete distinct domain coverage, includes both parent and candidate in the predeclared finite class, checks training/history versus validation event separation, and pays the sum of domain failure budgets. Each domain has its own sample count, budget, verified rational radius and tolerance.

The probability theorem derives a single measurable confidence event from explicit within-domain iid population laws and bounded loss. It covers every member of the fixed class across all declared domains without assuming independence between domains. The whole-evaluation theorem consumes the actual `evaluate` return and the same actual sample rows. A strict bound gives strict population improvement; a separate exact example distinguishes observed improvement from certified improvement and tolerated noninferiority. Average population risk improving from 9/10 to 1/10 can still worsen a protected point from 0 to 1.

`passesBounds` means computed interval comparisons passed. It is not a claim of externally verified sampling, authorization, acceptance, production loading or legal correctness. The existing logarithmic-radius verifier is conservatively reused with its factor-two class allowance; `finite_radius_mono_models` proves that allowance covers the ordinary fixed-class radius. Labels, actual event interpretation, the fixed-before-validation class and iid laws remain explicit premises; IDs do not prove them.

Independent [run 40436410064](https://github.com/laubeing-droid/legal-math-modeling/actions/runs/40436410064), [job 121965999424](https://github.com/laubeing-droid/legal-math-modeling/actions/runs/40436410064/job/121965999424), SUCCESS on subject `04942c277eacf3bd7f3b86be1fc353e94b92a9f3`: 12 exact type/axiom targets and 17 guarded executions, standard axioms only. Both source files match that subject byte-for-byte after LF normalization. `axiom-audit.raw.txt` preserves the driver's original named output; `verification.json` binds the subject and files. Lean suppresses the expected `#guard_msgs` messages; the successful driver compiles all 17 exact-result assertions.

Executable cases cover actual fitted parents/candidates, protected harm, missing/duplicate domains, exhausted joint budget, unsupported small budget/radius, empty data, a candidate outside the declared class, changed target/loss, reused training events, repeated validation events, changed protocol and legitimate changed model version. The literal original 14.2 contrast is also executed: 100 different cases/events give 100 training rows, while 100 measurement/record references to one case/event give one. Neither count is asserted to prove independence.

Earlier failed drafts remain failed: `14bf7b1925a4f1880dd4841046361e8c34de3aa6` / [run 40432628973](https://github.com/laubeing-droid/legal-math-modeling/actions/runs/40432628973) exposed proof-side ordering of absolute-value inequalities, casts and sample indexing; `a7bcf10890c2f0365ea2cff74cb95ec3982e3612` / [run 40433301935](https://github.com/laubeing-droid/legal-math-modeling/actions/runs/40433301935) left the dependent finite-index sum transport; `8a9330baccd7ec392dc7df2d3a124b41c479526c` / [run 40433882641](https://github.com/laubeing-droid/legal-math-modeling/actions/runs/40433882641) compiled the mathematical implementation but failed two driver record-syntax cases. The successful subject fixes the actual driver; no failed run is promoted to PASS.

Implementation joins the root only after this success; the audit remains a standalone entry point. Full PR ULM/Authority acceptance is separate. OPEN=20, closes_debt=false, CAND8=8 outside PROVE_CANDIDATES; no discharges or frozen tip-pin change. Actual authorized loading/next-round consumption and whole U00 are separate obligations.

The preceding subject fece078f7ae6defe0c6e7cd55e021867efb89ae7 also passed the same 12 targets and 17 executions in [run 40434490740](https://github.com/laubeing-droid/legal-math-modeling/actions/runs/40434490740). Initial full [Authority run 40435443558](https://github.com/laubeing-droid/legal-math-modeling/actions/runs/40435443558) compiled all Lean successfully but failed one Python documentation-anchor assertion (706 passed). Its missing seven-axis artifact and final gate failures followed that Python failure. The new internal helper name domainStatistics avoids the unique-prefix collision between the previous statistics name and the historical statistic field exemption. The historical exemption and gate rules remain unchanged. The renamed source passed all 20 local documentation-anchor tests and the newer independent job above; full PR acceptance is still separate.

Construction-card G-PROPOSED correspondence (baseline 825792b83476a767152396d7f5e2ba3017048841): the new namespace/source is absent in that baseline by Git tree/name lookup. Reuse of subsequently proved code is stated separately.

| Symbol | Original obligation | Baseline / reuse | Actual consumer | Acceptance |
|---|---|---|---|---|
| protected_iid_joint_event | 14.3 / S14, fixed-class joint confidence | NEW; reuses current finite-class iid risk bound and measure union bound | actual_protected_evaluation_confidence | arbitrary finite domains, explicit within-domain iid, summed budgets |
| blockRisk / domainStatistics | 14.2 / 14.3, actual sample unit and risks | NEW; reuses LearningConsumer.tableLoss and empiricalScore | assemble / evaluate | exact fitted parent/candidate and actual validation rows |
| blockValid / layoutValid | 14.2 / E14, nonempty independent-scope inputs | NEW; reuses existing rational radius verifier and actual training event history | evaluate | duplicate/reused events, incomplete domains, zero sample, budget/class violations |
| evaluate / Evaluation.passesBounds | 14.3, per-domain preservation | NEW; consumes actual candidates from EventFeedbackConsumer.processAndFit | validated feedback activation, integrated separately | actual interval checks, protected harm, target/version changes |
| bounds_gate_on_joint_event_preserves_each_risk | 14.3, true-risk contract | NEW; consumes computed statistics and the explicit confidence event | actual_protected_evaluation_confidence | actual evaluation result and every domain |
| strict_bounds_prove_strict_improvement | 14.3 / 15.1, strict versus tolerated change | NEW | strict-risk audit and downstream validation contract | strict inequality theorem plus observed-only/noninferior counterexamples |

UNLOCATED at this module boundary: the whole U00 business-to-learning caller and production refinement. The separate validated-loading module supplies a finite-store consumer; no production or whole-model acceptance is inferred here.

## 原题 14.2 重放、污染与样本身份 · 2026-11-06

冻结题单 L95、L97 与补正 S14 L228 分开规定计数反例、事件身份更新和五类风险。以下 E 指 `JurisLean.Candidates.EventFeedbackConsumer20261027`。

### L95 同案与不同案件的精确 100 输入

`ProtectedFeedbackAudit20261027.lean` L173–195 的两个已编译实际拟合检查使用相同 false 标签频率。第一批有 100 个不同 caseId/event，产生 100 cells 和样本数 100。第二批是同一 case/event 的 100 个不同 measurement/record/source 引用，产生 1 cell、样本数 1，历史保留 100 条。这里分别核对实际输入身份与拟合器读到的样本，引用数和样本数分列。

在相应 fair Bernoulli 模型及其原前提下，`JurisLean.Candidates.LearningDependence20261027.u01_4_independent_empirical_mean_variance` 给出 n 个独立观测之经验均值的方差 1/(4n)。`u01_4_copied_empirical_mean_variance` 给出 n 份同一观测之经验均值的方差 1/4。代入 n=100 得 1/400 与 1/4。 `u01_4_concrete_common_cause_counterexample` 另给 ID 不同而共享随机源的实际模型。独立性由抽样律及依赖结构承担，案件或事件标识只给计数单位。

### L95 当前训练视图与原始历史

按作用域和事件身份接收外部确认的记录。已见有效观测的原样重放只新增历史引用。尚未见过的有效输入若与当前事件 cell 的案件身份以及 active 的 feature、label 均匹配，也只新增引用，当前训练视图保持相等。直接复用 `E.replay_has_no_extra_training_row`。本题同案 100 次实例的当前计数为 1。尚未见过的冲突标签经实际 `E.observe` 使原 active cell 转为 conflicted，并保留记录。与当前 active cell 的案件身份或 feature 不匹配同样触发冲突。已冲突或已撤回的 cell 进入隔离分支。 `E.trainingRows` 只读取 active cells，所以冲突与撤回状态均与无争议训练样本隔离。

迟到更正需匹配当前记录的 supersedes 身份、版本、事件与案件、有效时间及精确许可。 `E.approved_correction_replaces_exact_prior` 绑定实际更正后 cell，`E.historical_replay_cannot_revive_superseded_label` 排除重放复活旧标签。 `E.observed_history_is_append_only` 和 `E.corrected_history_is_append_only` 保留历史前缀。幂等适用于当前标签和训练计数，追加历史仍可增长。外部确认及目标版本继续按原标签合同验收。

### L97 五类风险的位置和有限见证

| 风险 | 现有具名证据 | 对应数学责任 |
|---|---|---|
| 单案异常或错标 | `LearningBoundary20261027.u01_1_actual_fit_label_risk_not_truth_risk` 给出同一实际拟合器的标签风险 0、真实目标风险 1。 | 标签确认和目标解释承担可靠性，拟合过程消费的是已给标签。 |
| 同案重复 | 复用上面的精确 100 输入、两类方差和共享源反例。 | 事件身份控制训练计数。独立性与有效样本量依赖各自抽样模型。 |
| 地域或案由抽样偏差 | `LearningBoundary20261027.u01_3_actual_fit_zero_train_one_deploy` 给出训练域风险 0、部署域风险 1，`u01_3_two_worlds_same_training_uncontrolled_deployment` 给出同训练样本而未见域标签相反。 | 两点可解释为两个地域或案由。部署母体、选择条件和支持由相应输入声明。 |
| 答案泄漏 | `LearningEventSplit20261027.u01_3_event_split_does_not_certify_information` 给出实际 eventSplit 身份分离而各行仍读未来 feature、feature 等于 label、label 不等于目标的反例。 | 事件身份分割与信息可见性、独立标签目标分别验收。 |
| 局部改进损害其他能力 | `ProtectedFeedback20261027.average_improvement_can_harm_protected_point` 给出总体风险 9/10→1/10 且受保护点风险 0→1。现有审计的实际 evaluate 返回 `passesBounds=false`。 | 指定保护域需各自检查。概率保证依赖实际样本律、固定模型类及联合事件。 |

本归引复用 event-feedback-consumer、learning-provenance、learning-boundary、learning-event-split 和 protected-feedback 的已验收源包及 PR39 的完整接受。上述有限证据保持其输入条件。现有 U00/business-to-feedback 消费链沿独立调用合同验收。
