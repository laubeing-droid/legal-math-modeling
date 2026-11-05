# Archived weights revalidated in the current context

Scope: original 14.5 and 13/S14's rollback contract. Old weights are an input candidate, not permission to restore the archived service state. The implementation reuses the actual singleton finite fitter on the current journal, recomputing sample size and empirical loss and binding the full current protocol. The actual current loaded model is the validation parent. All declared protected domains are recomputed, then the existing current-context sampling/authority/activation function performs the write and readback.

General proofs bind the returned candidate to the current journal and protocol and to exactly the supplied archived weights. A successful rollback is the actual current activation result with its written model and readback; all outcomes preserve current Gamma, principal, loss scope and training journal. History is retained and actual activation attempts append a new entry. Refusal preserves the actual loaded predictor for every input. A permission bound to a different historical evaluation cannot authorize the newly computed package. Proposal/evaluation failures return their original Result status and leave the current service unchanged.

Independent [run 40442236021](https://github.com/laubeing-droid/legal-math-modeling/actions/runs/40442236021), [job 121985036697](https://github.com/laubeing-droid/legal-math-modeling/actions/runs/40442236021/job/121985036697), SUCCESS on `e579de9351b9fd6510b1c9f0ceadc8f003f67dc3`: 9 exact type/axiom targets and 8 guarded executions, standard axioms only. Both implementation and driver match that subject after LF normalization. Raw original named output and source binding are retained. The previous `1d309b91c0a7790998b75c05b7a117026efc02af` / [run 40441829108](https://github.com/laubeing-droid/legal-math-modeling/actions/runs/40441829108) failed two equality witnesses already reduced by case analysis. The successful subject uses reflexivity and also puts current training admission before validation in the synthetic fixture.

The successful execution obtains archived weights from the earlier actual loaded result under rule version 1, rebuilds current externally confirmed training rows under rule version 2, evaluates and loads a newly issued version 99, preserves rule version 2 and the current journal, appends history, and changes the actual two-point risk from 1/2 to 0. Negative executions cover absent authority, absent sampling, current protected-domain harm, changed loss, a historical permit for another package, a replaced validation snapshot and malformed archived weights.

Construction-card G-PROPOSED correspondence (baseline 825792b83476a767152396d7f5e2ba3017048841): the new source/namespace is absent in that baseline; reuse of newer proved components is explicit.

| Symbol | Original obligation | Baseline / reuse | Actual consumer | Acceptance |
|---|---|---|---|---|
| proposeRollback | 14.5 / S14, old weights under current target/data | NEW; calls current EventFeedbackConsumer.fitFromStore with the singleton archived table | evaluateRollback | current sample size/loss/snapshot/protocol; wrong loss and width rejected |
| evaluateRollback | 14.5, current support and protected domains | NEW; calls ProtectedFeedback.evaluate on actual current parent and reissued candidate | attemptRollback | current rule2, exact actual validation rows, protected harm |
| attemptRollback | 14.5, independent current authorization | NEW; calls ValidatedFeedbackLoad.activate | rollbackPost | absent/current/historical permission, changed validation snapshot |
| rollbackPost | 14.5, actual continued state | NEW; consumes actual LoadOutcome.post or retains current service on pre-activation failure | next service/model caller | actual written/readback model, current Gamma/journal/history preserved |
| rollback_loaded_weights_have_current_snapshot | 14.5, exact rollback identity | NEW; consumes actual fitter, evaluator and activation proofs | proof of rollbackPost's actual loaded value | general source-to-write chain plus normal execution |
| refused_rollback_keeps_actual_prediction | 14.5, refusal semantics | NEW; reuses actual activation refusal theorem | every input of post-service predictor | general theorem and all refusal executions |

The proof concerns the supplied archive package; its historical provenance remains an input responsibility. Real sampling, label truth and legal authority retain the protected-validation and authorization premises. This is an executable finite model store, not a production deployment. The runtime round budget/freshness/trusted-checker/learner-update contract and whole U00 remain separate obligations.

Root integration occurs after the independent success. The driver reuses the prior standalone load-audit fixture; the implementation does not import an audit module. Full PR ULM/Authority is separate. OPEN=20, closes_debt=false, CAND8=8 outside PROVE_CANDIDATES; no discharges/frozen-pin/workflow/toolchain change or local Lean/Lake/Elan.

## 原题 14.5 阻断后的模型保持与当前上下文回退 · 2026-11-06

冻结题单 L113、L115 与补正 S14 L232 要求精确候选、可回读快照、拒绝保持及当前上下文下的回退。以下 L 指 `JurisLean.Candidates.ValidatedFeedbackLoad20261027`，R 指 `JurisLean.Candidates.CurrentContextRollback20261027`。本归引连同相邻的 `validated-feedback-load-20261027` 证据包使用；两包的原验证、原始输出与源码绑定保留。

### L113 当前模型、候选与接纳事件

当前模型 θₜ 是 `L.Service.loaded` 中的 `TrainingCandidate`。其 `fitted.protocol.fit.modelVersion` 记录模型版本，完整 `fitted.protocol` 保留目标、特征、标签和损失等版本合同，`snapshot` 保存产生该候选的完整训练 Store。`readLoaded` 读取当前槽，`predictLoaded` 读取这个槽内的实际表。候选 θ′ 由 `prepareNext` 调用既有 `processAndFit` 产生：当前已加载表实际进入搜索类，事件更新后的 journal 实际供下一拟合读取。准备阶段保持原加载模型，候选不是通过另一个并行输入替换出来的。

`L.activate` 按实际输入核验：evaluation.parent 等于当前 readLoaded；candidate.snapshot 等于当前完整 journal；计划的规则/机制版本及损失版本与当前 Service 相容；以原 plan、parent、candidate、blocks 重新计算整个 evaluation 得到同一结果；每个计算出的保护域界通过；外部抽样回执精确绑定 plan、parent、blocks 且声明早于取得数据；独立许可精确绑定 evaluation，并由当前 Gamma、主体、动作、候选模型版本及有效时间核验。不同失败返回各自 LoadStatus。

`L.refusal_keeps_actual_prediction` 证明每次未加载结果仍读取原当前模型、readback 为 none，且对每个 query 预测相等。拒绝仍可追加审计历史，因此模型语义保持不等于整个 Service 对象不变。`L.activation_keeps_rules_mechanism_and_training` 保持 Gamma、主体、损失版本及训练 journal；`L.every_activation_attempt_retains_history` 保留原历史并追加本次尝试。

成功时，`writeAndRead` 先把 evaluation.candidate 写入槽，再读取刚写后的实际槽；回读值不是调用方提供的回声。`L.loaded_package_is_actual_written_readback` 将成功结果绑定到确切原 parent、完整当前快照、重新计算的 evaluation、保护域门、抽样与许可，并证明 post 的实际模型恰为被验证 candidate，readback 恰为该 post 槽的读取值。`L.newly_loaded_model_is_next_actual_parent` 又把这个已加载模型接到下一次实际拟合。

这里的接纳检查使用完整结构相等。哈希若用作包或快照的身份索引，只承担相应编码与同一性边界，不能替代上述内容匹配、实际计算或外部条件，更不证明候选的数学正确性、总体风险、标签可靠性或法律效力。现有 `L.actual_loaded_risk_follows_computed_domain_bounds` 另以明确的联合置信事件为前提，给实际加载模型逐域的有限风险合同；该前提不是从 hash 或版本号推出的。

### L115 三个有限不匹配见证

以下均为 `ValidatedFeedbackLoadAudit20261027.lean` 中已有的实际 guarded 求值，使用同一有限拟合/评估/加载 fixture。

| 改变项 | 实际改动与结果 |
|---|---|
| 校验后换候选 | L128–136 把已评估 candidate 的 fitted.table 换成 [1,1]，仍带旧评价与许可。重新计算整包检查失败，返回 `invalidEvaluation`，实际 loaded 保持原模型。`L.replaced_candidate_does_not_reuse_old_permit` 还一般性排除另一 evaluation 包复用旧许可。 |
| 数据快照改变 | L146–154 把各验证 block 的 snapshot 加 1，重新 evaluate 后仍使用旧抽样回执，返回 `samplingUnresolved`。`L.changed_validation_snapshot_does_not_reuse_sampling_receipt` 证明 blocks 不同就不能匹配旧回执。另 L181–190 在当前 journal 追加一次观测，即使当前训练值可相同，完整快照已不同，旧候选被 `snapshotMismatch` 拒绝且 loaded 不变。 |
| 目标规范改变 | L156–162 把 plan.scope.target 从原标识 2 改为 99，候选与旧合同未同步改变，返回 `invalidEvaluation`。这里以不同 target 标识表示旧/新目标规范；这是 S14 L232 的“target 换义”有限见证，不把该字段冒称为另一个不存在的 targetVersion 字段，也不把它混作 labelVersion。L229–238 另将下一拟合的 protocol.fit.target 改为 999，得到 `unknown .targetMismatch`，此前已加载模型及其实际预测仍保持。完整协议匹配另检查现有 labelVersion 等字段。 |

### 当前 legal context 下的回退与历史

线上结果与离线条件不符时，需要针对当前材料重新形成回退请求与验证，不能仅凭旧包曾被接受就恢复整个旧 Service。`R.RollbackRequest.archived` 提供历史候选；其历史来源真实性仍由外部证据承担。`R.proposeRollback` 仅取该包的权重表，调用当前 journal 上的既有单元素候选拟合器，重算当前样本数与经验损失，绑定请求的当前 protocol。`R.rollback_proposal_uses_current_sample` 证明返回候选使用当前完整 snapshot、当前 protocol 和恰好这些历史权重。损失版本不匹配由 `R.wrong_current_loss_blocks_rollback` 返回 `unknown .targetMismatch`。

`evaluateRollback` 使用当前实际 loaded 作为 parent，重新检查当前声明的保护域；`attemptRollback` 随后调用当前 `L.activate` 的抽样与授权门。`R.rollback_loaded_weights_have_current_snapshot` 将成功回退连到实际写入/回读：权重等于请求的 archived 表，而 snapshot 和 protocol 已是当前对象。`R.historical_permission_cannot_authorize_new_evaluation` 排除历史 evaluation 的许可授权不同的新包。

`R.rollback_keeps_current_rules_and_training` 对所有结果保持当前 Gamma、journal、主体和损失版本；`R.rollback_preserves_current_history` 保留历史前缀。进入 activate 的尝试追加记录，提议或评估阶段失败则保留原状态与原历史。`R.refused_rollback_keeps_actual_prediction` 保证没有成功加载时对每个 query 仍为原预测。

已有 `CurrentContextRollbackAudit20261027.lean` L75–88 的实际实例从规则版本 1 下真实加载过的结果取 archived 权重，在规则版本 2 的当前数据上重发模型版本 99。成功后保留当前规则版本 2 和当前 journal，样本数为 2，历史长度为 2，实际两点风险由 1/2 降至 0。其后负例分别拒绝缺少当前授权、缺少抽样、保护域受损、改变损失、历史许可换包、改变验证快照及不合宽度的旧表。它们说明有限回退合同的输入责任；回退预测权重不撤销法律规范，也不赋予删除历史的权利。

本归引复用 PR40 的加载与下一拟合、PR42 的当前上下文回退，以及同源 PR131 Authority 实际类型/公理输出。原加载包 9 目标与 15 项 guarded 执行、回退包 9 目标与 8 项 guarded 执行沿原证据保留。PR131 build 日志 L14287–14483、L16212–16362 提供对应具名输出，两处 audit 编译成功分别见 L14286、L16211；guarded 消息由编译时核验，不声称这些 true 文本在原日志另行展开。现有实现是有限数学模型中的实际状态转移，不据此宣称生产部署、实时漂移探测、物理数据库事务或自动法律授权。真实抽样、标签、来源和法律适用条件沿原合同；U00 与工程消费链仍按独立分母验收。本次只准备数学归引，不新增源码或 CI。
