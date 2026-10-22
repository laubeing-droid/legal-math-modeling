# Final20261021 候选施工检查点

状态：**PARTIAL_SOURCE_CANDIDATE / CHANGED_MODULE_CI_RUNNING**。本目录已有批次 0–9 的候选源码；尚未完成冻结理论的全部证明和接线，也未开始批次 10。当前不能宣称本任务完成。

基线固定为 `825792b83476a767152396d7f5e2ba3017048841`，候选分支为 `candidates/final20261021-825792b`。最新已完成的 run `39697636112` 在 `e26f0bac1ca3db5f9b6a67bdf0a87baf2e4fd785` 上通过 Iteration 后，于 Pipeline 的局部结果类型推断处失败。run `39698213475` 正在测试显式类型修复，subject 为 `76b24bb4e04a83a2a2aca7d535596761788ace8f`。逐轮原始日志、ZIP、散列、实际模块结果及修复范围以 `construction_status.json::ci_attempts` 和 `evidence/ci-stage1-*/` 为准。用户于 2026-10-22 授予连续 CI 修复、推送与派发授权。

## 逐模块与逐条复核入口

- `module_inventory.json`：每个模块的文件、理论编号、定理全名、操作入口及消费者行号、选定正反例和剩余义务。空例证栏明确表示缺少该类例证。
- `declarations.json`：声明与实际文本引用位置。文本引用不等于运行精化证明；空消费者不表示已被下游使用。
- `50_clause_status.json`：保留 50 条原始完整目标和验收句，列出候选声明与未闭合子目标；全部 `formal_ci=CI_NOT_RUN`。存在源码、定理名或导入关系均不自动关闭条目。
- `proposed_825792b.json`：全部包内拟议符号及新增 `proposed_*` 对固定基线的 `REUSE/NEW/UNLOCATED` 判定；没有定位的目标保留 `UNLOCATED`。`NEW` 表示新候选边界，未声称等价覆盖原包中的全部软件合同。
- `baseline_reuse.json`：真正调用的基线数量账和 Horn 声明、源散列、原文及消费者；`candidate_provenance.json`：历史候选参考来源。历史候选的成功状态不转移到当前源码。
- `construction_status.json`：施工卡及三家验收附录来源、两阶段 CI 状态、限制与阻塞。

另有两个入口模块：`CIAll.lean` 显式导入全部实现模块与候选审计；`AxiomAudit.lean` 导入 Acceptance 并逐声明执行 `#check` / `#print axioms`。二者没有新增定理声明；消费者分别是指定 CI 目标及 `CIAll`。最近已完成的整体构建仍在 Pipeline 停止，未执行到 Acceptance 和候选审计。全部 Lean 文件的 Git blob 散列均列在本地回执中。

## 本检查点补强的内容

`Compiler.proposed_checked_rule_input` 只有在逐规则检查闭包稳定后才返回 Known。`u03_2_checked_closure_complete` 把实际检查结果接到相对语义完备性；不足燃料返回 `checkIncomplete`。尚未证明该列表实现的完整有限载体/燃料上界。

`Ledger.ReceiptCoherent` 分别检查 U 与历史回执键的对应、每个回执自身的转移算术、同键回执唯一及现金事件背书。实际提交结果经 `consume_committed_origin` 导出其准入条件，再由 `Trace.u10_2_committed_executor_is_step` 接入混合轨迹。`u09_1_actual_trace_at_most_once` 只陈述安全性，不关闭恰一次活性或外部副作用。

`u09_1_scalar_vector_stream_refinement` 从初始数量投影证明候选标量支付流与基线向量支付流的最终余额一致；没有将最终投影相等放在前提里。它不证明法义解释、实际现金发生或完整产品事务精化。

`Learning.u01_0_independent_bounded_two_tail` 与 `u01_0_zero_width_tail` 覆盖一般独立有界和的正宽度/零宽度两支。`Feedback.u14_2_independent_cluster_two_tail` 规范化为簇大小公式，从 N>0 推出平方和正，而未增加这项独立前提。这些模块的对应源码已在正式模块构建中接受 Lean 检查；整体 CIAll 尚未通过。

`Pipeline` 实际传递第一步输出和刷新后输出。余额归零现在不会自动伪造外部测量；`n_pipeline_zero_balance_no_external_label` 要求缺少测量结果时仍返回未决并保留旧模型。`u10_2_pipeline_second_post_invariant` 连接实际第一步提交与第二步可确认后态。

## 八条必钉的候选位置

| 必钉 | 源码与验收入口 |
|---|---|
| U：Committed、YES、μ 齐，含合法零额；其余不写新 U | `Ledger.consume_ext`、`consume_success_is_gated`、`noncommit_does_not_write_U`；Acceptance 的 `a_zero_yes_writes_U`、`n_identity_unknown_no_U`、`n_applicability_unknown_no_U`、`n_not_applicable_zero_no_U` |
| 同案真实后态 | `Trace.correctStep`、`Pipeline.executePayments`、`u00_pipeline_wires_handles`；`n_non_continuous_consume`、`n_poststate_name_not_binding` |
| ExactExpr 为 ℚ | `Decision.ExactExpr`、`u06_3_eval_exists`、`u06_3_eval_unique`、`exact_ledger_bridge`；`n_exact_half_and_currency` |
| proposed 对基线逐项定位 | `proposed_825792b.json` 与 `baseline_reuse.json` |
| 三观察和 N-A1 | `forms_preserved_by_performance`；`a_u09_three_observations`、`n_a1_layer_collapse` |
| 返还三接口与 N1–N3 | `Ledger.RestClaim`、`ExecEligible`、`RestPay`；`a_rest_claim_then_eligibility`、`a_restpay_only_n3`、`n1_premature_cash`、`n2_auto_full_refund`、`n3_accrual_cash_collapse` |
| DS 六层 | `Interfaces` 模块注释和 `LogicalLayer` 枚举 |
| E09 负向和 BURNED_BY_UNKNOWN | Acceptance 的 `n09_*`、`n_burned_by_unknown`、`n_unknown_does_not_burn_U` |

Pipeline 成功、拒绝和未决均调用 `Pipeline.run`，对应 `u00_pipeline_success`、`u00_pipeline_reject`、`u00_pipeline_unknown`。最近的构建尚未通过 Acceptance，三者均未获 CI 证明，且固定合成例不能替代一般合成定理。UnknownCommit 没有可确认后态；本地 acknowledged U 不冒充未知服务器的 U。

## 第一轮 CI 失败与本地修复

GitHub 验证的实际 head 与授权 head 一致。目标计划确认为 `JurisLean.Candidates.Final20261021.CIAll`；固定工具链和 Mathlib 云缓存成功，构建实际执行。`Interfaces`、`Representation`、`Transactions` 在该 head 获得模块构建成功；这不是 50 条完整目标或 CIAll 的通过。

唯一报告的候选编译错误为 `Compiler.lean:125:2`：`unfold proposed_checked_rule_input` 留下局部 `let known`，随后的 `split at checked` 无法直接拆解。修复只增加 `dsimp only at checked`，先展开局部绑定，再沿原条件和原语义完备性命题证明；未改定理签名、前提、结论或运行函数。

原始工件 `changed-module-only-39689061670-1.zip` 的 SHA256 为 `2dfef73edd060ba0ee7b4f0cbdeab544edc296c1ade35eb6be8cdb96c67fe44b`，已与 GitHub 元数据核对。这一 Compiler 修复已由第二轮正式 CI 构建通过；CIAll 整体尚未通过。后续按连续 CI 授权推进，不重复派发旧 head。

## 必需工作与阻塞

完整 Beta 共轭与预测、全坐标 ridge logistic 极小值存在唯一、交换秩保形覆盖、一般可测分布 TV、条件测度/自适应预算、完整序贯政策、博弈背景与全路线精化等仍未闭合。**这些仍是任务义务，未移出验收。** 逐条缺口以 50 条表为准。

第一阶段正在连续修复并派发，目标为 `JurisLean.Candidates.Final20261021.CIAll`；即使该目标绿，也不代表上述数学义务完成。失败轮次、源 head 与原始工件逐轮保存。

第二阶段必须等第一阶段绿，接根后形成新 head，再按连续授权跑 full-release。现有 release 门禁的派生账本需要同步。具体接根与账本差异已准备在 `evidence/release-scope-proposal/outside-candidate-proposal.diff`，只在候选目录保存预案；目录外的账本范围尚待授权。未改任何 Lake、workflow、门禁配置或新建 lean_lib。

合成 Python 合同测试保存在本候选目录。现有 workflow 的 `tests/` 收集范围不会包含它，故其正式 Python CI 覆盖仍为 `NOT_RUN`。没有借修改 workflow、Lake 或根目录测试入口绕过此限制。

T113 原文、恰一次活性/外部效果、Dirty、全量中国法条映射继续作为明确排除的 OPEN 项；其他未闭合义务与这四项分别记账。JC/Harness 产品接线仍暂停。
