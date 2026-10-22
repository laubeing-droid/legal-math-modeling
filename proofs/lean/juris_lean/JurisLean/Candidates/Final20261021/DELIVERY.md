# Final20261021 候选施工检查点

状态：**PARTIAL_SOURCE_CANDIDATE / STAGE1_PASS / FULL_RELEASE_RETRY_PENDING**。批次 0–9 的候选源码及第一阶段正式 CI 已通过；接根后的首轮 full-release 中，干净 Lean 构建与现有数学审计通过，Python 派生账本检查失败，尚未获得全流程通过。冻结条目对应的 Lean 实现与接线义务仍按逐条表验收；这不表示底稿的数学证明缺失。

基线固定为 `825792b83476a767152396d7f5e2ba3017048841`，候选分支为 `candidates/final20261021-825792b`。run `39699620705` 已在 `d59a487b154818278ee4629234904bc8a3ac1ef3` 上通过完整目标 `JurisLean.Candidates.Final20261021.CIAll`；原始 ZIP、源 Git blob 对照、完整公理目标检查和回执见 `evidence/ci-stage1-d59a487/verification.json`。全部目标齐全，仅依赖标准公理。第一阶段通过只覆盖候选源码和所列 Lean 命题；完整冻结理论、产品精化与现实/法律前提未因此关闭。用户于 2026-10-22 授予连续 CI 修复、推送与派发授权。

## 逐模块与逐条复核入口

- `module_inventory.json`：每个模块的文件、理论编号、定理全名、操作入口及消费者行号、选定正反例和剩余义务。空例证栏明确表示缺少该类例证。
- `declarations.json`：声明与实际文本引用位置。文本引用不等于运行精化证明；空消费者不表示已被下游使用。
- `50_clause_status.json`：保留 50 条原始完整目标和验收句，列出候选声明与未闭合子目标；`formal_ci` 保留完整冻结条目的 `CI_NOT_RUN`；`candidate_formal_ci` 和具名回执另记已通过的候选声明，未把部分命题冒充整条关闭。存在源码、定理名或导入关系均不自动关闭条目。
- `proposed_825792b.json`：全部包内拟议符号及新增 `proposed_*` 对固定基线的 `REUSE/NEW/UNLOCATED` 判定；没有定位的目标保留 `UNLOCATED`。`NEW` 表示新候选边界，未声称等价覆盖原包中的全部软件合同。
- `baseline_reuse.json`：真正调用的基线数量账和 Horn 声明、源散列、原文及消费者；`candidate_provenance.json`：历史候选参考来源。历史候选的成功状态不转移到当前源码。
- `construction_status.json`：施工卡及三家验收附录来源、两阶段 CI 状态、限制与阻塞。

另有两个入口模块：`CIAll.lean` 显式导入全部实现模块与候选审计；`AxiomAudit.lean` 导入全部实现模块并逐声明执行 `#check` / `#print axioms`。二者没有新增定理声明；消费者分别是指定 CI 目标及 `CIAll`。最新完整构建已通过 Acceptance、AxiomAudit 与 CIAll；逐目标输出已经与完整源码清单核对。全部 Lean 文件的 Git blob 散列均列在本地回执中。

## 本检查点补强的内容

`Compiler.proposed_checked_rule_input` 只有在逐规则检查闭包稳定后才返回 Known。`u03_2_checked_closure_complete` 把实际检查结果接到相对语义完备性；不足燃料返回 `checkIncomplete`。尚未证明该列表实现的完整有限载体/燃料上界。

`Ledger.ReceiptCoherent` 分别检查 U 与历史回执键的对应、每个回执自身的转移算术、同键回执唯一及现金事件背书。实际提交结果经 `consume_committed_origin` 导出其准入条件，再由 `Trace.u10_2_committed_executor_is_step` 接入混合轨迹。`u09_1_actual_trace_at_most_once` 只陈述安全性，不关闭恰一次活性或外部副作用。

`u09_1_scalar_vector_stream_refinement` 从初始数量投影证明候选标量支付流与基线向量支付流的最终余额一致；没有将最终投影相等放在前提里。它不证明法义解释、实际现金发生或完整产品事务精化。

`Learning.u01_0_independent_bounded_two_tail` 与 `u01_0_zero_width_tail` 覆盖一般独立有界和的正宽度/零宽度两支。`Feedback.u14_2_independent_cluster_two_tail` 规范化为簇大小公式，从 N>0 推出平方和正，而未增加这项独立前提。这些模块的对应源码已在正式模块构建中接受 Lean 检查；整体 CIAll 已在上述精确源提交通过；完整理论范围仍按 50 条表保持开放。

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

Pipeline 成功、拒绝和未决均调用 `Pipeline.run`，对应 `u00_pipeline_success`、`u00_pipeline_reject`、`u00_pipeline_unknown`。最近构建已经通过这三条具体调用断言；它们仍不是一般全路线合成定理，且固定合成例不能替代一般合成定理。UnknownCommit 没有可确认后态；本地 acknowledged U 不冒充未知服务器的 U。

## 第一轮 CI 失败与本地修复

GitHub 验证的实际 head 与授权 head 一致。目标计划确认为 `JurisLean.Candidates.Final20261021.CIAll`；固定工具链和 Mathlib 云缓存成功，构建实际执行。`Interfaces`、`Representation`、`Transactions` 在该 head 获得模块构建成功；这不是 50 条完整目标或 CIAll 的通过。

唯一报告的候选编译错误为 `Compiler.lean:125:2`：`unfold proposed_checked_rule_input` 留下局部 `let known`，随后的 `split at checked` 无法直接拆解。修复只增加 `dsimp only at checked`，先展开局部绑定，再沿原条件和原语义完备性命题证明；未改定理签名、前提、结论或运行函数。

原始工件 `changed-module-only-39689061670-1.zip` 的 SHA256 为 `2dfef73edd060ba0ee7b4f0cbdeab544edc296c1ade35eb6be8cdb96c67fe44b`，已与 GitHub 元数据核对。这一段保留首轮失败及修复的历史事实；后续完整 CIAll 已在前述 d59a487/run 39699620705 通过。

## 必需工作与阻塞

当前候选尚未完成 Lean 落地与复证的范围包括：完整 Beta 共轭与预测、全坐标 ridge logistic 极小值存在唯一、交换秩保形覆盖、一般可测分布 TV、条件测度/自适应预算、完整序贯政策、博弈背景与全路线精化等。底稿中的纸面证明与当前分支的形式化完成状态分别记录。**这些仍是任务义务，未移出验收。** 逐条缺口以 50 条表为准。

第一阶段已经在前述精确 head 通过完整 CIAll 目标。接根后的 run `39700447562` 对应 `799b42c43d16e839ec3305577867120cb0deb917`；干净 Lean 构建、现有数学审计和既有 runtime-refinement 作业通过，Python 为 651 通过、13 失败。下游证书没有生成，整体 full-release 为 FAIL。原始工件及 head/digest 核验见 `evidence/ci-stage2-799b42c/verification.json`。

用户已明确授予完成本项目所需的全部授权。首轮 full-release 定位的 11 个派生账本、命名消歧及论文数字模板已按既有生成规则同步，现有相关测试 42 项通过；完整原有门禁将在新 head 的 full-release 中复跑。没有修改冻结理论、Lake、workflow 或门禁规则，也没有新增 lean_lib。

合成 Python 合同测试保存在本候选目录。现有 workflow 的 `tests/` 收集范围不会包含它，故其正式 Python CI 覆盖仍为 `NOT_RUN`。没有借修改 workflow、Lake 或根目录测试入口绕过此限制。

T113 原文、恰一次活性/外部效果、Dirty、全量中国法条映射继续作为明确排除的 OPEN 项；其他未闭合义务与这四项分别记账。JC/Harness 产品接线仍暂停。
