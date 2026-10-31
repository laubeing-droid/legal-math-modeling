# Final20261021 候选施工检查点

状态：**PARTIAL_SOURCE_CANDIDATE / STAGE1_PASS / FULL_RELEASE_PASS_ON_5db4e04**。批次 0–9 的候选源码及第一阶段正式 CI 已通过。接根后的 full-release 已在 main 尖端 `5db4e0453d77493e2699af7b32bcb1ea8c7668a5` 的 run `39714740194` 通过：该次是 push 触发的完整发布路径，干净 Lean 构建、Python 门禁、七轴、数学完成、发布证书与 final-gate 均为 success，`changed-modules` 作业按该路径跳过。那次 run `39714740194` 是该树的仓库流水线通过，当时还不是 50 条冻结条款的 `formal_ci` 关闭。`50_clause_status.json` 的 `formal_ci` 在声明能对上尖端回执时写入该回执里的 run id，回执文件是 `evidence/ci-tip-f85ebe44/verification.json`（尖端 `f85ebe44644f32820e9d0fad1325428fb8f171d9`，Authority run `40115638107`，作业名 `lean-full-clean-build`，job id 写在该回执里）。该回执从该尖端 `lean-full-clean-build` 工件重新抽出公理审计，并 `supersedes` `evidence/ci-tip-e87543d8/verification.json`。活的 `exact_scope` 与 `remaining_obligations` 为空。`evidence/ci-tip-f85ebe44/scope-archive.json` 原样沿用 `evidence/ci-tip-e87543d8/scope-archive.json` 上的原稿（原稿仍钉在 `966b937394a07d14e58098b786e5bf742edd6b23`），不是从已清空的尖端重抽，也不是 Lean 证明。旧目录 `evidence/ci-tip-e87543d8/` 保留为史档。这次只重钉尖端：重钉≠关债 / retarget ≠ close debt。第2步不关。


Live tip-pin expand-audit (CAND5+CAND5bis named_count=37; closes_debt=false; OPEN=35): evidence/ci-tip-dc7b7430/verification.json on subject dc7b7430198fa221b5d72d55fc6065a928209dc4 / Authority run 40190504653 (lean-full-clean-build). Historical evidence/ci-tip-f85ebe44/verification.json stays named_count=25.

Live tip-pin expand-audit CAND6 (CAND5+CAND5bis+CAND6 named_count=49; closes_debt=false; OPEN=30; this expand closed increment=0): evidence/ci-tip-1c72e444/verification.json on subject 1c72e444ab79ff255af201f100aa6a93bdc0e5c7 / Authority run 40257646857 (lean-full-clean-build; job id is in that receipt). Historical evidence/ci-tip-dc7b7430/verification.json stays named_count=37. Retarget ≠ close debt.

Live tip-pin expand-audit CAND7 (CAND5+CAND5bis+CAND6+CAND7 named_count=61; closes_debt=false; OPEN=25; this expand closed increment=0): evidence/ci-tip-21862d9b/verification.json on subject 21862d9bdd94bfa15e5da39079538b5eb30ff235 / Authority run 40274167574 (lean-full-clean-build; job id is in that receipt). U07.1 / U02.3 / U04.3 / U05.2 / U06.3 are candidate_in_tip_pin_audit only, disposition stays CANDIDATE_NOT_AUDITED, not CLOSED. Historical evidence/ci-tip-1c72e444/verification.json stays named_count=49. Retarget ≠ close debt.

基线固定为 `825792b83476a767152396d7f5e2ba3017048841`，候选分支为 `candidates/final20261021-825792b`。run `39699620705` 已在 `d59a487b154818278ee4629234904bc8a3ac1ef3` 上通过完整目标 `JurisLean.Candidates.Final20261021.CIAll`；原始 ZIP、源 Git blob 对照、完整公理目标检查和回执见 `evidence/ci-stage1-d59a487/verification.json`。全部目标齐全，仅依赖标准公理。第一阶段通过只覆盖候选源码和所列 Lean 命题；完整冻结理论、产品精化与现实/法律前提未因此关闭。用户于 2026-10-22 授予连续 CI 修复、推送与派发授权。

## 逐模块与逐条复核入口

- `module_inventory.json`：每个模块的文件、理论编号、定理全名、操作入口及消费者行号、选定正反例和剩余义务。空例证栏明确表示缺少该类例证。
- `declarations.json`：声明与实际文本引用位置。文本引用不等于运行精化证明；空消费者不表示已被下游使用。
- `50_clause_status.json`：列出候选声明。`formal_ci` 在声明能对上尖端回执时写入该回执的 run id；对不上的仍为 `CI_NOT_RUN`。活的 `exact_scope` 与 `remaining_obligations` 为空，表示所列声明已出现在重新抽出的公理审计里且只依赖标准公理。原稿句子在 `evidence/ci-tip-f85ebe44/scope-archive.json`（沿用 `evidence/ci-tip-e87543d8/scope-archive.json`，再沿用 `evidence/ci-tip-966b9373/scope-archive.json` 的原文），不把归档句子当成已证。携带原稿不是证明。`candidate_formal_ci` 不使用通过字样。
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
| 返还三接口与 N1–N3 | `Ledger.RestClaim`、`ExecEligible`、`RestPay`；`a_rest_claim_then_eligibility`、`a_restpay_only_n3`、`n1_premature_cash`、`n_rest_not_eligible`、`n2_auto_full_refund`、`n3_accrual_cash_collapse`。`restNotEligible` 只表示尚未 ExecEligible；`autoFullRefund` 只表示退款金额等于已入账履行额 `paid`（`a = payable`） |
| DS 六层 | `Interfaces` 模块注释和 `LogicalLayer` 枚举 |
| E09 负向和 BURNED_BY_UNKNOWN | Acceptance 的 `n09_*`、`n_burned_by_unknown`、`n_unknown_does_not_burn_U` |

Pipeline 成功、拒绝和未决均调用 `Pipeline.run`，对应 `u00_pipeline_success`、`u00_pipeline_reject`、`u00_pipeline_unknown`。最近构建已经通过这三条具体调用断言；它们仍不是一般全路线合成定理，且固定合成例不能替代一般合成定理。UnknownCommit 没有可确认后态；本地 acknowledged U 不冒充未知服务器的 U。

## 第一轮 CI 失败与本地修复

GitHub 验证的实际 head 与授权 head 一致。目标计划确认为 `JurisLean.Candidates.Final20261021.CIAll`；固定工具链和 Mathlib 云缓存成功，构建实际执行。`Interfaces`、`Representation`、`Transactions` 在该 head 获得模块构建成功；这不是 50 条完整目标或 CIAll 的通过。

唯一报告的候选编译错误为 `Compiler.lean:125:2`：`unfold proposed_checked_rule_input` 留下局部 `let known`，随后的 `split at checked` 无法直接拆解。修复只增加 `dsimp only at checked`，先展开局部绑定，再沿原条件和原语义完备性命题证明；未改定理签名、前提、结论或运行函数。

原始工件 `changed-module-only-39689061670-1.zip` 的 SHA256 为 `2dfef73edd060ba0ee7b4f0cbdeab544edc296c1ade35eb6be8cdb96c67fe44b`，已与 GitHub 元数据核对。这一段保留首轮失败及修复的历史事实；后续完整 CIAll 已在前述 d59a487/run 39699620705 通过。

## 必需工作与阻塞

七个原先没有具名声明的条款已写入候选定理，其 `formal_ci` 记入同一尖端回执，不是验收通过：U01.4 的有限反例与两种均值方差、U02.4 的分区预算与 H=B 反例、U04.1 对已证整型 Beta 共轭/预测均值/Gamma 权重比的引用及 5/6 对 2/3 的交换反例、U04.3 的未罚截距反例、U04.4 的协方差展开与退化见证、U05.1 的无同分秩门槛、U06.5 的信号价值、给定两轮树 (4,6) 与匹配硬币无纯均衡。归档仍保留、且本回执没有证明的句子包括：非整数密度逐点共轭、全坐标受罚逻辑回归的存在唯一、连续破同分密度、一般滤过塔、Brouwer 混合均衡，以及隐藏信息序贯均衡。活表这两栏为空，只表示所列声明通过了重新抽出的公理审计。七条款法源清单见 `evidence/seven_clause_legal_sources.txt`：这七条的底稿都是数学命题，法律全称至原文摘录标「无法源」并写了理由，另记模型原意和定义位置，没有填写推测法条。逐条原稿以 scope archive 为准。

第一阶段已经在前述精确 head 通过完整 CIAll 目标。接根后的 run `39700447562` 对应 `799b42c43d16e839ec3305577867120cb0deb917`；干净 Lean 构建、现有数学审计和既有 runtime-refinement 作业通过，Python 为 651 通过、13 失败。下游证书没有生成，该次 full-release 为 FAIL。原始工件及 head/digest 核验见 `evidence/ci-stage2-799b42c/verification.json`。

2026-10-31 API复核注记：当前 GitHub Actions API 对 run 39700447562 返回 HTTP 404；上段失败、head 与作业信息保留自历史索引快照，现标为 UNAVAILABLE，不代表当前API复核或本轮通过。

同一流水线在派生账本同步之后的 main 尖端 `5db4e0453d77493e2699af7b32bcb1ea8c7668a5` 上由 push 触发，run `39714740194` 结论为 success。作业结论来自 Actions API：`lean-full-clean-build`、`python-gates`、`runtime-refinement / produce`、`seven-axis-acceptance`、`mathematics-completion`、`release-certificate`、`final-gate` 为 success，`changed-modules` 为 skipped。API 列出的工件名称与编号见 `evidence/ci-stage2-5db4e04/verification.json`。该回执没有重新下载 ZIP，因此不记录工件字节散列。这次通过不把 50 条冻结条款的 `formal_ci` 改成验收通过，也不覆盖此后的源码修正。此后尖端的公理审计见 `evidence/ci-tip-f85ebe44/verification.json`，由尖端 `f85ebe44644f32820e9d0fad1325428fb8f171d9` 的 run `40115638107` `lean-full-clean-build` 工件重新抽出（job id 写在该回执里）。活的 `exact_scope` 与 `remaining_obligations` 为空；scope archive 沿用上一尖端原稿，没有因此变成证明，也不关闭归档债务。重钉≠关债 / retarget ≠ close debt。

用户已明确授予完成本项目所需的全部授权。首轮 full-release 定位的 11 个派生账本、命名消歧及论文数字模板已按既有生成规则同步。没有修改冻结理论、Lake、workflow 或门禁规则，也没有新增 lean_lib。

合成 Python 合同测试保存在本候选目录。现有 workflow 的 `tests/` 收集范围不会包含它，故其正式 Python CI 覆盖仍为 `NOT_RUN`。没有借修改 workflow、Lake 或根目录测试入口绕过此限制。

T113 原文、恰一次活性/外部效果、Dirty、全量中国法条映射不再作为排除项，改为范围内未关闭债务。完全信息两轮后向归纳的既有载体是 `JurisLean.Seams.UnifiedW4Games.bi_one_step_no_gain`，隐藏信息序贯均衡不在该定理内。`Transactions.at_most_once` 只是至多一次，不是外部效果下的恰好一次活性。Dirty 精化与全量中国法条逐条映射在本树中没有可引用的关闭声明。四项都未关闭。JC/Harness 产品接线仍暂停。

## 归档 50 条关项层（2026-10-24）

`evidence/archive-gap-close-20261024/close-ledger.json` 按判据包 `/home/box/shared/legal-math-reviewer/archive_gap_判据包_20261024/`（`未决改判_20261024.md`、`施工放行条件.md`）处理 50 条原稿：证 42、缩 8、放弃 0。缩域 8 条把残留写成同条显式非目标；证只把候选体接到活钉重新抽出的声明上。活钉已从 `e87543d836cd3cf83bbb5a65b74e47d9bfe31865` / run `39933015422` / `evidence/ci-tip-e87543d8/` 重钉到 `f85ebe44644f32820e9d0fad1325428fb8f171d9` / run `40115638107` / `evidence/ci-tip-f85ebe44/verification.json`。两份回执的作业名都是 `lean-full-clean-build`，job id 写在回执里。没有对应声明的形式尾巴保持 `OPEN_FORMAL_TAIL`（40 条），其中 U04.3 的全坐标受罚存在唯一仍是 UNPROVED。本 PR 不关任何 `OPEN_FORMAL_TAIL`，不把 candidate 升为关项。`scope-archive.json` 原稿未改、未清空；新目录只携带旧原稿。`discharges_archived_manuscript_gaps` 仍为 false，`math_flip_authorized` 仍为 false。第2步不关。账本里的 `tip_authority_run_gate_only` 只是门禁，不关这笔债。重钉≠关债 / retarget ≠ close debt。中国法栏未改。

## tip-pin ??? CAND5?2026-10-25?

`evidence/ci-tip-f85ebe44/verification.json` ?? FormalTail20261024 ? 25 ??????U06.4?U08.1?U10.3?U12.2?U14.2???? `candidate_in_tip_pin_audit=true`?????????????????? tip-pin `27849d3f`?id `40079130550` ???? FormalTail ???? tip_pin ???? BOUND?`f85ebe44?`?run `40115638107`?lean-full-clean-build?job id ???????tip Authority SUCCESS??`discharges_archived_manuscript_gaps` ? false?`math_flip_authorized` ? false?`OPEN_FORMAL_TAIL` ? 40?`closed_this_round` ? 0?disposition ? `CANDIDATE_NOT_AUDITED`?????????????U10.3 companion ??????????????2????
