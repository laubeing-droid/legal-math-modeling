# 原题 10.4：部分步骤的门控与失败路径边界

**状态：** Source R2 changed-module CI、11 项记录检查、gap-status 检查与两项 targeted paper 回归均通过；CI-index 引用与最终检查结果记于 verification.json；PR 全链验收仍待完成。R1 失败保留为历史。来源：R1 [41927109528](https://github.com/laubeing-droid/legal-math-modeling/actions/runs/41927109528)；R2 [41928458830](https://github.com/laubeing-droid/legal-math-modeling/actions/runs/41928458830)。

冻结题单 10_授权变更与多步法律轨迹.md L123–130，子项 L125、L127、L129，关联 U02.2 与 U10.2。本轮只映射这三段，保留外部授权目录与来源身份输入条件。

- **L125：** Pre_i、Step_i、Post_i 与 Frame_i 给出现有 Ledger.consume_ext 的局部契约。actual_committed_step_satisfies_local_contract 从实际 committed 结果推出正向适用、给定身份、实际前态、未消费标记与本题前后态条件；checked_payment_commit_exposes_a_current_grant 将实际 Pipeline permission 连到当前 query 下被检查通过的 catalog Grant。unknown_negative_and_conflict_are_distinct_framed_outcomes 保留 unknown、negative 与 payload conflict 的区别，并有把 unknown 错误扣入 10→3 的有限反例。
- **L127：** noncommit_returned_state_has_full_frame 证明有返回 post 的 noncommit 分支保留整个 Handle，包括其中 L/Q/N、env 等业务字段。unknown_commit_has_no_returned_post 明确该分支的 post 为 none；acknowledgedUsed 只刻画客户端承认视图，不推出服务器未提交。replay 是既有回执承认，不是新业务提交；诊断不算履行、形成或授权完成。
- **L129：** retry_matches_current_context_and_consumes_the_given_key_once 与 actual_pipeline_retry_rechecks_witness_and_prevents_double_effect 展示旧 Grant 在新上下文被拒、显式给定的合成当前 Grant 可使实际 Pipeline 提交、同 key 再试为 replay。现实来源身份直接复用 SourcePaymentIdentity20261103.sourced_calls_with_same_payment_id_are_at_most_once：它针对同一 consume_ext，以前提 samePaymentId、先前实际 commit 与中间 Trace.Path 推出后续调用不能再次 committed。finite_payment_identity_and_retry_outcomes 保留身份未判明与同 cash 冲突的有限分支；有限实例不判明现实身份，也不证明不同内部 ID 对应不同现实付款。

Source R2 报告 7 个本模块自有目标与 12 个复用目标，共 19 对 #check / #print axioms。本模块的目标按各自输出仅依赖 propext、Classical.choice、Quot.sound 的标准公理。当前 catalog Grant 的真实性与外部来源身份仍是显式输入，不由修改 Gamma 或给定当前 Grant 推出。

十五边复核表的边 8（事务→账本）补登记本轮实际 committed post/frame、unknownCommit 无返回 post 与同 key replay；边 9（账本→授权/轨迹）补登记实际当前 Handle/payload 授权检查及显式 source identity/Trace consumption 前提。见[本轮关债包](README.md)与独立[source CI](https://github.com/laubeing-droid/legal-math-modeling/actions/runs/41928458830)。两项均为 evidence-registration-only：不改 caller、接口或边评级，不升级旧 U00 接线、旧 Pipeline 完整合同、现实授权或现实身份结论。

总账只将原题 10.4 从 NOT_RECONCILED 调为 COVERED，原题计数为 75 COVERED / 15 PARTIAL / 7 NOT_RECONCILED。97 题、266 子段、105 项工程要求与 6 个 designated cuts 分母不变；全局 discharges、Step 2 与 math_flip 仍为 false。

## Source 结果与失败历史

Source checkpoint 3aab453192b76b0aa66a3448b571ffe97e4fb8ac，tree a6931ccaa637326fb5f1feb0beade23cd997d102，parent 5cb9564f9d825dd814cf20fdbd890050e7fc8bf9，base main 367bb4b8fa1afe7258ff53f764c034eb40ffb0eb。R2 run 41928458830, attempt 1, job 126918981036 成功；该 workflow_dispatch 只构建 changed-module，不是全链或 PR 验收。

Artifact changed-module-only-41928458830-1, ID 13370308358：ZIP 27475 bytes，SHA-256 1978b36963d421c5604655b6319d7f2b6696cebea36aeb9fe81cfcb593f2fc3a。module-plan.json 与 changed-module.log 是 ZIP 成员原始字节，大小与 SHA、19 项目标及逐项公理输出见 verification.json。R2 error 数为 0，sorryAx 数为 0。

R1 run 41927109528 / Artifact changed-module-only-41927109528-1, ID 13368479327 为失败历史：L175 的全局 simp_all 超过 200000 heartbeat/最大步数，L165 同一证明随后超时；该目标打印出 sorryAx，不计为通过。R2 只替换该证明中的局部 tactic 两行，没有改声明、参数、前提或 heartbeat 限制。R1 ZIP 为 28072 bytes，SHA-256 3d219102236cb82e4ca70ba32767d5d36461fa44841ac904031c8990b2bdc229；原始 artifact 与 log 保留在 Dtmp。

结构测试在初始 source checkpoint 运行一次并通过（17 passed in 5.25s）；R2 只改 proof tactic，未重跑结构测试。11 项记录检查、gap-status、两项 paper 回归与 CI-index 的实际结果和收据记于 verification.json 与 Dtmp；均不替代 PR 全链验收。

## 记录范围

本包绑定 frozen 10.4 的 L125/L127/L129、R2 source subject、tree 与 changed-module artifact。verification.json 区分 7 个本模块目标、12 个复用目标、R1 失败历史、逐项公理输出与 source pins。有限构造不证明现实授权签发、现实来源身份、法律正确性或生产运行时部署。
