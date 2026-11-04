# 原题 09.8：返还流程与双账守恒怎样有限闭合，而不抹写历史？

**状态：** Source R3 已通过 changed-module CI；本轮 11 项必需记录检查及 12 项 CI-index 测试均通过，独立记录复核与 PR 接受仍待完成。证据绑定 source checkpoint `88f29a6a029de736607650ea01cf738419e3adc1`，tree `71f3562ce57842bb1dd2faef71519bcb4ebd09cb`，parent `68fecb20e70f7a9a3b894871c03d0458f8452c6a`。R3 run [`41825560137:1`](https://github.com/laubeing-droid/legal-math-modeling/actions/runs/41825560137)，job `126559282946`，只构建 `JurisLean.Candidates.RestitutionFiniteClosureAudit20261104`。Artifact `changed-module-only-41825560137-1`, ID `13318902082`，官方 ZIP 4620 字节，SHA-256 `16fe95102e81791bf92b58f2068c637d78e3844f4d8778aba4f4e68bd9a17594`；本包 `changed-module.log` 与 `module-plan.json` 是 ZIP 成员的原始字节副本。R3 raw 显示 8516 jobs build 完成、9 个 theorem 检查/axiom 输出、2 个定义检查、错误 0、`sorryAx` 0；逐目标 axiom 集与 source pins 见 `verification.json`。

## 冻结条文与源证据

冻结题单 `09_关系效果数量账本与履行.md` L202–209，子项 L204、L206、L208，关联 U09.2 与 U09.3。九个本题 public target 的 FQN 列在 `verification.json`。本模块是给定有效提取、明确 Θ 输出与有限状态/轨迹条件下的数学生产者；不证明现实来源真实性、任意 parser 正确性、现实法域规则或协议验收。

- **L204：** `first_two_stages_no_cash` 和 `q_receipt_is_actual_event_and_history` 将 RestClaim 与 ExecEligible 的两阶段构造连接现有无现金定理。q 是返还 `PaymentRequest` 的 `PaymentId`；完整来源、norm、payer/payee、关系、金额和 cashId 仍在 payload/receipt 中，实际返还事件由 payload 构造，不以相等金额混同事件身份。Ready 要求显式原债/新返还输入提取、身份、案件与版本、适用门、不同支付和关系、单位、未使用身份、额度边界及新现金身份条件。
- **L206：** `separated_quantity_and_cash_components` 在既有 `Conserves` 与 `CashConsistent` 前提下保持原 I+newDebt+accrual = allocated+balance+writeoff、paid 与 paid=allocated+surplus；新返还债额为 R−k，非负且 R=k+(R−k)，实际返还额 a 独立保留 a=k+(a−k)。`refundPost` 保留旧 paid、allocated、surplus 与 cash 历史，另记新 rest 余额和 refundCash。`actual_closed_account_conservation` 将完整既有事件清单与新事件接到同一有限账户集合：输入清单完整覆盖旧现金、单位一致、主体投影为原事件的真实 payer/payee，闭合账户和为零。`joint_from_actual_trace` 将这些条件与有限 Trace 初态不变量连接。一般 Θ 给定 k 的数量生产者与 `legacy_RestPay_is_min_branch` 的 min 且金额门控分支分开；两例都具体应用了旧 RestPay 分支，但不声称一般 Θ 已接入生产协议。
- **L208：** `cash_balance_does_not_supply_admission` 展示账户现金平衡本身不足以让未经授权、超额或未明确规则的 effect 入场。`ten_seven_seven_nonempty_witness` 使用 Acceptance 的两步实际 Trace（10/7/7）连接数量、事件与条件性 RestPay；`w6_nonempty_witness` 以 W6+ 状态和已有初态不变量为起点连接返还数量、现金、J 与 V，保留 V.insufficient。W6 的 nil 路径仅表示新返还前没有额外全局协议步，不把先前 raw performance 当成 validated 协议。

原题给定的 Extractor 输出是完整、规范化的 PaymentRequest；Option Rule 中 none 不准入。模型不从现金守恒推出返还权，不按金额相等推断身份，也不把实际事件发生、来源真实性或法律认可从数学条件自动推出。U00 当前 15 条消费边没有实际 caller 消费本 finite producer，本轮 `affected_edges=[]`，不改 edge 评级或造新边。U09.3 保持已关闭，本轮不重开。

## 失败历史与范围

R1 run [`41823095980:1`](https://github.com/laubeing-droid/legal-math-modeling/actions/runs/41823095980)，Artifact `changed-module-only-41823095980-1`, ID `13316624404` 是失败历史：claimPost record 布局导致 parser cascade，另有事件成员分支与数值命题 tactic 错误；恢复输出中 5 个目标含 `sorryAx`。R2 run [`41824812639:1`](https://github.com/laubeing-droid/legal-math-modeling/actions/runs/41824812639)，Artifact `changed-module-only-41824812639-1`, ID `13317444139` 也是失败历史：仅余 q_receipt 数量投影 proof 未展开 `Ledger.balance`。R3 只修复记录排版、两个事件清单 membership 证明、两个数字命题的展开及 balance 投影化简；命题、前提、导入与其他定义保持不变。

Source CI、records 检查与同 C 验收分别计量。Changed-module 通过不等于全模型完成或 PR 已接受；global discharges、Step 2 与 `math_flip` 仍为 false，D5 保持 NOT_RECONCILED。
