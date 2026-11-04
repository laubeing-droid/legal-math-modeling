# 原题 09.6：形成、真实支付、清偿与未成立后的效果

**状态：** 冻结原题的有限数值/状态见证与 conditional quantity/cash update 映射为 COVERED；本轮 11 项 records 检查与 index 测试均通过；独立 records 复核与完整 PR/post-merge 接受仍待完成。源 checkpoint `a9a65abcd6576f32e1bc5cd60d1e48ffaeb749ce`，tree `6ab85fb1afb541f28bbd49e30656407ab96c04f4`，parent `8059e33665749bef069e746bb835864389ecb3e3`。changed-module run [`41787704361:1`](https://github.com/laubeing-droid/legal-math-modeling/actions/runs/41787704361)，job `126433553869`，只构建 `JurisLean.Candidates.WitnessedCashAllocationAudit20261104`。Artifact `changed-module-only-41787704361-1`, ID `13302241704` 的 ZIP 为 2368 字节，SHA-256 `4c124af5ab90578864820cdfb28d554323d17aadfef7a6a69e4445ee577cf119`；本包 `changed-module.log` 与 `module-plan.json` 是 ZIP 成员的原始字节拷贝。CI 有 6 组 theorem `#check`/`#print axioms`、2 个定义检查，错误 0、`sorryAx` 0。各目标实际 axiom 集、直接 source/toolchain pins 与命令边界见 `verification.json`。

## 冻结条文与源证据

冻结题单 `09_关系效果数量账本与履行.md` L177–184，子项 L179、L181、L183，关联 `U09.3` 与 `U09.2`。新模块的六个公开目标完整 FQN 列在 `verification.json`；证明只把冻结原题给定的外部合法分配量 `k`、付款事实与当前账本数量关系连接到实际状态更新，没有从算术界推出法律规则、现实支付已发生或协议已接受。

- **L179：** `arbitrary_k_same_state_update` 使用旧状态中的实际 `Ledger.quantity` 见证与 `0 ≤ k ≤ min(payment, debt)`，证明实际 `allocationPost` 后数量为 `d-k`、非负、余额分解、现金事件追加和对应的 paid/allocated/surplus 更新；未要求付款人与债务人身份相等。`performance_is_min_allocation` 记录当前 V2 `performance` 的最小分配实例，不能据此声称 V2 已支持一般 Theta 法律规则。
- **L181：** `unformed_option_none_cash_six` 给出数量查询为 `none` 时，原始状态仍可记录 cash 6，且状态变化；这是纯模型中的 raw event 反例，不表示它通过 validated payment protocol。`formed_four_cash_six_allocates_four` 给出已形成的 toy 账本中收到 6、清偿 4、余款 2 的计算实例。
- **L183：** `allocationPost_record_frame` 证明实际状态更新的记录字段 frame，`allocationPost_cash_consistent` 证明现金一致性保持，`arbitrary_k_same_state_update` 给出数量更新与现金/程序字段关系。旧 `next_performance_is_identity` 只针对 Seams 的关系表（`forms`），不推出整个 State 的债务/诉权效力。没有 actual caller 消费本轮 ToyTheta/conditional producer。

R1 run [`41786834570:1`](https://github.com/laubeing-droid/legal-math-modeling/actions/runs/41786834570)，Artifact `changed-module-only-41786834570-1`, ID `13301587538` 是失败历史，不能作为成功证据。R1 的三处 Lean 错误只在 `hqFacts` 取分量、余额改写和数量定义展开处；R2 仅改这三段 proof body，结论、量词、前提、模型定义与 `PaymentPayload` 现金字段均未改变。R1 恢复输出含 `sorryAx`，R1/R2 源文件均无显式 `sorry`/`admit`/新 `axiom`；R2 成功输出不含 `sorryAx`。

## 边界

本轮证明覆盖明示的账本数据、分配数值、状态与现金记录关系。Theta/事实对合法 `k` 的依据、真实法律效果以及真实支付事件的发生由原题输入给定；这些不能由本模块的数值界或 Toy 例子推出。现有 U00 15 条消费边中没有实际 caller 消费本轮 witness，因此 `affected_edges=[]`，不改 U00 边或评级。U09.3 是已关闭条目，不因本记录重开。全局 discharges、Step 2、`math_flip` 仍为 false；本模块 changed-module 通过不等于全理论/全链完成或 PR 已接受。