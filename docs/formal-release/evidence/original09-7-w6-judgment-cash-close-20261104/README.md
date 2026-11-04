# 原题 09.7：W6+ 中裁判与再次支付怎样避免双扣、复制原债或漏记现金？

**状态：** 冻结原题 L187–L200 映射到有限同一 Theta 的三个世界、W6 观察与现金投影，以及条件性、来源绑定的 rJ 分支；本轮 11 项 records 检查与 12 项 CI-index 测试均通过；独立 records 复核与完整 PR/post-merge 接受仍待完成。Source checkpoint `87b7fe1b1054d610c70bef76055fb8074b92c8ea`，tree `fc074202bf6f02de6c7b86ba7d6bdcfffa02c84e`，parent `8856a737c7d7f91373ded1371de8f5ebcf422925`。changed-module run [`41807723062:1`](https://github.com/laubeing-droid/legal-math-modeling/actions/runs/41807723062)，job `126498847023`，只构建 `JurisLean.Candidates.W6JudgmentCashAudit20261104`。Artifact `changed-module-only-41807723062-1`, ID `13310766708` 的 ZIP 为 2067 字节，SHA-256 `956fad59522a9f0ed01ae422a676e390302a7fd817be5488069eafd5b0239c04`；本包 `changed-module.log` 与 `module-plan.json` 是 ZIP 成员的原始字节拷贝。CI 有 9 组 theorem `#check`/`#print axioms`、2 个定义检查，错误 0、`sorryAx` 0；各目标 axiom 集与直接 source/toolchain pins 见 `verification.json`。

## 冻结条文与源证据

冻结题单 `09_关系效果数量账本与履行.md` L185–201，子项 L187、L189、L191–196、L198、L200，关联 `U09.3`。九个公开目标的完整 FQN 列在 `verification.json`。模型显式限定为有限抽象 Theta 和给定输入，不将其称为现实法域或协议验收。

- **L187/L189：** `four_stage_numeric_and_cash_witness` 给出四阶段状态、数量与现金记录关系；`timed_X_is_actual_cash_projection` 将 X 绑定到模型中的第二债项现金投影；`raw_stages_reuse_existing_invariants` 复用现有守恒/现金不变量。实例使用不同现金事件 ID，并在给定前提下区分裁判真值与现金真值，避免再次扣减或复制原债。
- **L191–L196：** `toyWorlds_satisfy_one_Theta` 与 `toyWorlds_share_same_observed_W6` 给出同一 context、同一 W6 观察下的三个有限世界；`Bp_does_not_semantically_entail_Bn`、`Bn_does_not_semantically_entail_E`、`E_does_not_semantically_entail_X` 是三项非蕴含见证。X 仅按 toy model 定义为第二债项的实际现金投影。
- **L198/L200：** `conditional_rJ_branch_is_separate_and_source_bound` 只证明命题列出的条件性 rJ 分支与来源绑定，不增造额外 Theta 规则或一般兼容性结论。

R1 run [`41804371257:1`](https://github.com/laubeing-droid/legal-math-modeling/actions/runs/41804371257)，Artifact `changed-module-only-41804371257-1`, ID `13309950968` 是失败历史，不能作为成功证据；保留 reserved field `at` 引起的 parser cascade 与恢复输出 9 个目标含 `sorryAx`。R2 run [`41806734801:1`](https://github.com/laubeing-droid/legal-math-modeling/actions/runs/41806734801)，Artifact `changed-module-only-41806734801-1`, ID `13309902910` 也是失败历史；唯一 proof blocker 是 `toyWorld_is_a_Theta_model` 中 `scopedBool` 投影等式未展开，4 个依赖目标的恢复报告含 `sorryAx`。R3 仅将 `scopedBool` 添入该 helper 既有 `simp` 展开列表；原模型、前提与目标未变。

## 边界

证据限于显式构造的有限抽象 Theta、三个模型及声明前提。它不证明任意 Theta、现实法律体系或任意层兼容；抽象现金投影不证明现实付款发生或通过 validated protocol。U00 当前 15 条消费边均无实际 caller 消费本 witness，因此 `affected_edges=[]`，不改边或评级。U09.3 保持已关闭，本轮不重开。全局 discharges、Step 2、`math_flip` 仍为 false；本模块 changed-module 通过不等于全理论完成或 PR 已接受。
