# U06.5：噪声信息与给定议价树的有限实例

冻结归档的原始残余原文如下：

> Signal value 3/10-cost, cost>3/10 net negative, given two-round tree (4,6), and matching-pennies no pure equilibrium are named. Brouwer/mixed equilibrium is not claimed. Hidden-information sequential equilibrium is not bi_one_step_no_gain. T113 perfect-information carrier remains JurisLean.Seams.UnifiedW4Games.bi_one_step_no_gain and is not re-labeled as the original hidden-information statement. formal_ci records run 39783481932, whose lean-full-clean-build compiled these declarations. That run does not discharge Brouwer/mixed equilibrium or hidden-information sequential equilibrium.

本包绑定独立 source `9945f1710a7d8067ebeb264ed35d28b4394a1c33`，run `41136762457` / attempt 1 / job `124341022636`，driver 为 `U06_5OriginalClosureAudit20261031.lean`。实际 Artifact `13016933102`（`changed-module-only-41136762457-1`）为 6115 bytes，SHA-256 `c8056bfd68b444fe64ffea029b89f1d514d1ff6128b1d1ff2d36b4b3d21eefdb`；实际 ZIP 的 `module-plan.json` 与 `changed-module.log` 指纹、从后者抽取的 9 个 driver 输出块见 `verification.json` 和 `axiom-audit.raw.txt`。9块含3个 theorem type、对应3个 axioms 输出和3个对象类型；每个目标仅依赖 `propext`、`Classical.choice`、`Quot.sound`。

- `signal_joint_law` 在实际归一化四原子联合测度下给出状态边际 1/2、条件信号命中率 4/5 及联合正确概率 4/5。
- `signal_information_values` 对同一 law 比较不看信号的 1/2 与读取信号的 4/5，净信息价值为 `3/10 - k`，且正收益恰在 `k < 3/10`。
- `bargain_backward_induction` 对已给两轮完全信息树按节点逆推，复用既有 W4 结构并计算新终局效用；每人 delay loss 为 1、failure payoff 为 -1，导出该具体策略结果 `(4,6)` 并证明其对所有完整单方偏离的最优性。

匹配硬币无纯均衡由已存在的 `JurisLean.Candidates.Final20261021.Decision.u06_5_matching_pennies_no_pure` 保留为既有引用。混合 Nash/Brouwer 背景复用已合并 main 的 `GameTheory.KernelGame.nash_fp_is_nash`、`GameTheory.KernelGame.mixed_nash_exists` 和 `GameTheory.brouwer_mixedSimplex`；它们已在 canonical `JurisLean/AxiomAudit.lean`（L3943、L3960、L3984）并由 PR80 Authority run `41167738968` / Lean job `124438858543` 实际审计为标准三公理。它们是先前接受的复用证据，不计入本轮 driver 的9块或此包的3个目标。

本包没有重做一般均衡存在证明；隐藏信息顺序均衡也没有被 `bi_one_step_no_gain` 替代。原题 06.7 的其他一般条件及七问整体义务仍依原状态。此证据仅支持归档 U06.5 的有限范围，不改全局 discharges、Step 2、math_flip，也不声称旧 Pipeline 数值消费者已接线。
