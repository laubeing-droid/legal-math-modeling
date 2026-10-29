# U04.2 原始识别区间与条件化污染界：OPEN 8 → 7

本包只针对冻结 U04.2 的原始残余。独立审计绑定源码提交 `5c8cf787c1d545a0ab1e037fa793d8f6417b886e`、changed-module run `40879691794` / job `123467594841`，以 15 个真实 `#check` / `#print axioms` 输出为准。

- 宽度：保留一般实数区间包围和正分母条件下的原识别区间宽度界；Beta(2,3) 半点例的积分及比率为 `1/12`、`11/192`、`11/16`。
- 三事件：在任意 `p₁,p₂,p₃ ∈ [0,1]` 下，有限 `Fin 8` 概率质量实现三边际与 Fréchet 联合区间中的每个值，包含上下端点；两种同边际概率律的混合保持边际并混合联合概率。
- 污染与条件化：一般可测空间上，`ε ∈ [0,1)`、可测 `B` 且 `P(B)>0` 时给出实际混合测度、条件概率差界及污染权重 `η` 公式；`Q(B)=0` 推出条件结果不变。有限数值例展示条件放大；零分母、失实包围与不可能联合下端点均作为前提失败或不可行边界示例，不构成运行时输入验证器。
- 审计 raw 只保留该 driver 15 组实际输出及续行。目标公理仅为 `propext`、`Classical.choice`、`Quot.sound`，无 `sorryAx`。Artifact `changed-module-only-40879691794-1`（ID `12899702798`，3321 bytes），ZIP SHA256 `1187cd23da95b79f3ffbdf90c64f99588063009dace4b6bf886ab273621c1cc2`；log 与 module-plan 的逐文件摘要见 `verification.json`。
- 诊断失败记录及其真实 run/job/head 保存在 `verification.json` 的 `diagnostic_runs` 中，仅作修复历史，不作为本包验收证据。

本包关闭归档的 U04.2 四项 residual。原题 04.3 仅补入与本模块直接重合的区间宽度及 Beta 积分证据；其共轭、预测、校准及 Hoeffding 等要求仍待核对。04.4 的 missing-group 全失败/全成功模型、端点识别集及与 U11.1 共享的外部识别条件未在本轮逐项核证；这不表示仓内没有实现，也不改 04.4 状态。04.1、04.6 其他义务保持原状。U00 消费边6仍未把实际概率数值送入旧决策计算，旧 Pipeline 仍直接读取 `i.alternatives` 中的概率。全局 `discharges_archived_manuscript_gaps=false`、math flip=false、Step 2 open，冻结 tip pin 保持不变。独立 changed-module 证据不是整体 release 验收。