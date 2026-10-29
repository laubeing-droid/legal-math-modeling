# U06.2 混合期望与固定议价树桥：OPEN 6 → 5

本包关闭归档 U06.2 的原始残余：“Universal allowed-deviation real payoff transfer present; mixed expectations and explicit strategy/tree bridge remain.” 证据绑定独立 source `fe9e4b689d317e75d91415ea65d701583a205929`，run `40939134896` / job `123677528713`，32 个真实 `#check` / `#print axioms` 输出。原始 changed-module ZIP 为 Artifact `changed-module-only-40939134896-1`, ID `12925329796`，4930 bytes，SHA-256 `46591a17cd3591eccbd2ffc912718b10b538f159a9c05f32bea2762905bd820e`；`axiom-audit.raw.txt` 是从实际 `changed-module.log` 提取的本模块声明输出，不是 ZIP 中的独立原生文件。

- 混合期望部分给出有限 mixed payoff 下的一般 ε+2η transfer，并复用既有完整偏离和正仿射最佳响应声明。
- 固定 W4 实例连接具体完整策略、两轮树、行动/历史与信息、确定转移核、终局账本收益及均衡迁移；不是一般均衡存在定理。
- 32 个目标仅依赖 `propext`、`Classical.choice`、`Quot.sound`；`sorryAx`、非标准公理和冲突目标均为空。4 个实际源码 SHA 与独立 CI 绑定见 `verification.json`。两次失败 run 只列诊断用途，不作为证明证据。

原题 06.7 仍为部分映射：本证据覆盖其固定两轮议价树与实际 KernelGame 收益桥对应段落；原稿关于混合 NE 存在条件、matching pennies、一般逆向归纳条件及整体七问交付仍需按原题核对。本轮未建立旧 Pipeline 数值消费者接线，不主张 06.2/06.7 整体完成，也不映射到 U00 消费边。全局 discharges、math flip 与 Step 2 保持未关闭，冻结 tip pin 不变。
