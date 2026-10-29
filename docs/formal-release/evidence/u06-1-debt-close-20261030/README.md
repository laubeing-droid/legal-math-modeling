# U06.1 有限时域 Bellman 与轨迹测度：OPEN 7 → 6

本包只关闭归档 U06.1 的既有残余句：全 Bellman 最优性、空行动/终值约定与非矩形反例。独立 changed-module 绑定 source `8340ffa6d88138b89ec9083253414d8b69e96803`，run `40919387762` / job `123608188128`，14 个真实 `#check` / `#print axioms` 输出见 `axiom-audit.raw.txt`。

- 模型为有限状态、有限行动、有限时域、全可观测的时变 Markov 控制；终局收益 `g` 一般。冻结总稿允许空行动显式终止或标为 `BLOCKED` 并规定终值；本模块采用终止分支并取 `g(s)`。策略只依赖当前状态和可见历史，并提供逐步合法性证明。
- 轨迹权重由实际转移核和同一历史策略构造；证明其非负、总质量为 1，并把轨迹收益期望连接到递归 policy value。贪心策略逐时达到 Bellman 值，并支配所有合法 history policies；同策略成本在累计回报中扣除一次。非矩形 Bool 例区分先选固定模型与观测状态后逐点选最坏模型。
- 第 14 个目标复用既有 `Decision.u06_1_value_of_free_information`。它是有限 `FiniteLaw`/列表策略下的免费信息夹逼定理，不扩张为任意实数模型或有成本信息价值。
- `axiom-audit.raw.txt` 仅摘录本 driver 的 14 组真实 CI 类型/公理输出。14 目标只依赖 `propext`、`Classical.choice`、`Quot.sound`，无 `sorryAx`。实际 artifact `changed-module-only-40919387762-1`（ID `12917367581`，3136 bytes），ZIP SHA256 `aaf0f038397ded7d503a055245d4921d686af680d9bf7751418ad18af0b553b8`；逐文件摘要、source SHA、module plan 和失败诊断角色见 `verification.json`。

原题 06.3、06.4、06.5 仅保留与有限策略、免费信息界和 Bellman/轨迹期望直接对应的部分证据，三行仍为 PARTIAL。没有证明不同法律分支的共同可行集或 max-min 稳健值，也没有补齐信息采集/等待成本、部分可观测信念更新、隐藏真值不可区分例或现实消费者接线。U00 的实际 Pipeline 未因此改动或接入本模型。其他 97 题、105 工程项和 6 个切口不由本包覆盖。全局 `discharges_archived_manuscript_gaps=false`、math flip=false、Step 2 open，冻结 tip pin 不变。

本包是独立模块证据，不是整体 release 验收或法律/经验有效性结论。
