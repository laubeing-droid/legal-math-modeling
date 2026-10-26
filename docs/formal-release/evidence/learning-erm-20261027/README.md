# 实际有限类 ERM 消费证明的独立模块证据

成功 subject：`daf2a08624c4677b4cabe76dbf52eb8d0b913c4e`。

GitHub Actions Authority 的 changed-modules 模式 [run 40378405554](https://github.com/laubeing-droid/legal-math-modeling/actions/runs/40378405554)、[job 121767689066](https://github.com/laubeing-droid/legal-math-modeling/actions/runs/40378405554/job/121767689066) 成功构建 `LearningERM20261027` 与独立驱动 `LearningERMAudit20261027`。

`axiom-audit.raw.txt` 逐行保留该驱动的原始 `#check` / `#print axioms` 输出，仅移除 Actions 时间戳、驱动位置前缀与安装/构建噪声。五个完整目标名与源文件散列在 `verification.json`；只出现 `propext`、`Classical.choice`、`Quot.sound`。

本批实现有限非空候选列表上的有理数经验风险最小化。实际数据选择的输出具备成员性、最优性和所选总体风险的可测性，并被既有 iid 有限类总体风险定理消费；这些性质由实现证明，不作为拟合器未经核实的输出声明。空候选集和空样本返回 `none`。独立驱动含三个 `#guard_msgs` 包裹的真实 `#eval`，分别检查全 false 样本返回 `some false`、全 true 样本返回 `some true`、空候选集返回 `none`；构建成功证明消息匹配，消息本身被 guard 消费，不冒充原始日志中的额外打印。

总体定理仍要求固定候选类、明确总体分布、联合 iid 样本机制、同一可测有界损失和合法失败概率；经验最小化不产生这些数据机制前提，也不证明标签、法律判断或现实事实为真。此记录只覆盖独立模块检查，不代表全分支 ULM/Authority、全部 U01 子题、15 条消费边或完整 U00 已验收。

`closes_debt=false`，OPEN 仍 20；不翻 `discharges`，不更改冻结 tip_pin。
