# U14.1 原欠项关债：OPEN 14 → 13

本包验收原稿 U14.1 的三件残余义务：独立统计验证、自适应条件预算与服务装载集成。
原 `remaining_obligations` 逐字保存在 `verification.json`。仅关闭 U14.1，本轮增量 1，独立关债累计 7；此前 U03 两条、U01 三条与 U04.5 一条的回执保留。

本包只具名复核既有证明，不新增定理体：

- 独立统计验证：`ProtectedFeedback20261027` 的预声明有限类 iid 联合事件、实际抽样块置信前提、联合事件下各保护域风险界保持，以及已证严格改进与仅观察到改进的分离。
- 自适应条件预算：`AdaptiveValidation20261027` 的按可见历史可预测失败预算与历史单元内新鲜 iid 验证，`HarnessRisk20261027` 的随机预算自适应并集界，以及 `AdaptiveRoundLedger20261027` 的实际轮账本在任意有限轮动作下保持声明限额。
- 服务装载集成：`ValidatedFeedbackLoad20261027` 的装载门与实际写入回读、装载模型风险按已验证界、新装载模型作为下一轮实际父母，`AdaptiveRoundLedger20261027` 的评估装载来自实际激活，`BusinessFeedbackLoop20261027` 的下一生产动作读取实际评估后态。

独立审计 [run 40548856008](https://github.com/laubeing-droid/legal-math-modeling/actions/runs/40548856008)，
[job 122346800954](https://github.com/laubeing-droid/legal-math-modeling/actions/runs/40548856008/job/122346800954)，
subject `30e1524d8689dda130a653c22c13c230f0e48669`，SUCCESS。
同目录保存 15 个完整类型与公理输出、七份源码指纹和原欠项。仅使用标准公理。

现实标签真实性、抽样律与独立性、部署服务与法律有效性仍需原合同指定的外部证据，不由证明生成。
全局 `discharges_archived_manuscript_gaps=false`，冻结 tip_pin、CAND8 八条及历史
不关债回执均不改变。最终关债合并须本提交的 ULM、Authority 全链与独立证书通过。
