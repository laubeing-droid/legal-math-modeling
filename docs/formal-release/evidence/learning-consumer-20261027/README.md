# 实际拟合表到校准门的消费证据

成功 subject `927df18fb9de571902e9c0d62dc7c70b28a7a494`，独立驱动 `LearningConsumerAudit20261027` 的 [run 40385438770](https://github.com/laubeing-droid/legal-math-modeling/actions/runs/40385438770) / [job 121792358693](https://github.com/laubeing-droid/legal-math-modeling/actions/runs/40385438770/job/121792358693) 成功。

八个完整类型/公理目标的原始输出保存在 `axiom-audit.raw.txt`，只移除 Actions 时间戳、驱动位置前缀和构建噪声。`verification.json` 绑定模块与驱动的实际源码。仅有标准公理，无 sorryAx。这是新的 U01 消费审计，与 FormalTail 的 CAND8 名单无关。

`fitTable` 在有限有理数预测表中按实际监督样本选择经验风险最小者，输出真实表内容、样本量和计算出的经验风险。成功结果证明作用域、样本量、表维数、候选成员性和最小性；表维数由实际输入检查推出。`fitThenCalibrationGate` 将这一实际输出传给 `consumeCalibration`，查询值直接从选中表读取。

绑定包含旧 FitContract 的任务/目标/特征与模型版本/证据版本/输入截点/测量单位，并补上标签、损失、总体、抽样设计、分组、选择协议、适用域和失败预算。校准记录还绑定完整预测表；即使版本字段相同，替换表内容仍拒绝。独立驱动三个受 `#guard_msgs` 约束的实际求值分别检查全 false 标签输出 0、全 true 标签输出 1，以及使用另一张表的校准记录被拒绝。guard 消费预期消息，不把它们冒充原始日志的额外输出。

本模块复用 `Calibration.proposed_calibration_support_gate` 的输入条件。实际校准置信事件、总体与联合采样机制、来源/特征/标签解释仍需相应数学或外部证据；标识相等和这些检查不证明其真实性。输出是任务分数及条件性风险记录，不自动成为法律事实、许可或已加载生产模型。它也尚未替换被冻结的 U00 总入口；完整十五边仍需逐项接入和核验。

本记录只确认模块构建、八个精确证明和三个执行检查。全分支 ULM/Authority 另验。OPEN=20、closes_debt=false，不翻 discharges、不改冻结 tip_pin。
