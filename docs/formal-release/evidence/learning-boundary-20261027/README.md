# 拟合与部署、事实、授权边界：原题 01.1 / 01.5 / 01.6

成功 subject：`b25cb9f6723063450a9daed7caa773994d4c98ba`。

独立驱动 `LearningBoundaryAudit20261027` 的 [run 40380565418](https://github.com/laubeing-droid/legal-math-modeling/actions/runs/40380565418) / [job 121775341571](https://github.com/laubeing-droid/legal-math-modeling/actions/runs/40380565418/job/121775341571) 成功。五个精确类型/公理目标的原始输出保存在 `axiom-audit.raw.txt`，只移除时间戳、驱动位置前缀与构建噪声。`verification.json` 绑定该 subject 中的边界模块、独立驱动及实际 ERM 实现源码；只有标准公理，没有 sorryAx。

有限总体采用 `LearningRisk20261027.finiteBinaryRisk` 的真实有限加权风险；新证明核验点质量非负且总和为 1。由 `LearningERM20261027.fitNonempty` 从实际两条标签样本计算出的候选，在所声明标签总体可达风险 0，同时对相反事实目标风险为 1；同一模型在训练点风险 0、部署新点风险 1。另对任意样本长度和任意只依可见训练样本的确定性学习器，证明两个目标世界训练资料完全相同但新输入标签不同，且至少一个部署世界的风险为 1。合法行动另作明确外部输入，完美标签拟合仍存在不获许可的非空语境。

这些是原题要求的有限反例与一般不可区分结论，不是域外检测器、现实标签可信性证书、法律裁决或无限模型类的泛化结论。本记录仅覆盖模块构建与具名审计；全分支、全部原题及实际全链消费者需另验。`closes_debt=false`，OPEN 仍 20，不翻 `discharges`，不改冻结 tip_pin。
