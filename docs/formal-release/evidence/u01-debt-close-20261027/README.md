# U01 原欠项关债：OPEN 18 → 15

本包关闭原始 `scope-archive.json` 中 U01.1、U01.2、U01.3 的
`remaining_obligations`。三条原文逐字保存在 `verification.json`；不改原稿范围、
原欠项或已验收的 U03 关债包。本次关 3 条，独立关债累计 5 条。

| 条款 | 原欠项与本次采用的证明 |
| --- | --- |
| U01.1 | `LearningFiniteClass20261027` 从独立有界和推到实际 iid 样本均值，代入 ε＝√(log(2M/δ)/(2n))，覆盖评价前固定的非空有限类与依数据选择的近似 ERM。`LearningRisk20261027` 给出同一风险的表示差、头类差、估计差分解及表示塌缩造成 1/2 风险差的反例。 |
| U01.2 | `LearningBridge20261027` 证明分类事件包含关系，并对一般可测的同一个 [0,1] 损失积分。两个依样本变化的有效上界按各自失败概率作并集预算；不要求两个估计独立，也不把点估计当作有效上界。 |
| U01.3 | 同模块在任意可测概率空间上，以可测事件概率差的上确界定义联合分布 TV；用 layer-cake 积分正反两个方向，得到同一有界可测损失的绝对风险差界。该证明没有有限支撑限制，亦没有把待证风险界作为 TV 的定义。 |

复用具名审计 [run 40369446453](https://github.com/laubeing-droid/legal-math-modeling/actions/runs/40369446453)，
成功 [job 121735932469](https://github.com/laubeing-droid/legal-math-modeling/actions/runs/40369446453/job/121735932469)，精确 subject
`c265e254ecc45565642dd087ad8a095fc47ede5a`。14 个完整类型、公理输出和四份源码
指纹见同目录原始日志与回执。四份源码与成功审计时的 Git 内容一致；本包未改任何
定理体。原 `learning-theory-20261027` 模块回执仍保留 `closes_debt=false`，
这里另立 `closes_debt=true` 的原欠项验收记录。

`LearningTheoryAudit20261027` 纳入全量构建根；现有
`LearningERM20261027.u01_1_actual_fit_consumes_iid_oracle` 已把 iid 结论用于实际
有限类经验最小化器。`LearningConsumer20261027` 的后续校准调用读取所选表及实际
样本结果。二者是已有消费者，源码在本次保持不变。

抽样机制、总体、损失与标签目标的解释仍是原定理显式前提。联合分布 TV 不能换成
输入边际 TV；该结论不负责估计 TV，也不推出域外有效性或目标的法律真值。
这三条原欠项的验收不等于整个 U00 组合或全部原题完成。

旧 tip_pin 继续是 subject `21862d9bdd94bfa15e5da39079538b5eb30ff235`、
Authority `40274167574`、named=61；CAND8 仍为原八条，历史增量仍为零。
`discharges_archived_manuscript_gaps=false`。关债门同时校验 U03 与 U01 两份独立
回执、原欠项、具名原始输出、精确源码和构建入口；最终合并还须同一 PR 的 ULM、
Authority 全链及独立证书验收通过。
