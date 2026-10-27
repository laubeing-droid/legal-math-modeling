# U04.5 原欠项关债：OPEN 15 → 14

本包验收原稿的事件似然义务：一般联合似然、确定性记录副本，以及副本的信息域。
原 `remaining_obligations` 逐字保存在 `verification.json`。仅关闭 U04.5，
本轮增量 1，独立关债累计 6；此前 U03 两条和 U01 三条的回执保留。

`MeasurementLikelihood20261027` 对任意可测样本空间中的假设概率律 P、Q 证明：

- 联合事件的似然比按首事件似然和条件事件似然分解；所用正分母前提明确。
- 两次测量须在 P、Q 各自之下满足 `IndepFun`，才能由联合概率导出似然比相乘。
- 已观测 X=x 后，记录 g(X)=g(x) 对应的联合事件与原观测事件相等，故副本的似然比不变。
- Q 的事件概率为零时不给出有限似然比；非退化测量不能与自身独立。

这些结论覆盖原稿 U04.5 的二元测量及 LR4/LR16 区分；没有将记录编号当成独立性
证据，也没有把零概率点当作已定义的密度似然。原稿的对象、测量和记录身份类型及
4/16 数值结论沿用原已验收实现。`ExactProbability20261027` 已证明
σ(X,g(X))＝σ(X)，并得到相同信息下可积目标的条件期望相等；本次一并具名复核。

独立审计 [run 40532401962](https://github.com/laubeing-droid/legal-math-modeling/actions/runs/40532401962)，
[job 122288487688](https://github.com/laubeing-droid/legal-math-modeling/actions/runs/40532401962/job/122288487688)，
subject `693b5db3ff9f6e1046877b878a287fb388aa5899`，SUCCESS。
同目录保存 9 个完整类型与公理输出、三份源码指纹和原欠项。仅使用标准公理。

测量机制、身份和假设概率律的真实性仍需原合同指定的外部证据。
全局 `discharges_archived_manuscript_gaps=false`，冻结 tip_pin、CAND8 八条及历史
不关债回执均不改变。最终关债合并须本提交的 ULM、Authority 全链与独立证书通过。
