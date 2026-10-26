# 按测量单位划分及其边界的模块证据

成功 subject `0b2fca079d85ad033138ab126c24a83906bcb4a4`，独立驱动 `LearningSplitAudit20261027` 的 [run 40392393562](https://github.com/laubeing-droid/legal-math-modeling/actions/runs/40392393562) / [job 121816477854](https://github.com/laubeing-droid/legal-math-modeling/actions/runs/40392393562/job/121816477854) 成功。

原题01.3要求按测量单位μ划分，而不是以记录ρ不同作为独立性证明。`groupedSplit` 对实际记录执行两个互补过滤，六个具名目标证明准确成员条件、同测量单位不跨区、每个输入记录都有分区、复制全体记录不增加不同测量单位数，以及记录改名不改变分区。一般结论量化任意记录列表和单位分配函数；来源解释必须另行保证测量身份正确。

有限反例把两个不同事件、测量和记录实际划入两区，同时仍存在截止后特征、特征直接等于标签，以及统一的错误标签机制（标签为目标的否定）。这证明身份分组不能排除这些泄漏和偏差；已有 `LearningDependence20261027` 的实际概率模型另行刻画共同原因和复制的集中保证差异。不同测量单位的计数不自动成为独立或有效样本量。

独立驱动的两个 `#guard_msgs` 求值检查读取实际划分：同一测量的新记录ID仍在同区，三个记录只含两个不同测量单位。六个精确类型/公理原始输出在 `axiom-audit.raw.txt`；`verification.json` 绑定实现和驱动的确切源码，仅标准公理或无公理依赖，无 sorryAx。guard消费预期消息，不把未显示的消息伪记为日志输出。

本证据只确认上述模块与执行检查。U00中的具体调用、独立采样与真正来源身份、全部原题子项及整条ULM/Authority分别验收。OPEN=20、closes_debt=false，不翻discharges，不改冻结tip_pin，也不改变旧CAND8的八条。
