# 原题01.3：真实事件身份分组的证明与执行证据

成功subject `1d74048a9c96b8fbdec3b0905b0812dcdc7df350`，独立驱动 `LearningEventSplitAudit20261027` 的 [run 40394833453](https://github.com/laubeing-droid/legal-math-modeling/actions/runs/40394833453) / [job 121825006993](https://github.com/laubeing-droid/legal-math-modeling/actions/runs/40394833453/job/121825006993) 成功。源码与本次原始输出由 `verification.json` 绑定。

原题基本定义第88行及补正S01第7/15行的μ是**真实事件身份**。`eventSplit`实际读取 `EventSplitObservation.event`，不同measurement、record的同事件行继承同一分区。真实事件身份如何由来源解释确定是独立前提，不因赋予整数ID即已证真。原题编号与50条U登记编号不同，本证据按原题01.3/S01核对，不改变U登记处置。

六个具名目标覆盖任意记录列表和事件分配函数的准确成员条件、同事件不跨训练/测试、每行都有分区、复制不增加不同事件数，以及改变测量和记录ID不改变事件分区。有限反例在实际event分区中保留未来特征、直接标签特征和统一错误标签机制，说明分组不排除这些问题。共同原因和复制对集中保证的影响另由既有 `LearningDependence20261027` 的概率模型刻画；事件数本身不等于独立或有效样本量。

两个受 `#guard_msgs` 约束的实际求值检查包含“同事件、不同measurement与record”的重复行：两行必须同在训练区，三行仅含两个不同事件。六个精确类型和公理目标原始输出在 `axiom-audit.raw.txt`，仅标准公理或无公理依赖，无sorryAx；guard消费预期消息，不把它们伪记为原始日志额外输出。

范围纠正：未合并的 `formal/grouped-split-20261027` 旧分支按measurement分组，已明确撤回其符合原题01.3的主张。该旧函数的模块成功和测试均不沿用到本模块；本版本从已验证PR30主线重新建立，并独立重编。

本记录只确认事件分组模块与执行检查。U00的实际调用、全部U01子项、原始身份解释及独立抽样条件、整条ULM/Authority仍分别验收。OPEN=20、closes_debt=false，不翻discharges，不改冻结tip_pin，不改变CAND8八条。
