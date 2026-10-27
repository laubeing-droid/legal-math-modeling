# U03.1 / U03.2 实质关债包

这是用户要求化债后另立的实质关债工作包。原 CAND8 v1.1 的 8 条非充分性说明、扩审计回执及冻结 tip_pin 保留；本包不借那些说明关债，而核验后来已经实现的正向证明及实际消费者。仅放行 U03.1、U03.2；其余 18 条 OPEN 不变，全局 discharges=false。

具名审计：[run 40518100988](https://github.com/laubeing-droid/legal-math-modeling/actions/runs/40518100988)，[job 122237036992](https://github.com/laubeing-droid/legal-math-modeling/actions/runs/40518100988/job/122237036992)，SUCCESS；subject `ce5c5d85f0940c8a841d3865f59866a578d9e405`。15 个现有定理的完整类型及公理输出见 axiom-audit.raw.txt；未新增定理体。源码、原欠项和逐条全名映射见 verification.json。审计同时编译已有 SourceCompilationAudit 的执行断言。

| 原债项 | 已完成的原义务 | 实际消费者及边界 |
|---|---|---|
| U03.1 | 有限来源图检查、健全与无环；来源图的实际接受叶和启用规则进入有限闭包；{1}/{2} 与 1→3、2→3 的反例确实运行于稳健查询，严格超出共同事实闭包 | SourceCompilation.compileView 实际读取提取输出，再读取图检查输出，再调用 closureFromEvidence；源事实真、规则保真仍是明确前提，不推出现实真实性或法律效力 |
| U03.2 | 对实际允许重复元素的 list 实现，以初始事实及规则头的去重载体基数给出燃料界；不足饱和时集合严格增长；足够燃料下闭包成立，实际 checked 结果与可推导性双向等价 | closureFromEvidence 实际计算并传入该基数；不推出现实否定，不把无限项生成系统说成有限终止 |

合前核：原欠项文字逐字保留；精确量词、前提与结论经源码复核；所有具名输出齐全且仅标准公理；真实消费者有实际参数传递；来源/规则/法律边界保留；仅这两行获放行。关债检查器验证全名、原欠项、源码与成功 subject 一致，缺项、改弱、改源码、失败回执或改钉都会判红。

候选关债账：CLOSED_BY_NARROW=8，CLOSED_BY_WIRING=24，OPEN_FORMAL_TAIL=18，closed_this_round=2。本包合并仍须其最终 head/tree 的 ULM 与 Authority 全部适用门通过。原始稿的 archive 文本保留；减掉的是这两行已满足的形式残余义务，不宣称整个理论、现实法源或生产系统已全部完成。
