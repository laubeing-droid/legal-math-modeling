# Findings: gpt-prompt v4 重写依据

## 蒸馏管线资产盘点（2026-09-23，angle D 事实源）

- 位置：D:\Codex\1.法律工作区\legal-cn-distillation工作区\legal-cn-distill-books\
- wave1_法律方法/method_library：**40,428 record / 78 source / 40,427 bodies**，审计 40,468 checked / 0 badquote / 0 miss；结构 = records.jsonl + bodies + manifest.json + sources.jsonl。
- wave2：94 个记录组目录；wave3：3 组（大源）；wave4：7 组（src-005~011，133 册书，18,815 条，源文 45.7M 字符）。
- wave3 存量 9,782 + wave4 新增 18,815 = **28,597 条**（wave4 收官 audit 全库 0 badquote/0 miss）。
- 全库合计 **80,430 条**（2026-09-23 现场清点补上 wave2 实数 11,405：40,428+11,405+28,597），这是"需要数学消化"的资产本体。早前"约七万"漏计 wave2，v4 提示词曾误将 wave2 并入 28,597。
- 成品区 README 顶部"wave2 — 待启动"已过时（wave2-4 实际均已完成），引用时以各 wave 目录与 completion report 为准。
- wave4 记录体例：固定"案情简介—裁判要旨—裁判概要—争议焦点—分析—关联法条—参考文献"（判例书）等，含原文行号锚点。

## 仓库基线（angle B 事实源）

- b00d315 全管线绿（run 35833467010）：lean-full-clean-build / python-gates / runtime-refinement / seven-axis-acceptance / mathematics-completion / release-certificate / final-gate 全 SUCCESS。
- 清单工件现行 subject 1e0875c，计数 145/111/27/4；200 文件 disk==blob==json 三方哈希全等。
- 已有定理群：DDL 四模态、裁判四值、grounded/preferred、请求保持、权限层级、污点、量纲算术、有限单调迭代内核（详见 wave4-evidence.md §一"仓库对应物"列与仓库 docs/paper-rewrite/PROGRESS.md）。
- 待证缺口（HANDOFF 第三问+本轮审查补充）：五座桥（违反→攻击、例外→undercut、优先级→击败政策、证明责任→裁判闸门、时间→适用性闸门）；最小性收编内核；机器可达性/终止；非单调更新；combineAssurance 代数律（结合/交换/幂等）；weightedMetricSpace 的 CompleteSpace 与 ContractingWith 桥；ULM10 grounded 的 conflict-free/admissible/complete 绑定 DefeatAF.WellFormed；FullMath 公理审计（64 文件 #print axioms 0 命中）；ULM07→ULM08 依赖桥；五个零居民合同至少一个闭合实例。
- 跨仓 UNKNOWN：juris-calculus 按名消费定理，改名波及面未查。

## 提示词版本沿革

- v1：法律地位构成理论（八定理群+五桥）。
- v2：十三维+八结构命令。
- v3（合并版）：v1+v2 合并 + 证据规则；后升级为三任务（论文审查/CI 诊断复核/方案完善），CI 闭环后任务B改为闭环审查。
- v4（本次）：四角度全量重写（统一数学理论/系统待证/七书维度/管线消化），新增硬性"查论文与 GitHub"检索义务与检索产物格式。v3 的论文§1-3审查并入角度B的子项。
