# 禁止声明

以下说法当前都不成立，不能出现在 README、发布说明、论文摘要、仓库介绍或口头对外表述中。

## 明确禁止

- “整个 `juris-calculus` Python 实现已经被 Lean 完整证明”
- “四阶段组合正确性已经全部形式化关闭”
- “Banach 固定点闭环已经完成并并入 formal core”
- “差分隐私保证已经建立”
- “38 个常量已经完成真实数据校准”
- “诉讼自动化和研究自动化已经由本仓完成”
- “archive tag 代表活跃发布分支”

## 当前精确替代口径

### 对 `legal-math-modeling`

应写为：

> 有限单调系统、Dung grounded 不动点层、有限 Horn 闭包层的形式化核心已完成仓库级发布封板；Banach 仍为独立未完成研究轨道。

### 对工程层

应写为：

> Lean 已证明数学规格边界；Python 工程实现通过测试、证书校验与精化基线继续收口，但并未被本仓整体形式化证明。

### 对 Banach

应写为：

> Banach 相关工作仅保留为归档研究轨道，不属于 `formal-core-v1`。

## 分支与归档口径

当前公共分支模型：

- 只保留 `master`

归档 tag：

- `archive/banach-track-b-d23e8f2`
- `archive/track-c-prod-f43e273`

这些 tag 只用于追溯，不用于扩大当前 release claim。
