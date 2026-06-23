# 允许的声明

## 数学证明层面

- 有限单调系统在 |universe| 步内达到不动点（鸽巢原理），已在 Lean 中证明
- Dung Grounded Extension 是 F 的最小不动点，已在 Lean 中证明
- Grounded Extension 分割为 IN / OUT / UNDEC 三值标注，已在 Lean 中证明
- 有限 Horn 闭包存在唯一最小模型，已在 Lean 中证明
- T_H 算子是单调的且保持在 universe 内，已在 Lean 中证明
- 全部 39 个核心定理不含 sorry、不含自定义 axiom、不含 True 规避

## 工程层面

- juris-calculus evaluate_horn 使用 derived_bound 替代硬编码 max_iterations
- SCC 分解使用迭代式 DFS（消除递归溢出风险）
- Deli AutoResearch 桥接协议 fail-closed：截断/未收敛/引擎版本不兼容 均拒绝
- Banach 加权最大范数收缩条件 Lw <= qw -> weightedDist(Tx,Ty) <= q * weightedDist(x,y) 的代数不等式已在 Lean 中证明

## 方法层面

- FiniteMonotoneSystem 是 AAF 和 Horn 共享的通用不动点内核
- 所有证明通过单一内核实例化，而非各自重复