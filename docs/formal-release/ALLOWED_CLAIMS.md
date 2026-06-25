# 允许的声明

## 数学证明层面

- 有限单调系统的不动点存在、在有限步内稳定，以及最小不动点性质可复现构建
- Dung Grounded Extension 的最小不动点性质可复现构建
- 有限 Horn 闭包的最小模型性质可复现构建
- `formal-core-v1` 的仓库级发布门禁已关闭

## 计数口径

- 形式化核心模块定理：`39`
- 扩展核心定理：`43`
- supporting results：`32`
- theorem manifest 总计：`75`

## 工程层面

- `juris-calculus` 的 grounded engine 输出 `derived_bound` / `convergent` / `truncated`
- `Deli AutoResearch` 当前桥接协议对截断、未收敛和协议不兼容采取 fail-closed
- 独立 `AxiomAudit` 和 Lean guard scan 可以在当前仓库复现
