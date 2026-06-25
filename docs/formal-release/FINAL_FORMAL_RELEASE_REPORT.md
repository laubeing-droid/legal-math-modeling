# 最终形式化发布报告

**状态**: FORMAL_CORE_RELEASED_BANACH_BLOCKED  
**发布 ID**: formal-core-v1  
**日期**: 2026-06-25

## 形式化核心

- 仓库级 clean build 已通过
- `AxiomAudit` 可复现
- Lean guard scan 通过：`0 sorry / 0 admit / 0 custom axiom / 0 theorem : True`

### 计数口径

- 形式化核心模块定理：`39`
- 扩展核心定理：`43`
- supporting results：`32`
- manifest 总计：`75`

说明：
- `39` 用于对外描述有限单调系统、AAF Grounded、Horn 闭包三块核心规格
- `43` 反映当前 manifest 中被归类为 core 的全部已检查结果
- `75` 是仓库级 machine-readable theorem manifest 的总条目数

## Axiom Audit

以下对象已通过 `#print axioms` 审计：

1. `exists_fixpoint_le_card`
2. `fixed_at_card`
3. `grounded_is_least_fixed_point`
4. `horn_completeness`
5. `horn_result_is_minimal_model`
6. `weightedSupDist_complete`

审计结果仅依赖：

- `propext`
- `Classical.choice`
- `Quot.sound`

未引入项目自定义 axiom。

## Banach 子目标

Banach 仍是独立 Track B，当前状态为 `UNPROVED_TRACK_B`。

当前可宣称：

- 加权距离相关基础定理已纳入检查清单
- Banach 需要的 complete-space / `ContractingWith` / fixed-point error bounds 尚未作为 formal-core 发布条件

当前不得宣称：

- Banach 固定点闭环已经完成
- 完整多维 Banach 收缩已经进入正式发布状态
