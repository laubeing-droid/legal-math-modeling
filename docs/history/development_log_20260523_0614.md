# 2026-05-23 ~ 2026-06-14 历史归档摘要

## 文件定位

这是早期建模阶段的历史摘要，不是当前发布状态说明。

如果要判断当前仓库到底完成到了哪一步，优先看：

- `docs/formal-release/FORMAL_RELEASE_REPORT.md`
- `docs/formal-release/FORBIDDEN_CLAIMS.md`
- `docs/final-closure/final-report.md`

## 这一阶段做了什么

这一阶段主要完成了三类工作：

1. 初始法律数学建模材料整理
2. 第一轮 theorem / counterexample / trust-label 结构搭建
3. 工程与形式化之间的早期对齐尝试

## 这一阶段的真实价值

- 奠定了“证据边界必须显式标注”的工作方法
- 暴露了 Banach、DP、图相似度、常量校准等高风险口径
- 为后续 formal-core 收口提供了反例和边界清单

## 为什么这份历史文件不能直接当当前状态

因为该阶段仍然带有明显的早期特征：

- theorem 计数口径尚未统一
- Banach 边界尚未最终降级
- 仓库级 formal release gate 尚未关闭
- 分支与轨道策略尚未收口到 `master` only

## 当前如何使用这份文件

把它当成“问题从哪里暴露出来”的历史记录，而不是“今天已经完成了什么”的真相源。
