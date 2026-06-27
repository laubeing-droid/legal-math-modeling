# 2026-06-16 ~ 2026-06-17 仓库创建期归档

## 文件定位

这是 `legal-math-modeling` 仓库创建与第一轮发布阶段的归档摘要。

**不记录当前最终发布边界。** 当前状态见 `program/PLANS.md`。

## 当时完成的关键工作

1. **仓库拆分**：从多份实验资料中拆出独立的数学配套仓库 `legal-math-modeling`
2. **目录结构搭建**：建立 `proofs/`、`theory/`、`docs/`、`data/`、`program/` 结构
3. **Lean 项目初始化**：建立 `proofs/lean/juris_lean/` 目录，开始 Lean 4 形式化
4. **第一轮 README 和发布口径**：形成初始版本的文档结构

## 对当前版本仍然有效的遗产

- 反例优先于夸大声明
- 数学配套仓必须与工程运行仓分离
- README、审计与历史记录需要同步维护
- 证据标签体系的雏形

## 对当前版本已经过时的部分

- 早期文件数、模块数、论文数等统计
- 当时的 Banach 表述（尚未形式化）
- 当时的 release 结构和分支状态
- 尚未完成 formal-core 封板前的临时口径

## 后续发展

从这一阶段开始，项目进入了系统性形式化阶段，最终达到：

- 94 个 Lean 定理，0 sorry
- `lake build JurisLean` 2954 jobs
- 25 个 Lean 文件，59 个 Python 模块
- 状态：FORMAL_CORE_RELEASED
