# 07 向 Codex 交接

日期：2026-06-28（原版 2026-06-11）

## 1. 当前状态

legal-math-modeling 项目已完成形式化核心发布（formal-core-v1）。

| 指标 | 数值 |
|------|------|
| Lean 唯一定理 | 94（43 core + 51 supporting） |
| sorry 数量 | 0 |
| 构建 jobs | 2954 |
| Lean 文件 | 25 个 |
| Python 模块 | 59 个 |
| 规范类型 | 11 个 |

## 2. 交接输入

1. `proofs/lean/juris_lean/` — 25 个 Lean 形式化文件
2. `theory/` — 59 个 Python 理论模块
3. `theory/spec/` — 11 个规范类型定义
4. `data/` — 法律验证数据集
5. `docs/` — 建模文档和历史记录

## 3. 已完成工作

1. 94 个定理已通过 Lean 形式化验证，0 sorry
2. 公理审计通过 AxiomAudit.lean 可复现
3. 11 个规范类型已定义并文档化
4. 59 个 Python 理论模块已编译通过
5. 13 个幽灵文件引用已从文档中清除
6. 跨结构映射采用 obstruction-first 路由

## 4. 不可违反的边界

1. 不得引用不存在的 Lean 文件（幽灵文件清单见审计文档）
2. 不得把 Python 架构探索声称形式证明
3. 不得把 sorry 隐藏在未审计的文件中
4. 不得削弱已证明定理的命题强度
5. 不得伪造构建数据

## 5. 验收命令

```bash
# Lean 构建
cd proofs/lean/juris_lean && lake build JurisLean

# 公理审计
lake build +JurisLean.AxiomAudit

# Python 验证
python -m compileall -q theory/
python -m theory --summary

# 幽灵文件扫描
python scripts/scan_lean_guards.py proofs/lean/juris_lean/JurisLean
```

## 6. 下一步任务

1. Track A2：executable refinement baseline
2. Track C1：certificate soundness
3. Track C0：no-uncertainty-upgrade gate
4. Track D1/D3：impact analysis + incremental grounded
5. Track B0-B3：Banach worktree（不阻塞 formal core）
