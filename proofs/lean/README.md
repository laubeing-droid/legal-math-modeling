# Lean 形式化验证

## Lean 是什么

Lean 是一个**交互式定理证明器 (proof assistant)**，由 Leonardo de Moura 在 Microsoft Research 创建。
它的核心功能是：通过类型检查 (type checking) 来验证数学证明的正确性。

不同于 Python/Z3/穷举这类"运行后输出结果"的验证工具，Lean 的工作方式是:

1. 你写下一个**类型**（即你想证明的数学陈述）
2. 你构造一个**证明项**（即达到该类型的策略和数据）  
3. Lean 的**类型检查器**验证证明项确实匹配声明的类型

如果类型检查通过，这个数学陈述就被**永远证明**了——不是"跑了 N 次测试都通过"，
而是"在所有可能情况下都正确"。

## 为什么用 Lean

对于 legal-math-modeling 项目，选择 Lean 有四个理由:

1. **完备性**: 数学归纳法、∀/∃ 量词、无限域——这些是 Z3 和 Python 穷举无法处理的
2. **可复现性**: Lean 的 `lake build` 命令在任何机器上产生相同结果，不依赖 CPU 浮点或随机种子
3. **公理透明**: `#print axioms` 可以精确列出每个定理依赖的公理，没有隐藏假设
4. **组合性**: 小的证明可以组合成大的证明，满足模块化推理

## 在项目中的应用

Lean 证明的是**数学规格层**，而不是 Python 工程实现:

```
数学规格 (Lean 证明)          工程实现 (Python, 测试+证书验证)
─────────────────────          ─────────────────────────────
有限单调迭代通用内核           编译器和引擎中没有直接一对一对应
Dung Grounded Extension        代码中的 stratified_evaluator.py
Horn 闭包                      代码中的 compiler_core 模块
固定点存在性和唯一性            代码通过测试+证书验证
```

关键区分:
- Lean 保证了**数学规格**的正确性（推理系统应当满足的性质）
- Python 测试和证书保证了**工程实现**的正确性（代码实际行为满足规格）
- 两者之间通过精化边界 (refinement boundary) 连接，而不是"Lean 证明了 Python 代码"

## 当前状态

| 项目 | 状态 |
|------|------|
| Lean 版本 | 4.30.0 |
| Mathlib 版本 | v4.30.0 |
| 形式化核心模块 | FiniteMonotoneIteration, DungDefinitions, DungFixedPoint, HornDefinitions, HornFixedPoint |
| 形式化核心定理数 | 39 |
| 仓库级文件数 | 22 .lean 文件 |
| `lake build` | 2954 jobs, 全量通过 |
| sorry | 0 |
| admit | 0 |
| 自定义 axiom | 0 |
| theorem : True | 0 |
| AxiomAudit | PASS |

## 如何验证

```bash
cd proofs/lean/juris_lean

# 全量构建
lake build

# 单独构建 AxiomAudit
lake build +JurisLean.AxiomAudit

# 检查 sorry/admit/axiom
rg -n "\bsorry\b|\badmit\b|\baxiom\b" JurisLean/

# 打印关键定理的公理依赖
lake env lean JurisLean/AxiomAudit.lean
```

## Lean 目录结构

```
proofs/lean/juris_lean/
├── lakefile.lean              # Lake 构建配置文件
├── lean-toolchain              # Lean 工具链版本
├── lake-manifest.json          # 依赖清单
├── JurisLean/
│   ├── Basic.lean              # 基础定义
│   ├── FiniteMonotoneIteration.lean  # 通用有限单调迭代 (12 定理)
│   ├── DungDefinitions.lean    # AAF 定义 + 单调性
│   ├── DungFixedPoint.lean     # Grounded extension (13 定理)
│   ├── DungAAF.lean            # 接口聚合
│   ├── HornDefinitions.lean    # Horn 逻辑定义
│   ├── HornFixedPoint.lean     # Horn 闭包 (10 定理)
│   ├── SupZeroLemma.lean       # sup 辅助引理
│   ├── AxiomAudit.lean         # 公理审计
│   ├── BanachWeightedNorm.lean # 加权范数定义 (未完成)
│   ├── BanachCertificate.lean  # Banach 证书
│   ├── ContractionCondition.lean # 收缩条件
│   ├── WeightedSupNorm.lean    # 加权上确界范数
│   ├── JC_Formalization.lean   # 全局聚合
│   └── ... (实验性文件)
```

## 常见误解

**误: "Lean 证明了整个 Python 系统是正确的"**
正: Lean 证明了数学规格层。Python 实现通过测试和证书验证，
但未被 Lean 形式化证明。正确的说法是: "数学规格已被 Lean 证明，
工程实现与规格之间的精化关系已通过测试和证书验证。"

**误: "0 sorry = 所有东西都已完成"**
正: 0 sorry 只表示当前形式化核心模块没有未完成的证明。
Banach 多维收缩仍然在研究中，部分定理的正确陈述是定义而非证明。
它们不在 formal-core-v1 发布范围内。

**误: "自定义 axiom = 0 意味着零公理依赖"**
正: Lean 定理仍然依赖标准公理 (propext, Classical.choice, Quot.sound)。
"0 自定义 axiom" 意味着项目没有引入新的、未经验证的假设。
