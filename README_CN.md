# Legal Math Modeling

> 形式化法律推理的数学配套仓库
>
> 工程仓库: [juris-calculus](https://github.com/laubeing-droid/juris-calculus) |
> 研究框架: [deli-autoresearch](https://github.com/laubeing-droid/deli-autoresearch) |
> 许可: [CC BY 4.0](LICENSE)

## 这是什么

这个仓库是 [juris-calculus](https://github.com/laubeing-droid/juris-calculus) 的**数学配套仓** -- 一个跨中国内地、香港和美国法域的确定性符号法律推理引擎的数学基础和形式化验证。

仓库包括:

- 跨法域法律推理的完整形式化数学框架
- 59 个可运行的 Python 理论模块
- Lean 4 形式化证明（核心规格层）
- Z3 SMT 约束验证
- 7 级证据校准信任标签系统
- 13 篇数学论文
- 机器可复现的审计和证明工件

## 系统架构

```
┌─────────────────────────────────────────────────────────────────┐
│                       用户约束                                  │
│         法域 + 案件类型 + 证据集 + 法律问题                      │
└──────────────────────────┬──────────────────────────────────────┘
                           │
                           ▼
┌─────────────────────────────────────────────────────────────────┐
│              第一层: 法律本体论 (L0/L1/L2)                      │
│   L0: Agent, Asset, Act, Status, Power, Defect (6 个原语)       │
│   L1: 15 个元本体范畴                                          │
│   L2: 20+ 个法域特定领域概念                                    │
│   来源: core_ontology.yaml (1,298 行)                           │
└──────────────────────────┬──────────────────────────────────────┘
                           │
                           ▼
┌─────────────────────────────────────────────────────────────────┐
│         第二层: 两阶段推理引擎                                  │
│                                                                │
│  阶段 1: Horn 闭包              阶段 2: Dung AAF               │
│  (前向事实扩展)                 (反驳 + 例外处理)               │
│  2,117 条 PRC 规则              n ≤ 4 穷举验证                  │
│  单调性 (已证明)                Grounded extension (已证明)     │
│                                                                │
│  k ≤ 3: 可证明安全区            k ≥ 4: TAINTED (需人工审查)     │
└──────────────────────────┬──────────────────────────────────────┘
                           │
                           ▼
┌─────────────────────────────────────────────────────────────────┐
│         第三层: 证据校准信任标签                                 │
│   PROVED → REFUTED → PARTIAL → INSUFFICIENT → TOY → PENDING    │
│   每个声明通过它的证明生命周期被追踪                              │
│   反例被保留为第一等工件                                         │
└──────────────────────────┬──────────────────────────────────────┘
                           │
                           ▼
┌─────────────────────────────────────────────────────────────────┐
│         第四层: 跨法域碰撞检测器                                 │
│   Tri-Rail: PRC x HK x US 三轨并行推理                          │
│   12 类冲突检测                                                 │
│   60 条 CBL 阻断规则 (= Bell-LaPadula 非干涉)                   │
└─────────────────────────────────────────────────────────────────┘
```

## 核心数学结果

这里的计数对应论文中的 40 个数学 claim 跟踪台账，不等于
`formal-core-v1` 的公开发布边界。对外 Lean 发布口径
(`39` 个核心定理, `0 sorry`, `0 自定义 axiom`) 见
[FORMAL_RELEASE_REPORT.md](docs/formal-release/FORMAL_RELEASE_REPORT.md)。

| 状态 | 数量 | 典型例子 |
|------|------|---------|
| **已证明** | 18 | AAF grounded extension, Horn 单调性, Kripke 时态守卫 |
| **已反证** | 10 | DP epsilon 确定性, 评估器单调性, 图度量 |
| **数据不足** | 4 | Rosetta 真实数据, Banach 真实数据 |
| **仅玩具模型** | 2 | Rosetta 玩具, Banach 标量 |
| **待工具链** | 6 | Lean 草案 (含 sorry), SMT 待运行 |

## 形式化核心 (Lean 4)

形式化核心是**数学上经过验证的规格层**:

- **有限单调迭代内核**: 通用不动点层 (12 定理)
- **Dung Grounded Extension**: 论证框架不动点 (13 定理)
- **Horn 闭包**: 前向推理闭包 (10 定理)

合计: **39 个核心定理**, 0 sorry, 0 自定义 axiom.

**Lean 是什么？** Lean 是一个交互式定理证明器 (proof assistant)。它通过类型检查证明项来验证数学陈述的正确性。在这个项目中，Lean 证明的是**数学规格** -- 推理引擎应当满足的性质。Python 实现通过测试和证书校验验证，但本身并未被 Lean 形式化证明。

工具链: Lean 4.30.0 + Mathlib v4.30.0。

Lean 工作区: [proofs/lean/juris_lean/](proofs/lean/juris_lean/)

## 仓库结构

```
legal-math-modeling/
├── paper/                              # 13 篇数学论文
│   ├── main.md                         #   核心论文 (13 章, KaTeX 渲染)
│   ├── main.tex                        #   LaTeX 源码
│   ├── icail_full_paper.md             #   ICAIL 合并版
│   └── ... (12 篇专题论文)
│
├── theory/                             # 59 个 Python 理论模块
│   ├── model_status.py                 #   信任标签系统
│   ├── argumentation_horn_unification.py # Dung AAF + Horn 统一
│   ├── bounded_horn_correctness.py     #   Horn 正确性证明
│   ├── temporal_kripke_ltl.py          #   Kripke 时态模型
│   ├── non_interference_cbl.py         #   CBL 非干涉
│   └── ... (54 个模块)
│
├── proofs/                             # 机器可复现证明
│   ├── engineering_proof_artifacts/    #   17 个工程证明工件
│   ├── strict_proof_baseline/          #   8 个严格基线证明
│   ├── lean/juris_lean/               #   Lean 4 形式化 (22 文件)
│   └── formal_verification_logs/       #   Codex 7 工具链审计
│
├── verification/                       # Z3 SMT 验证
│   └── verification_engine.py          #   4 项检查: consistency, LFP, pi_legal, DP
│
├── data/                               # 法律验证数据集
│   ├── cn_legal/                       #   中国法 (6 个领域)
│   ├── us_legal/                       #   美国法数据
│   ├── hk_legal/                       #   香港法数据
│   ├── aaf_legal/                      #   AAF 反驳模式
│   ├── banach_pricing/                 #   Banach 定价数据
│   └── external/                       #   COMPAS, LegalBench, SPC
│
└── docs/                               # 文档
    ├── formal-release/                 #   发布边界 (正式真相源)
    ├── final-closure/                  #   关门报告
    ├── audit/                          #   定理矩阵, proof ledger
    ├── modeling/                       #   8 份建模文档
    └── history/                        #   历史归档
```

## 快速开始

```bash
git clone https://github.com/laubeing-droid/legal-math-modeling.git
cd legal-math-modeling
pip install -r requirements.txt

# 运行信任标签系统
python -m theory

# 运行 Z3 验证 (4 项检查)
python verification/verification_engine.py

# 运行对抗性测试
python -m pytest proofs/engineering_proof_artifacts/adversarial/

# 运行所有严格证明
python proofs/strict_proof_baseline/run_all_proofs.py

# 构建 Lean 形式化 (需要 Lean 4 + Mathlib)
cd proofs/lean/juris_lean && lake build
```

## 文档导航

按以下顺序阅读可以了解仓库当前状态:

1. [FORMAL_RELEASE_REPORT.md](docs/formal-release/FORMAL_RELEASE_REPORT.md)
2. [FORBIDDEN_CLAIMS.md](docs/formal-release/FORBIDDEN_CLAIMS.md)
3. [final-report.md](docs/final-closure/final-report.md)
4. [theorem_status_matrix.md](docs/audit/theorem_status_matrix.md)
5. [next-stage-spec-first-roadmap.md](docs/analysis/next-stage-spec-first-roadmap.md)
6. [contract-breach-vertical-slice.md](docs/analysis/contract-breach-vertical-slice.md)
7. [jc-transition-gate-status.md](docs/analysis/jc-transition-gate-status.md)

当前转向规则:

- 本仓继续承担数学规格与 oracle 真相源
- 只有在 canonical semantic types、最小 DDL core、Horn -> AAF 编译契约、
  reference interpreter、differential validation boundary 封板后，主工程
  重心才应全面转向 `juris-calculus`

## 三仓关系

| 仓库 | 职责 | 分支 | HEAD |
|------|------|------|------|
| `legal-math-modeling` (本仓) | 数学配套, 形式化规格 | `master` | `5f4d635` |
| `juris-calculus` | 工程运行时 | `main` | `c18b478` |
| `deli-autoresearch` | 研究编排 | `main` | `e3e1c1f` |

- `legal-math-modeling` 证明**规格**
- `juris-calculus` 实现**运行时**
- `deli-autoresearch` 编排**长周期研究**

## 许可

[CC BY 4.0](LICENSE)
