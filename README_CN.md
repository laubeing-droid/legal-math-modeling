# Legal Math Modeling

> 形式化法律推理的数学配套仓库
>
> 工程仓库: [juris-calculus](https://github.com/laubeing-droid/juris-calculus) |
> 研究框架: [deli-autoresearch](https://github.com/laubeing-droid/deli-autoresearch) |
> 许可: [CC BY 4.0](LICENSE)

## 这是什么

这个仓库是 [juris-calculus](https://github.com/laubeing-droid/juris-calculus)
的**数学规格配套仓** -- 一个跨中国内地、香港和美国法域的确定性符号法律推理引擎的
数学基础和形式化验证。

仓库包括:

- 跨法域法律推理的完整形式化数学框架
- 59 个可运行的 Python 理论模块
- Lean 4 形式化证明（核心规格层，94 个验证结果：43 core + 51 supporting）
- Z3 SMT 约束验证
- 7 级证据校准信任标签系统
- 13 篇数学论文
- 机器可复现的审计和证明工件

## 系统架构

```
+-------------------------------------------------------------------+
|                       用户约束                                     |
|         法域 + 案件类型 + 证据集 + 法律问题                        |
+----------------------------+--------------------------------------+
                             |
                             v
+-------------------------------------------------------------------+
|          第一层: 法律本体论 (L0/L1/L2)                            |
|  L0: Agent, Asset, Act, Status, Power, Defect (6 个原语)          |
|  L1: 15 个元本体范畴                                              |
|  L2: 20+ 个法域特定领域概念                                       |
|  来源: core_ontology.yaml                                         |
+----------------------------+--------------------------------------+
                             |
                             v
+-------------------------------------------------------------------+
|         第二层: 两阶段推理引擎                                     |
|                                                                    |
|  阶段 1: Horn 闭包             阶段 2: Dung AAF                   |
|  (前向事实扩展)                (反驳 + 例外处理)                    |
|  单调性 (已证明)               Grounded extension (已证明)          |
+----------------------------+--------------------------------------+
                             |
                             v
+-------------------------------------------------------------------+
|         第三层: 证据校准信任标签                                    |
|  PROVED > REFUTED > PARTIAL > INSUFFICIENT > TOY > PENDING         |
|  每个声明通过它的证明生命周期被追踪                                 |
|  反例被保留为第一等工件                                             |
+----------------------------+--------------------------------------+
                             |
                             v
+-------------------------------------------------------------------+
|         第四层: 跨法域碰撞检测器                                    |
|  Tri-Rail: PRC x HK x US 三轨并行推理                              |
|  12 类冲突检测                                                     |
|  60 条 CBL 阻断规则 (= Bell-LaPadula 非干涉)                       |
+-------------------------------------------------------------------+
```

## 形式化核心 (Lean 4)

形式化核心是**数学上经过验证的规格层**:

- **有限单调迭代内核** -- 通用不动点层
- **Dung Grounded Extension** -- 论证框架不动点
- **Horn 闭包** -- 前向推理闭包
- **加权上确界范数完备性** -- 收缩论证的度量基础

### 构建状态

| 指标 | 值 |
|------|------|
| `lake build JurisLean` | 2954 jobs, 0 error, 0 sorry |
| 核心定理 | 43 |
| 辅助结果 | 51 |
| 总验证结果 | 94 |
| 延迟公理 | 3 个（非阻塞，登记在 SORRY_LEDGER.md） |
| 工具链 | Lean 4.30.0 + Mathlib v4.30.0 |

标准机器可读源: [theorem_manifest.json](docs/formal-release/theorem_manifest.json)

### 核心定理分布

| 文件 | 数量 | 关键定理 |
|------|------|---------|
| DungFixedPoint.lean | 17 | `F_monotone`, `grounded_eq_groundedSpec`, `finite_termination`, `grounded_is_least_fixed_point`, `grounded_is_least_complete`, `self_attack_precise_theorem` |
| HornFixedPoint.lean | 10 | `horn_operator_monotone`, `horn_finite_termination`, `horn_result_fixed_point`, `horn_soundness`, `horn_completeness`, `horn_result_is_minimal_model` |
| FiniteMonotoneIteration.lean | 9 | `iter_mono`, `iter_stable`, `iter_card_lt_of_ne`, `exists_fixpoint_le_card`, `fixed_at_card` |
| WeightedSupNorm.lean | 4 | `weightedSupDist_triangle`, `weightedSupDist_symm`, `weightedSupDist_complete` |
| HornDefinitions.lean | 2 | `TH_monotone`, `TH_subset_univ` |
| ContractionCondition.lean | 1 | `lipschitz_coupling_implies_weighted_contraction` |

### Lean 源文件（25 个）

Lean 工作区位于 `proofs/lean/juris_lean/JurisLean/`，包含以下文件:

`AxiomAudit.lean`, `BanachCertificate.lean`, `BanachComplete.lean`, `BanachContraction.lean`, `BanachEffectiveNodes.lean`, `BanachFixedPoint.lean`, `BanachScratch.lean`, `BanachWeightedNorm.lean`, `Basic.lean`, `ContractionCondition.lean`, `DungAAF.lean`, `DungDefinitions.lean`, `DungFixedPoint.lean`, `FiniteGaloisAdjunction.lean`, `FiniteMonotoneIteration.lean`, `FiniteRosetta.lean`, `HornDefinitions.lean`, `HornFixedPoint.lean`, `HornOperationalRefinement.lean`, `JC_Formalization.lean`, `ScratchApi.lean`, `SupZeroLemma.lean`, `TemporalKripke.lean`, `UnifiedModel.lean`, `WeightedSupNorm.lean`

**Lean 是什么？** Lean 是一个交互式定理证明器 (proof assistant)。它通过类型检查证明项来验证数学陈述的正确性。在这个项目中，Lean 证明的是**数学规格** -- 推理引擎应当满足的性质。Python 实现通过测试和证书校验验证，但本身并未被 Lean 形式化证明。

工具链: Lean 4.30.0 + Mathlib v4.30.0。

Lean 工作区: [proofs/lean/juris_lean/](proofs/lean/juris_lean/)

## 规范门禁状态

| 门禁 | 状态 | 文档 |
|------|------|------|
| M1: Canonical Schema | SUBSTANTIAL_PARTIAL | [canonical_legal_schema.md](docs/spec/canonical_legal_schema.md) |
| M2: DDL 最小核心 | SUBSTANTIAL_PARTIAL | [ddl_minimal_core.md](docs/spec/ddl_minimal_core.md) |
| M3: Horn-to-AAF Contract | SUBSTANTIAL_PARTIAL | [horn_to_aaf_contract.md](docs/spec/horn_to_aaf_contract.md) |
| M4: Certificate/Checker 边界 | PARTIAL | [certificate_checker_boundary.md](docs/spec/certificate_checker_boundary.md) |
| M5: 统一停止口径 | CLOSED | [FORMAL_RELEASE_REPORT.md](docs/formal-release/FORMAL_RELEASE_REPORT.md) |

## 标准类型（11 种）

`LegalFact`, `LegalRule`, `LegalNorm`, `LegalClaim`, `Argument`, `Attack`, `Priority`, `Violation`, `Reparation`, `DecisionStatus`, `ProofTrace`

## DDL 模态

4 种模态: OBLIGATION, PROHIBITION, PERMISSION, CONSTITUTIVE。
4 种修复模式。3 种异常类。

标准 Python 源: `theory/canonical_semantics.py`（类型定义唯一权威）

## 仓库结构

```
legal-math-modeling/
+-- paper/                              # 13 篇数学论文
|   +-- main.md                         #   核心论文 (13 章, KaTeX 渲染)
|   +-- main.tex                        #   LaTeX 源码
|   +-- icail_full_paper.md             #   ICAIL 合并版
|   +-- ... (12 篇专题论文)
|
+-- theory/                             # 59 个 Python 理论模块
|   +-- canonical_semantics.py          #   标准类型定义 (唯一权威)
|   +-- model_status.py                 #   信任标签系统
|   +-- argumentation_horn_unification.py # Dung AAF + Horn 统一
|   +-- bounded_horn_correctness.py     #   Horn 正确性证明
|   +-- temporal_kripke_ltl.py          #   Kripke 时态模型
|   +-- non_interference_cbl.py         #   CBL 非干涉
|   +-- ... (53 个模块)
|
+-- proofs/                             # 机器可复现证明
|   +-- engineering_proof_artifacts/    #   工程证明工件
|   +-- strict_proof_baseline/          #   严格基线证明
|   +-- lean/juris_lean/JurisLean/     #   Lean 4 形式化 (25 个文件)
|   +-- formal_verification_logs/       #   Codex 7 工具链审计
|
+-- verification/                       # Z3 SMT 验证
|   +-- verification_engine.py          #   检查: consistency, LFP, pi_legal, DP
|
+-- data/                               # 法律验证数据集
|   +-- cn_legal/                       #   中国法 (6 个领域)
|   +-- us_legal/                       #   美国法数据
|   +-- hk_legal/                       #   香港法数据
|   +-- aaf_legal/                      #   AAF 反驳模式
|   +-- banach_pricing/                 #   Banach 定价数据
|   +-- external/                       #   COMPAS, LegalBench, SPC
|
+-- docs/                               # 文档
    +-- formal-release/                 #   发布边界 (正式真相源)
    +-- final-closure/                  #   关门报告
    +-- audit/                          #   定理矩阵, proof ledger
    +-- modeling/                       #   建模文档
    +-- history/                        #   历史归档
```

## 快速开始

```bash
git clone https://github.com/laubeing-droid/legal-math-modeling.git
cd legal-math-modeling
pip install -r requirements.txt

# 运行信任标签系统
python -m theory

# 运行 Z3 验证
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

1. [FORMAL_RELEASE_REPORT.md](docs/formal-release/FORMAL_RELEASE_REPORT.md) -- 发布边界与构建证据
2. [theorem_manifest.json](docs/formal-release/theorem_manifest.json) -- 标准机器可读定理清单
3. [canonical_legal_schema.md](docs/spec/canonical_legal_schema.md) -- M1 门禁
4. [ddl_minimal_core.md](docs/spec/ddl_minimal_core.md) -- M2 门禁
5. [horn_to_aaf_contract.md](docs/spec/horn_to_aaf_contract.md) -- M3 门禁
6. [certificate_checker_boundary.md](docs/spec/certificate_checker_boundary.md) -- M4 门禁
7. [FORBIDDEN_CLAIMS.md](docs/formal-release/FORBIDDEN_CLAIMS.md) -- 禁止声明清单
8. [ALLOWED_CLAIMS.md](docs/formal-release/ALLOWED_CLAIMS.md) -- 允许声明清单
9. [SORRY_LEDGER.md](SORRY_LEDGER.md) -- 延迟公理追踪台账

## 仓库角色

本仓库是 `juris-calculus` 的**规格上游与形式化边界源**，不是运行时实现。

**当前状态：** `spec-first-transition-ready` -- 五道门禁（canonical schema、DDL 最小核心、
Horn-to-AAF contract、certificate/checker 边界、统一停止口径）已达到可转向状态。

**此后：** 主工程重心转向 `juris-calculus`。本仓新增数学工作仅限"支持 JC 新能力"，
不再作为独立研究扩张。

**公开边界：** 见 [PUBLIC_PRIVATE_BOUNDARY.md](docs/disclosure/PUBLIC_PRIVATE_BOUNDARY.md)。
本仓继续公开。`juris-calculus` 公开范围收窄为可审计内核；商业层不再继续公开扩张。

## 精确口径

**对本仓库:**
> 有限单调系统、Dung grounded 不动点层、有限 Horn 闭包层的形式化核心已完成仓库级
> 发布封板；Banach 仍为独立未完成研究轨道。

**对工程层:**
> Lean 已证明数学规格边界；Python 工程实现通过测试、证书校验与精化基线继续收口，
> 但并未被本仓整体形式化证明。

**对 Banach:**
> Banach 相关工作仅保留为归档研究轨道，不属于 `formal-core-v1`。

**对 UnifiedModel:**
> `UnifiedModel.lean` 是独立的组合证明（Kripke -> Horn -> AAF -> Banach），
> 不属于 blocking path，不代表 production end-to-end correctness。

## 三仓关系

| 仓库 | 职责 | 分支 |
|------|------|------|
| `legal-math-modeling` (本仓) | 数学配套, 形式化规格 | `master` |
| `juris-calculus` | 工程运行时 | `main` |
| `deli-autoresearch` | 研究编排 | `main` |

- `legal-math-modeling` 证明**规格**
- `juris-calculus` 实现**运行时**
- `deli-autoresearch` 编排**长周期研究**

## 许可

[CC BY 4.0](LICENSE)
