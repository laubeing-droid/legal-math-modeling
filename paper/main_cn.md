# Legal Math Modeling: 跨法域符号法律推理的形式化框架

**作者:** Laupinco

**配套仓库:** [juris-calculus](https://github.com/laubeing-droid/juris-calculus) | **许可:** [CC BY 4.0](../LICENSE)

> **英文原文:** [paper/main.md](main.md) | **LaTeX 源码:** [paper/main.tex](main.tex)

---

## 摘要

我们提出一个跨多法域（中国内地、香港、美国）的符号法律推理形式化数学框架。
该框架包括三层法律本体论（L0/L1/L2）、用于前向事实扩展的单调 Horn 闭包引擎、
用于反驳和例外处理的 Dung 抽象论证框架、用于程序状态追踪的 Kripke 时态模型，
以及用于跨法域概念对齐的范畴论映射。

我们通过穷举枚举、符号计算和 SMT 验证证明了 18 个正面结果。
我们通过构造显式反例反证了 10 个声明。
我们确认 6 个声明为数据不足或仅限于玩具模型。
所有数学声明通过一个 7 级证据校准信任标签系统追踪，防止未验证的断言传播到下游工程决策。

**关键词:** 计算法学, 形式化方法, 法律 AI, 抽象论证, Horn 逻辑, Kripke 语义, 范畴论, 证据校准

---

## 目录

1. [导论](#1-导论)
2. [预备知识](#2-预备知识)
3. [法律本体论: L0/L1/L2](#3-法律本体论)
4. [单调 Horn 闭包](#4-单调-horn-闭包)
5. [Dung AAF Grounded Extension](#5-dung-aaf-grounded-extension)
6. [分层评估器正确性](#6-分层评估器正确性)
7. [Kripke 时态不变量](#7-kripke-时态不变量)
8. [范畴论 Rosetta 映射](#8-范畴论-rosetta-映射)
9. [Banach 定价压缩](#9-banach-定价压缩)
10. [差分隐私与法律特免权](#10-差分隐私与法律特免权)
11. [非干涉: CBL 阻断作为 Bell-LaPadula](#11-非干涉)
12. [证据校准信任标签系统](#12-证据校准信任标签系统)
13. [结论与开放问题](#13-结论与开放问题)

---

## 1. 导论

跨法域法律推理面临独特的形式化挑战：在一个法律体系中定义明确的概念（如美国合同法中的"实质违约"）
在另一个体系中（如中国民法典下的合同法）没有直接对应物。
现有计算法律系统通常依赖概率性检索增强生成（RAG），缺乏关于可靠性、完备性或跨法域一致性的形式化保证。

本文提出 **juris-calculus** 的数学基础，一个跨中国内地、香港和美国三法域运行的符号法律推理引擎。
核心贡献是一个形式化数学框架，包括:

1. **三层法律本体论** (L0/L1/L2)，包含 6 个不可约原语、15 个元本体范畴和 20+ 个法域特定领域概念
2. **单调 Horn 闭包引擎**，覆盖 2,117 条中国法规则，有界深度 k ≤ 3 下正确性已证明
3. **Dung 抽象论证框架**，用于反驳和例外处理，n ≤ 4 已穷举验证
4. **Kripke 时态模型**，带 LTL 嵌入用于程序状态追踪
5. **范畴论** 和 **Banach 压缩** 模型，用于跨法域映射和定价，带有显式反例标记其边界
6. 7 级**证据校准信任标签系统**，追踪每个数学声明在证明生命周期中的状态

### 1.1 研究方法: AI 辅助形式化

本研究采用迭代 AI 辅助方法:

1. **Claude** (Anthropic) 进行初始数学建模和法律推理架构的逆向工程
2. **Codex** (OpenAI) 使用 7 个工具链进行形式验证: Hypothesis, Z3, CrossHair, TLA+, Alloy, Lean 4, Dafny
3. **Kimi** (Moonshot AI) 收集法律验证数据并产出严格的数学证明重做
4. 第二轮 **Codex** 审计降级了过度声明，建立了最终证据校准基线

每个 AI 主体贡献了不同的验证模态。信任标签系统记录哪个主体产出了哪个证据，
防止任何单个主体的输出被推广到超出其已验证范围。

### 1.2 主要结果汇总

| 状态 | 数量 | 例子 |
|------|------|------|
| **已证明** (穷举/SMT/符号) | 18 | AAF grounded ext., Horn 单调性, Kripke 互斥 |
| **已反证** (反例) | 10 | DP epsilon, 评估器单调, 图度量 |
| **数据不足** | 4 | Rosetta 真实数据, Banach 真实数据 |
| **仅玩具模型** | 2 | Rosetta 玩具, Banach 标量 |
| **待工具链** | 6 | Lean 草案 (`sorry`), SMT 待完成 |

---

## 2. 预备知识

### 2.1 Horn 逻辑

**定义 2.1** (Horn 子句). *Horn 子句* 是至多有一个正文字的文字析取。在其确定形式中:

$$h \leftarrow b_1 \wedge b_2 \wedge \cdots \wedge b_n$$

其中 h 是头部（结论），b1, ..., bn 是体（前提）。空体 Horn 子句是事实；空头 Horn 子句是约束。

**定义 2.2** (Horn 闭包). 给定事实 F 和 Horn 子句 H，*前向闭包* H*(F) 是以下算子的最小不动点:

$$T_\mathcal{H}(\mathcal{F}) = \mathcal{F} \cup \{ h \mid h \leftarrow b_1 \wedge \cdots \wedge b_n \in \mathcal{H},\; b_1, \ldots, b_n \in \mathcal{F} \}$$

根据 Tarski-Kleene 定理，如果 H 在有限域上是有限的，则 H*(F) = T^k_H(F) 对某个有限 k。

### 2.2 抽象论证框架

**定义 2.3** (Dung AF). *抽象论证框架* 是一个对 A = (Args, →)，其中 Args 是论证集合，→ ⊆ Args × Args 是攻击关系。

**定义 2.4** (Grounded extension). A 的 *grounded extension* GE(A) 是以下算子的最小不动点:

$$F_\mathcal{A}(S) = \{ a \in \text{Args} \mid \forall b:\; b \rightarrow a \Rightarrow \exists c \in S:\; c \rightarrow b \}$$

**定理 2.1** (Grounded extension 的唯一性). 对任意有限 A = (Args, →), GE(A) 存在且唯一。
在 Lean 4 中已通过有限单调迭代的通用不动点内核证明。

### 2.3 Kripke 时态语义

**定义 2.5** (Kripke 结构). 法律 Kripke 结构 M = (W, R, V)，其中 W 是程序阶段的世界集，
R 是阶段转移关系，V 是命题赋值（法律事实、程序状态、结论）。

**定理 2.2** (时态守卫). 在 Kripke 结构中，时间守卫 □(t_fact < t_procedural) 在所有可达世界中成立。
即，法院不能引用尚未确立的事实。

### 2.4 信任标签系统

每个数学声明通过 7 级证据阶梯追踪:

| 级别 | 标签 | 含义 |
|------|------|------|
| L7 | PROVED_BY_EXHAUSTIVE_ENUMERATION | 穷举证明 |
| L6 | PROVED_BY_SMT | SMT 验证 |
| L5 | PROVED_BY_SYMBOLIC | 符号证明 |
| L4 | PARTIAL_PROVED | 部分证明 |
| L3 | DATA_INSUFFICIENT_FOR_PROOF | 数据不足以证明 |
| L2 | TOY_SYNTHETIC_PROOF_ONLY | 仅玩具模型证明 |
| L1 | REFUTED_BY_COUNTEREXAMPLE | 已被反例反证 |

---

## 3. 法律本体论: L0/L1/L2

法律本体论分为三层，为跨法域法律推理提供统一的概念基础。

### 3.1 L0 层: 不可约法律原语

六个不可约 L0 原语构成所有法律概念的基础:

1. **Agent** (主体): 法律权利义务的承担者
2. **Asset** (资产): 法律关系客体
3. **Act** (行为): 产生法律后果的行动或事件
4. **Status** (地位): 法律认可的状态或身份
5. **Power** (权力): 创制法律关系的可能性
6. **Defect** (瑕疵): 可能导致法律后果无效的情况

### 3.2 L1 层: 元本体范畴

L1 层定义 15 个抽象法律范畴，跨法域通用:

- 义务 (Obligation)、许可 (Permission)、禁止 (Prohibition)
- 权利 (Right)、责任 (Liability)、豁免 (Immunity)
- 违约 (Breach)、履行 (Performance)、终止 (Termination)
- 救济 (Remedy)、时效 (Limitation)、管辖 (Jurisdiction)
- 证据 (Evidence)、程序 (Procedure)、判决 (Judgment)

### 3.3 L2 层: 法域特定领域概念

L2 层包含 20+ 个法域特定概念，如中国法中的"善意取得"、
美国法中的"discovery"、“plea bargaining”、香港法中的"普通法惯例"。
CBL 阻断规则防止这些概念在未经过形式对齐门的情况下跨法域流动。

---

## 4. 单调 Horn 闭包

### 4.1 核心性质

**定理 4.1** (Horn 闭包单调性). Horn 闭包算子 T_H 是单调的:

$$\mathcal{F}_1 \subseteq \mathcal{F}_2 \Rightarrow T_\mathcal{H}(\mathcal{F}_1) \subseteq T_\mathcal{H}(\mathcal{F}_2)$$

该性质保证推理引擎在添加更多事实后永不"忘记"已经确立的结论。

### 4.2 k ≤ 3 边界

对 2,117 条 PRC 规则的实证分析表明:
- k ≤ 3 覆盖 100% 的法律规则链深度
- 在此范围内，Horn 闭包是可直接计算的，且单调性有保证

### 4.3 数学验证

- **穷举验证**: 3,965 个无环知识库，100% 通过 Horn 正确性检查
- **Z3 SMT**: Horn 闭包与不动点语义等价的约束一致性验证通过
- **Lean 4**: 有限 Horn 闭包的 10 个定理已形式化证明 (0 sorry)

---

## 5. Dung AAF Grounded Extension

### 5.1 核心性质

**定理 5.1** (Grounded extension 存在性与唯一性). 对任意有限论证图 A = (Args, →),
存在唯一的 grounded extension GE(A)，且可通过迭代 F_A 算子至多有 |Args| 步计算。

**定理 5.2** (有限单调迭代). Grounded extension 是有限单调系统的不动点。
通用不动点内核 (`FiniteMonotoneIteration`) 被 AAF 和 Horn 系统共享。

### 5.2 数学验证

- **穷举枚举**: n ≤ 4 时检查了 66,066 个攻击图，grounded extension 正确性验证通过
- **Z3 SMT**: grounded extension 的不动点性质验证通过
- **Lean 4**: 13 个 Dung grounded extension 定理已形式化证明 (0 sorry)

---

## 6. 分层评估器正确性

**定理 6.1** (阶段分离). 分层评估器将原始的非单调求值分解为:
- 阶段 1 (Horn 闭包): 单调
- 阶段 2 (AAF 构造): 非单调但确定

**定理 6.2** (反单调性反例). 原始统一评估器不单调: A = {a} ⊂ B = {a, b}, E(A) = {a}, E(B) = ∅。

---

## 7. Kripke 时态不变量

**定理 7.1** (时间守卫). □(t_fact < t_procedural) 在所有可达世界中成立。

**定理 7.2** (R_supersedes 与 R_corrects 互斥). Kripke 结构中的两个可达关系 R_supersedes
和 R_corrects 互斥: R_supersedes ∩ R_corrects = ∅。

**验证**: Z3 SMT 对 3 世界诉讼时间线的归纳验证通过。

---

## 8. 范畴论 Rosetta 映射

**目标**: 构造一个函子 Rosetta: Law_CN → Law_US，将中国法律概念映射到美国法律概念。

**定理 8.1** (玩具无碰撞函子). 对于 5 个法律概念 × 3 个法域的玩具模型，不存在无冲突的函子分配。
穷举 243 种赋值全部失败。

**定理 8.2** (真实数据边界). 在 44 个最高法院真实权利要求中，CN_ONLY 主导映射 (30/44)。
不存在全局自然变换。跨法域映射必须通过对齐门 + 阻断规则处理。

**验证**: 真实数据穷举检查，玩具模型穷举所有赋值。

---

## 9. Banach 定价压缩

**定理 9.1** (标量 Banach 压缩). 对于标量定价函数 f: R → R，如果 |f(x) - f(y)| ≤ β|x - y|，β < 1，
则存在唯一不动点。在 `BanachEffectiveNodes` 中已验证。

**当前状态**: 多维 Banach 压缩（加权范数下的 ContractingWith）仍未完成完整证明。
当前仅保留为数学路线图和研究轨道。

详见: [docs/formal-release/FORMAL_RELEASE_REPORT.md](../docs/formal-release/FORMAL_RELEASE_REPORT.md)

---

## 10. 差分隐私与法律特免权

**定理 10.1** (CN 格: 无单调 epsilon 函数). 在中国法律特免权格中，不存在单调的 ε: Privilege → R^+。
Z3 SMT 给出了 UNSAT 结果。

**定理 10.2** (跨法域反例). 同一特免等级: CN 格中 ε = 1.0, US 格中 ε = 2.5。
这意味着无法用统一的差分隐私预算函数跨法域运作。

**反例 10.4** (裁剪违反 ε-DP). 在证据值上使用简单 floor 裁剪，隐私比 → ∞，违反 ε-DP 定义。

---

## 11. 非干涉: CBL 阻断作为 Bell-LaPadula

**定理 11.1** (CBL 非干涉). 60 条 CBL 阻断规则构成 Bell-LaPadula 非干涉属性:
高法域的概念在未通过形式对齐门的情况下，不能流向低法域。

**验证**: 穷举图可达性分析，120 个法律原子，60 条阻断边。所有非法路径均被阻断。

---

## 12. 证据校准信任标签系统

信任标签系统确保每个声明都有明确的状态。已证明 18 项，已反证 10 项，
部分/不足 6 项，待定 6 项。没有声明可以同时声称已证明且未验证。

核心原则: **你能做出的最强声明，就是你的证据支持的声明——不能更强。**

详见: [theory/model_status.py](../theory/model_status.py)

---

## 结论与开放问题

### 已完成的工作

1. 有限单调迭代的通用 Lean 形式化内核
2. Dung Grounded Extension 和 Horn 闭包的核心定理证明
3. Lean 构建 0 sorry, 0 自定义 axiom
4. 仓库级 formal-core-v1 发布封板已关闭

### 开放问题

1. 多维 Banach 加权范数压缩的完整形式化证明
2. 真实数据上的参数校准
3. 差分隐私正式保证
4. Lean 规格与 Python 实现之间的精化证明
5. 图相似度性质的完整数学审计

### 三仓关系

| 仓库 | 职责 | 状态 |
|------|------|------|
| `legal-math-modeling` | 数学规格 + 形式化证明 | formal-core-v1 已发布 |
| `juris-calculus` | 生产运行时 | 241/241 测试通过 |
| `deli-autoresearch` | 长周期研究自动化 | Phase 4 已完成 |
