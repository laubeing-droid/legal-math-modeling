# 数学建模设计决策日志

> 本文档记录 juris-calculus 数学模型从"法律技能库"到"形式语义法律推理系统"的完整演变过程。
>
> **覆盖时间**：2026-05-23 至 2026-06-14（22 天）
>
> **数据来源**：22 份每日工作日志 + 1 份 10,359 行对话转录 + 多个 AI 会话记录
>
> **核心发现**：一个法律 AI 系统如何在 22 天内完成从 348 个重复技能 → 编译器架构 → 形式语义系统 → 20 个可执行数学证明 → 证据校准信任标签体系的完整跃迁。

---

## 一、完整时间线（22 天）

### 第一周（5/23—5/31）：基础设施与数据

| 日期 | 里程碑 | 关键产出 |
|------|--------|----------|
| 5/23 | 技能库重构 | liuweibin-legal-skills 13 个技能 + 4 个领域检查门 |
| 5/29 | WorkBuddy 首启 | v4.0 路线图设计启动，6 个仓库首次系统性审计 |
| 5/30 | v4.0 设计完成 | 6 专家并行审计，47 项未解决🔴，22 项决策全部裁决 |
| 5/31 | SPC 数据库构建 | 20 本 OCR 教材 → Agent 2 蒸馏 → 2,891→2,117 条规则，ChromaDB 向量索引 |

**本周建立了数学建模的"原材料"：2,117 条中国法 Horn 规则 + 13 个法律领域全覆盖。**

### 第二周（6/1—6/7）：编译器架构与数学建模

| 日期 | 里程碑 | 关键产出 |
|------|--------|----------|
| 6/1 | **形式语义突破** | 豆包 6 轮对话 → LegalOS 重构 → 编译器架构 → 形式语义设计 → 380 案卷点火 |
| 6/2 | juris-calculus 发布 | v1.0.0→v1.0.2 五轮修复 + 论文定稿 |
| 6/3 | SPC↔juris 桥接 | Schema v5.3 + 2,117 条规则转 YAML + 13/13 基准测试通过 |
| 6/4 | v1.2.0 TriRail | 三轨对撞器（CN×HK×US）+ 12 类冲突检测 + MCP Server |
| 6/5 | Harvey's Benchmark | 架构终局审计 + 去平台化 |
| 6/6 | 算法改进 | 14 项 P0~P2 修复 + pre-release-auditor |
| 6/7 | 环境准备 | Win11 Home→Pro + Claude Desktop 安装 |

**本周完成了从"技能堆叠系统"到"法律编译器"的架构跃迁，并建立了三轨跨法域碰撞检测引擎。**

### 第三周（6/8—6/14）：数学证明与形式化验证

| 日期 | 里程碑 | 关键产出 |
|------|--------|----------|
| **6/8** | **Claude 数学逆向工程** | 8 份分析报告（47 公式 + 23 算法 + 38 常量）+ theory/ 20 定理骨架初始化 |
| **6/9** | **Codex 形式化验证 + Claude 自修复** | 7 工具链 12 门类验证 + 发现 1 个反例 + Claude 20→46 收敛（4 轮自修复） |
| 6/10 | 数据归档 | 8 份英文报告中文翻译 + 实验数据整理 |
| **6/11** | **数学模型深挖规划** | 10 条深挖方向 P0→P4 + 四大模块数据需求详评 |
| 6/12 | V2.0 架构重设计 | 内核修改落地 + 会话恢复急救 |
| 6/13 | HK DDL 引擎 | 道义缺省逻辑规则引擎（10 commits, +15,900 行）+ 2,117/2,117 高置信度 DDL |
| 6/14 | 持续迭代 | v2.0 类型系统/法域适配/碰撞引擎 + 33 份性能基线 |

**本周完成了数学建模的核心突破：20 个可执行证明 + 证据校准信任标签系统 + Kimi 严格证明基线。**

---

## 二、六个认知跃迁

### 跃迁 1：从"补丁思维"到"编译器思维"（6/1 对话，行 2499）

> "core = 永不变的机制（Mechanism），profiles = 可变策略（Policy）"

**之前**：348 个技能各自独立，通过 patch 注入中国化规则。
**之后**：统一为 select → compose 组合系统，删除"patch"概念。

### 跃迁 2：从"组合系统"到"语义冲突系统"（6/1 对话，行 3259）

> "法律系统不是纯集合运算，而是语义冲突系统。"

三个例证：
- upstream: plea bargaining（辩诉交易）→ PRC: 明确不存在且制度排斥
- upstream: discovery rule（证据开示）→ PRC: 部分等价但结构性不同
- upstream: jury trial（陪审团）→ PRC: 制度不存在

**引入 Semantic Conflict Resolver + Policy 层三权分立。**

### 跃迁 3：从"数据驱动冲突解决"到"编译器驱动语义转换"（6/1 对话，行 3893）

系统本质被重新定义——从 LegalOS 变为 **Legal Domain Compiler System (LDCS)**：

| 编译器概念 | LDCS 对应 |
|:----------|:----------|
| AST | domain（知识结构） |
| Compiler flags | policy（制度约束） |
| Target semantics | reasoning_modes（推理范式） |
| Execution backend | core engines（引擎层） |
| Syntax analysis | 解析上游能力 |
| Semantic analysis | 冲突检测 |
| IR | 中间表示 |
| Optimization | 推理简化 |
| Code generation | 结论输出 |

### 跃迁 4：从"编译器外壳"到"形式语义系统"（6/1 对话，行 5401）

> "真正的内核是形式语义。没有形式语义，我们永远只能做'聪明的文本处理'，而不是'真正的语义编译'。"

**诊断**：缺 Semantic Model Layer（语义模型层）——LegalWorld Model + Interpretation Function + Satisfaction Relation。

**关键修正**：
1. Type System 必须"约束推理空间"，不只是分类
2. IR transition 必须可组合（Sequential/Parallel/Conditional/Fixed-point）
3. Rule Algebra 本质是 priority override，需升级为非单调逻辑
4. Verifier 缺语义模型 M → "伪验证器"

### 跃迁 5：从"声称证明"到"证据校准"（6/8—6/9）

**6/8 Claude**：生成 20 个定理 Python 文件，声称 84 条定理全部通过。

**6/9 Codex 审计**：PASS 0, SUSPECT 13, FAIL 7。7 个致命问题：
1. Banach 压缩 c=1.0（恒等映射，不满足 c<1）
2. Horn-Dung 对应性运行结果反驳定理
3. 范畴论 is_natural 返回 True（声称不存在，代码证明存在）
4. 渐进式验证跑在简化模型上而非实际引擎
5. DP 特权映射方向反了
6. 非干涉信息流方向反了
7. Counts-as 缺少渐进验证规则预排队

**6/9 Claude 自修复**：4 轮修复循环 → 20→46 收敛，零失败。

**教训**：不能把 Hypothesis 的"未发现反例"写成数学证明，不能把 Lean skeleton 写成已证明。建立 7 级证据状态体系。

### 跃迁 6：从"单一引擎"到"分层验证架构"（6/9—6/11）

最终接受的架构是四层：

```
Layer 1: Monotone Horn Core（Stage 1）
  → 前向事实闭包，有限知识库上可证明单调

Layer 2: Static AAF Argumentation（Stage 2）
  → Dung grounded extension，n≤4 穷举验证

Layer 3: Data Quality & Trust Label Layer
  → 阻止 toy/proxy/draft 数据被提升为生产声明

Layer 4: Engineering Policy Layer
  → 定价校准、DP epsilon、跨法域映射全部通过配置和审计门
```

---

## 三、关键设计决策详解

### 3.1 k≤3 边界与责任防火墙

**两档处理机制：**

**硬错误——编译直接失败：**
1. 规则存在循环依赖（如 Control → Affiliate → Control 的环）
2. 规则结论部分是纯析取式（A∧B→C∨D，且 C 和 D 互相排斥）

**编译通过，但打降级标记：**
- 例外链到了 k≥4
- k≤3 = 可证明安全区；k≥4 = 可运行但不可完全验证区

> "在监管环境下，为一个 AI 辩护说'这个法律结构太复杂，不能做确定性评估，需要人工审查'是很轻松的。为一个 AI 辩护说'它因为栈溢出在例外链中幻觉了一个无效合同'是根本不可能的。"

### 3.2 Kripke 程序状态建模

**分支约束：**
```
Branching ≤ 2（反诉约束）
Loops ≤ 3（举证质证循环约束）
Depth ≤ 3（审级约束：一审→二审→再审）
```

**世界分叉（Event Sourcing）：**
```
W1（一审）：□(Contract Valid)
  └─ 上诉 → W2（二审）：parent_world = "trial_1"
       └─ 模态状态从 □（既判力）回退到 ◇（争议中）
```

上诉 = `git checkout -b appeal/second_instance`。如果上诉被驳回，W2 关闭，W1 的 □ 成为终局。

**举证责任跨世界继承：**
> "W2 分叉时，W1 的 BurdenOfProof 集合完整继承，不重置。如果重置，等于鼓励当事人在一审故意不举证、到二审再亮底牌——这叫证据突袭，中国民事诉讼法明确禁止。"

### 3.3 非单调逻辑 → 法律规则的例外链

中国法经典三层例外链：
```
《民法典》第584条：违约赔偿 = 实际损失 + 可得利益
  但：不得超过违约方订立合同时预见到的损失
    但的但：故意或重大过失不适用上述限制
```

用 k≤3 非单调异常引擎自然建模：
```
R₁ (Depth 1): True → O(Deliver)           "你本不该违约"
R₂ (Depth 2): except (R₁.status = VIOLATED) → O(PayDamages)
                                          "但如果你违约了，你必须赔偿"
```

### 3.4 道义逻辑 → 义务冲突检测

场景：
```
条款3.1：O(乙方在30日内交付)        ← 义务
条款5.2：F(乙方在30日内自行处置)     ← 禁止
如果交付 = 移转占有 = 处置的一种形式？
→ O(φ) ∧ F(φ) → 义务冲突！
```

### 3.5 counts-as 算子 = 编译器的前端解析器

$$\text{Parser: } X \xrightarrow{\text{counts\_as}(C)} Y (\text{Type: LegalFact})$$

中国法场景：
- X = "未办理不动产抵押登记" → 在《民法典》语境下 counts_as "抵押权未设立"
- 但 Y = "抵押合同已生效" → counts_as "抵押人有义务配合办理登记"
- 两个 counts-as 的交互：物权效果 vs 债权效果，不能混淆

### 3.6 法规时间线（Intertemporal Law）

Kripke 结构中世界 W 的 context 必须包含两个时间戳：
- `fact_occurrence_date` → 实体法规则（民法典生效前适用合同法）
- `procedural_current_date` → 程序法规则（举证时限等）

两套规则集在同一个 IRState 中并行运作，杜绝"时空错配"。

---

## 四、证据校准信任标签系统

### 4.1 设计动机

6/9 Codex 审计发现 7 个"致命问题"后，建立了一个核心原则：

> "不能把 Hypothesis 的'未发现反例'写成数学证明，不能把 Lean skeleton 写成已证明。"

### 4.2 七级证据状态

| 状态 | 含义 | 置信度 |
|------|------|--------|
| `PROVED_BY_EXHAUSTIVE_ENUMERATION` | 全部情况穷举 | **最高** |
| `REFUTED_BY_COUNTEREXAMPLE` | 显式反例构造 | **极高** |
| `PARTIAL_PROVED` | 部分阶段已证明 | 中 |
| `DATA_INSUFFICIENT_FOR_PROOF` | 真实数据存在但不完整 | 低 |
| `TOY_SYNTHETIC_PROOF_ONLY` | 仅在构造的玩具模型上成立 | 低 |
| `PENDING_TOOLCHAIN` | 证明脚本存在，工具链未就绪 | 未知 |
| `ENGINEERING_BASELINE` | 工程假设，不是证明 | N/A |

### 4.3 核心声明注册表

| 声明 | 状态 | 证据 |
|------|------|------|
| Dung AAF grounded extension (n≤4) | **PROVED** | 66,066 图穷举 |
| Horn 闭包单调性 | **PROVED** | 解析证明 + 82,836 PBT |
| Kripke 时态不变式 □(t_fact < t_proc) | **PROVED** | Z3 SMT 归纳 |
| CBL 阻断 = Bell-LaPadula 非干涉 | **PROVED** | 60 条规则结构分析 |
| 原始评估器单调性 | **REFUTED** | 反例：{a}⊂{a,b} |
| 特免权确定 DP ε | **REFUTED** | 两模型见证：CN=1.0, US=2.5 |
| 图相似度是度量 | **REFUTED** | sim(∅,∅)=0.4≠1.0 |
| 范畴论 Rosetta (real data) | **DATA_INSUFFICIENT** | 44 行，7 碰撞见证 |
| Banach 定价压缩 (real) | **DATA_INSUFFICIENT** | 225 代理观测，0 真实工时 |

### 4.4 禁止标签

以下标签在任何下游系统中**永远不得出现**：
- `FINAL_ALL_THEOREMS_PROVED`
- `REAL_PRICING_VALIDATED`
- `DP_EPSILON_LEGALLY_DETERMINED`
- `ALL_SOURCES_OFFICIALLY_VERIFIED`

---

## 五、多 AI 协作方法论

本项目使用了一种独特的**迭代多 AI 形式化管线**：

```
阶段 1：Claude（Anthropic）
  → 初始数学建模 + 逆向工程
  → 产出：47 公式 + 23 算法 + 38 常量 + 20 定理骨架

阶段 2：Codex（OpenAI）
  → 形式化验证（7 工具链）
  → 产出：12 门类验证 + 1 个反例发现

阶段 3：Kimi（Moonshot AI）
  → 法律数据收集 + 严格数学证明重做
  → 产出：8/8 可运行证明通过 + 3 Lean 草稿 PENDING

阶段 4：Codex 审计
  → 降级过度声明 + 建立证据校准基线
  → 产出：7 FAIL → 4 轮修复 → 46/46 收敛

阶段 5：Gemini 外部审计
  → 独立视角审查
  → 产出：4 条采纳建议 + 7 条过度工程拒绝 + 3 条应拒绝建议
```

**每个 AI 贡献不同的验证模态。信任标签系统记录哪个 agent 产出了哪类证据，防止任何单个 agent 的输出被提升到其验证范围之外。**

---

## 六、数据资产全景

### 6.1 SPC 裁判规则数据库

| 指标 | 数值 |
|------|------|
| 来源 | 最高人民法院全国法官统编教材（14本/20册）|
| 蒸馏模型 | DeepSeek V4 Flash |
| 规则总数 | 2,117 条 |
| 字段完整度 | 100%（v5.2 后） |
| 向量索引 | 2,117 × 1,024 维（BAAI/bge-large-zh） |
| 领域覆盖 | 13 个法律领域 |
| 法条验证 | 1,223 命中 / 359 部未命中（codices 缺库） |

### 6.2 数学证明资产

| 资产 | 数量 |
|------|------|
| Python 理论模块 | 31 文件，~7,015 行 |
| Lean 4 草稿 | 3 文件（全部含 sorry，PENDING_TOOLCHAIN）|
| SMT/Z3 脚本 | 2 文件 |
| Hypothesis PBT | 82,836 测试用例 |
| 穷举验证 | 66,066 攻击图（AAF）+ 74,954 fixtures（Galois）|
| 反例 | 10 个已注册 |
| 证据校准声明 | 7 个核心声明 |

### 6.3 法律验证数据

| 数据集 | 内容 |
|--------|------|
| CN legal | 合同/侵权/公司/刑事/行政/数据 6 类 |
| US legal | 生成脚本 |
| HK legal | 阻断法律依据 + 特权格 |
| AAF legal | 论证框架验证摘要 |
| Banach pricing | Lipschitz 估计 + 定价证据摘要 |
| Category Rosetta | 语料清单 + 阻断分析 |
| DP privilege | 管辖区格 |
| Galois semantics | 审计摘要 + 定理依赖图 |

---

## 七、优先级路线图（截至 6/11）

### P0 — 数学基础修复

| 方向 | 状态 | 下一步 |
|------|------|--------|
| Galois Connection Lean 证明 | PENDING_TOOLCHAIN | 定义 α/γ，证明双向蕴含 |
| Graph similarity 公理化 | REFUTED（非度量） | 明确为 similarity function，证明/反证三角不等式 |
| Fixpoint 收敛拆分 | MIXED | Theorem A (抽象终止) + Theorem B (操作有界性) |

### P1 — 模型校准

| 方向 | 状态 | 下一步 |
|------|------|--------|
| 38 个硬编码常量 | 无经验依据 | OAT 敏感性分析 + 贝叶斯优化 |
| Theil-Sen 估计器 | 破坏 29.3% 崩溃点 | 改用 Siegel 重复中位数 |

### P2 — 差分隐私形式化

| 方向 | 状态 | 下一步 |
|------|------|--------|
| DP 邻接数据集定义 | 缺失 | 定义 sensitivity + tuple-level 隐私 |
| Floor clipping 偏置 | 已推导公式 | 实证验证 |

### P3 — 跨法域数学结构

| 方向 | 状态 | 下一步 |
|------|------|--------|
| 范畴论自然变换 | DATA_INSUFFICIENT | Alloy 建模 + 更多数据 |
| Kripke 互斥性 | Z3 UNSAT | 从有限域推广 |

### P4 — 论文理论

| 方向 | 状态 | 下一步 |
|------|------|--------|
| 可反驳性形式化 | 设计完成 | Dung AAF / ASPIC+ 实现 |
| 三轨博弈论建模 | CONJECTURE | 12 场景非合作博弈建模 |

---

## 八、关键教训

1. **先反例发现，再有限域证明，再模型检查，最后机器数学证明。** 顺序不能颠倒。

2. **"未发现反例" ≠ "已证明"。** Hypothesis PBT 是随机搜索，不是证明。

3. **Lean skeleton ≠ Lean proof。** 包含 `sorry` 的 Lean 文件只是草稿，不是验证。

4. **Codex 审计是必要的。** Claude 自称 20/20 PASS，Codex 找出 7 个 FAIL。自审计有盲区。

5. **证据校准比"全部证明"更有价值。** 诚实标注 "DATA_INSUFFICIENT" 比虚假声称 "PROVED" 对学术和工程都更有用。

6. **法律的 open-textured semantics 是根本约束。** "完全可证明正确的法律编译器"不可实现。可实现目标：bounded formal verification system。

---

## 九、理论定位总结

```
5/23：法律技能库（348 个重复技能）
  ↓
6/1：法律编译器（LDCS 五阶段管线）
  ↓
6/8：形式语义系统（20 定理 + 84 条数学声明）
  ↓
6/9：证据校准系统（46/46 收敛 + 7 级信任标签）
  ↓
6/13：V2.0 道义缺省逻辑引擎（2,117/2,117 高置信度 DDL）
```

**最终定位**：
- **不是**："可证明正确的法律编译器"（不可实现）
- **而是**："有界形式验证的法律推理系统"（Bounded Formal Verification System for Legal Reasoning）
- **核心创新**：证据校准信任标签系统——诚实标注每个数学声明的证明状态，防止 AI 幻觉进入工程决策
