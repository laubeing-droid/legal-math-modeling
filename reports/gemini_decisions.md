> **Historical record of external AI review (Gemini, 2026-06-18). Technical decisions herein represent Gemini's recommendations; verify against actual codebase state before acting on them.**

---

# Technical Decision Document: Legal Model System

**Source:** Gemini conversation
**Date:** 2026-06-18
**Scope:** 25 technical decision items for the "JC Legal Reasoning Unified Mathematical Model Formal Proof System"

---

## 一、Bug 修复与工程优化决策

### Bug 1: 分词盲区修复

- **决议:** 选择 A 方案（原地修改）作为短期过渡，长远向 C 方案（全局预处理）演进。
- **边界情况处理（`"unsigned"` vs `"signed"`）:** 利用正则分词 `re.split(r'[\s_\-]+', text.lower())` 后，`contract_signed` 会被切分为 `['contract', 'signed']`，此时用 `phrase in words` 能够精准匹配。而 `unsigned` 独立成词 `['unsigned']`，不会误匹配 `signed`。
- **回归测试必要性:** 极其需要。在法律文本中，`"not_signed"`、`"not-signed"` 与 `"not signed"` 代表了完全相同的法律事实（否定真值）。必须在 `tests/` 中显式补充这三种形式的对抗测试用例，防止分词器将其拆解为独立的 `signed` 从而引发逻辑真值逆转。

### Bug 2: 前向推导缺失

- **决议:** 选择 C 方案（分层设计）。保留 `construct_frame()` 作为仅依赖初始事实的基础图构造，另设 `construct_deductive_frame()` 专门处理前向闭包。
- **循环规则与安全阀:** 由于命题 Horn 闭包在有限谓词空间内必然收敛（不动点计算），标准的固定点迭代（Fixed-point iteration）在检测到事实集不再扩大时会自动终止，因此 `r_1 -> r_2 -> r_1` 的死循环在数学上可以自然规避。
- **安全阀设计:** 建议引入 `HornRule.depth` 作为辅助限制。允许用户配置 `max_depth=10`，当迭代层数超过该值且未触发不动点时，抛出 `DeductionDepthExceededWarning`，以防规则库被意外引入无限生成逻辑。

### H1: DP 平滑剪裁

- **决议:** 选择 A 方案（tanh 平滑）。`clip_C(x) = C * tanh(x/C)` 具备全局可微性与渐近有界性，能更好地保持隐私泄露量（Privacy Loss）的连续性分析。
- **参数配置:** 采用动态配置模式。默认 `C = 1.0`，但允许在初始化引擎时通过测算基准域数据的方差动态调整。
- **Fallback 机制:** 保留旧的 floor clipping 作为 fallback，并可通过配置项 `enable_legacy_clipping=True` 开启，用于比对平滑前后的边界差异。

## 二、形式化证明与验证系统设计 (Lean & Z3)

### Lean sorry 消除

- **推进顺序:** 严格按照 Banach -> Rosetta -> Galois 的难度梯度推进。
- **高难度项处理:** Galois 关联的 4 个高难度 sorry 属于理论深水区，应先行定义为 `PENDING_PROOF` 或通过 `axiom` 引入，优先确保整体编译流水线（CI）能够跑通，避免阻塞工程进度。
- **Python 桥接验证:** 强烈建议在写 Lean 证明前，先用 Python 编写有界穷举验证脚本。通过暴力搜索穷举有限格（Finite Poset）和伴随关系（Adjunction），确保证理本身无误，避免在 Lean 中耗费大量时间去证明一个存在反例的伪命题。

### JC_Formalization.lean 补充

- **具体构造 vs Axiom:** 对于 `Counterexample6_2` 和 `MDL_FP_Analysis.v3_result` 这类有限对象或纯数值项，应构造具体证明（直接将 JSON 字典硬编码或通过脚本转化为 Lean 的 inductive 类型）；对于 `InfiniteHornCounterexample`（无限集编码），短期内直接使用 `axiom` 假设，待一期系统稳定后再行补全结构化证明。

### Z3 验证器

- **字符串等价性:** 弃用 Z3 的原生字符串理论（`Seq/String`，极易引发超时）。推荐采用 Hash 映射或 Bitvector 编码，在 Python 侧将法律术语转换为固定的整数 ID，再交付 Z3 逻辑体系进行符号推导。
- **DP 验证:** 引入 `tanh` 后必须启用 Z3 的非线性实数算术（NRA）解算器。若遇到性能瓶颈，可在特定区间内使用分段线性（Piecewise Linear）函数进行近似符号约束。
- **核心优先级:** 约束一致性 > LFP 单调性 > pi_legal 等价性 > DP 平滑安全性

## 三、产品功能扩展架构抉择

### F1: 时态推理集成

- **决议:** 选择 C 方案（Pipeline 中间层）。此方案对核心数据结构的侵入性最小。在 Horn 推导触发前，由时态引擎根据时间戳前置过滤掉失效规则，生成临时的"有效法条快照"。
- **缺失日期处理:** 默认适用"当前日期（系统时间）"，但在推导日志中输出 `TemporalWarning`。
- **法律冲突解决原则:** 抽象出独立的法理规则层——程序法从新（溯及既往），实体法从旧（法不溯及既往）。在过滤规则时，根据法条元数据中的属性（`procedural=True/False`）自动判定适用优先级。

### F2: 跨域 Obstruction Checker

- **样本构造:** 采用混合模式。通过脚本直接抽取 `claim_mapping.csv` 的真实行作为大样本基准，同时人工剪裁出 3 组各包含 5 行的极简合成样本（`ObCN_sample` 等）用于单元测试。
- **冲突判定标准:** 采用分级放行机制。严格定义 `Strict`（不允许 PARTIAL）与 `Tolerant`（允许 PARTIAL，但需输出阻断见证标记 `Warning Tokens`）两种模式。
- **输出格式:** 兼顾工程与理论，统一输出结构化的 JSON witness，并在系统内部留出向 Lean4 Axiom 自动生成器的文本接口。

### F3: 图相似度度量化

- **决议:** 选择 B 方案（最大公共子图, MCS）。既然系统定位为"统一数学模型形式化证明"，满足度量公理（反身、同一、三角不等式）就是不可妥协的硬性底线。Weisfeiler-Leman（C 方案）因不满足三角不等式直接予以排除。对于法律论证结构图（通常节点数 n <= 10），MCS 虽然是 NP-hard，但在此规模下的绝对耗时在毫秒级，完全可承受。
- **向后兼容与测试:** 必须保持旧接口兼容；测试规模直接采用 n <= 4 的图进行全穷举测试，确保反射性与同一性在边界下 100% 正确。

### F4: 偏离度检查器

- **权重:** 维持 (0.4, 0.35, 0.25) 的经典法理学理论配比，但通过 `deviation_config.yaml` 暴露外置接口。
- **基准数据:** 采用预计算存储模式（读取 `reports/deviation_baselines.json`），避免每次运行时重复计算导致性能崩塌。
- **阈值机制:** 根据具体的法律管辖区（Domain）进行动态阈值调整，而非一刀切。
- **集成方式:** 核心逻辑封装为核心 Pipeline 节点，外层包装一个独立的 CLI 工具供日常批量审计使用。

## 四、验证与测试

### 对抗测试扩展

- **目录划归:** 新建 `tests/adversarial/` 专有目录，与常规的单元测试、集成测试并列。
- **生成策略:** 采用混合生成法。针对时态冲突、举证责任倒置等强法理逻辑场景，由人工设计极端的"法理悖论边界案卷"；针对依赖图传播和粗糙集上下近似，使用 `Hypothesis` 进行 Property-based 自动模糊测试。
- **最低容忍标准:** 所有测试模块必须通过 `test_no_crash_and_valid_schema` 校验，即"不可抛出未捕获异常 + 输出必须通过 Pydantic 结构化校验"。

### Benchmark 扩展

- **规模:** 精准扩容至 25 个核心 Cases。
- **Expected 值审计:** 由现有推理引擎自动化生成初稿，再由法学专家（或通过高阶法理规则链）进行人工双盲逐项审核标注。

## 五、架构决策

### 代码组织

建议重构目录如下：

```
├── theory/                        # 核心法理逻辑推导层（纯Python实现）
│   └── engines/                   # 包含时态、粗糙集等具体引擎
├── verification/                  # 新增：符号验证与一致性检查器
│   ├── z3_verifier.py             # Z3 验证器
│   └── judgment_deviation.py      # 偏离度检查器
├── proofs/
│   ├── formal/                    # 新增：统一存放 Lean4 源码与 sorry 证明
│   │   ├── BanachEffectiveNodes.lean
│   │   └── FiniteRosetta.lean
│   └── engineering_proof_artifacts/
│       └── cross_jurisdiction/    # 存放工程验证脚本
```

### 依赖管理

- **新增依赖许可:** 批准引入 `networkx`（图度量与依赖图计算的底层刚需）和 `scipy`（统计自助法 CI 校准）。鉴于系统并不进行大量图表绘制，拒绝引入 `matplotlib`，可视化部分交由前端或轻量级 Markdown 文本报告完成。
- **Python 版本要求:** 维持 Python 3.12.5+ 限制，充分利用高级类型提示（PEP 695）和性能优化，暂不向下兼容 3.10。

## 六、基于投入产出比（ROI）的优先级路线图

综合"工作量"、"数学价值"与"产品价值"，建议将开发周期划分为四个波次（Sprints）：

| 波次 | 任务项 | 估算时耗 | 决策理由 |
|---|---|---|---|
| **Wave 1: 核心阻断修复** | Bug 1 分词修复; Bug 2 前向推导; Benchmark 扩展 | 10min / 30min / 2h | 极低投入，极高产出。迅速稳固既有测试基准。 |
| **Wave 2: 产品价值变现** | F4 偏离度检查器; 对抗测试扩展; H1 DP 平滑 | 3-4h / 5h / 1h | 偏离度检查是面向用户交付的核心产品亮点，配合对抗测试能显著压低产品线缺陷率。 |
| **Wave 3: 数学边界合规** | Z3 验证器; Lean Banach 2 sorry; Lean Rosetta 3 sorry | 4-6h / 2-3h / 3-5h | 开始向形式化系统充实数学证明，确保模型本身的逻辑自洽性。 |
| **Wave 4: 理论深水区突破** | F1 时态集成; F2 Obstruction Checker; Lean Galois 4 sorry | 5-8h / 2-3h / 5-8h | 属于高投入的长期演进项。在 Wave 1-3 筑牢地基后，再行攻克这几项高难度任务。 |
