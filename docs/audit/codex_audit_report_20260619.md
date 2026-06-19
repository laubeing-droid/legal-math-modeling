# JC 数学模型深化 — Codex 审计报告

> **审计日期：** 2026-06-19
> **审计范围：** Playbook #91-100 全量任务 + 隐藏任务发现 + 代码修复方案
> **审计依据：** 仓库实况扫描、既有审计产物复核、proof/benchmark/adversarial/Lean 产物抽查、关键源码核对
> **工作区：** `D:\Claude\数学证明\legal-math-modeling`

---

## 0. 审计执行摘要

### 0.1 总体判断

原 Playbook 的研究方向成立。本次审计在 Codex 2026-06-18 修订版基础上，形成了较完整的推进清单；但本报告原稿有若干“完成态”表述需要降级为“已核实 / 部分核实 / 待清理”。二次复核后的结论如下：

1. **核心三份状态文件的主统计口径已统一**（theorem_status_matrix / ARTIFACT_MANIFEST / proof_run_results）：10 PROVED / 3 REFUTED / 4 PENDING_TOOLCHAIN / 0 FAILED；但 `docs/audit/proof_ledger.json` 仍是 audit-fix-2 旧口径，不能称为全审计总账已统一。
2. **17 个 proof artifacts 的最新运行记录可核实**，`proof_run_results.json` 显示耗时 126.03s、overall PASS。
3. **31 个对抗性测试产物可核实**，结果为 31/31 通过；但 ADV-014a/ADV-014b 是“known blind spot 被记录”的通过，不代表下划线矛盾检测缺陷已修复。
4. **13 个 benchmark cases manifest 可核实**，覆盖 5 个法律域；但尚未发现 `multi_model_comparison.py` 或等价 runner，不能写成“多模型期望输出已运行验证”。
5. **Lean 4.30.0 + Mathlib v4.30.0 安装已核实**，二次复核运行 `lake build` 通过 2944 jobs；但既有 Lean proof artifacts 仍包含可执行 `sorry`，证据等级不能升级。
6. **theory 模块数量需修正**：当前扫描为根目录 53 个 `theory/*.py`、递归 58 个 `theory/**/*.py`；原“51 个理论模块”应解释为历史/筛选口径，不能作为当前全仓事实。
7. **#94 与 #95 有可行落地路径**，但 #94 的 `claim_mapping.csv` 是总计 44 行、其中 CN_ONLY 30 行；#95 的 180 条 claims 已通过 6 个 `*_claims.json` 的 `claims` 数组复核。

### 0.2 关键数字

| 指标 | 值 |
|---|---|
| Proof artifacts 总数 | 17 |
| PROVED | 10 |
| REFUTED | 3 |
| PENDING_TOOLCHAIN | 4 |
| FAILED | 0 |
| 对抗性测试 | 31（按预期通过；含 2 个盲区记录） |
| Benchmark cases | 13（5 个法律域） |
| 理论模块总数 | 当前根目录 53；递归 58；原 51 需说明筛选口径 |
| 有 proof number 的模块 | 20 |
| 不在 proof_ledger 中的模块 | 14+ |
| 隐藏任务 | 10（H1-H10） |
| 需要修复的代码缺陷 | 2 |
| Lean sorry 总数 | 可执行 `sorry` 5 处；文本出现 11 次；涉及 4 个 Lean 文件路径（含 engineering copy） |
| 重复文件 | 2 对 |

### 0.3 二次审计修订意见

本报告可以作为后续执行入口，但必须补上以下修订：

| 项 | 二次审计判定 | 需要写入后续任务 |
|---|---|---|
| 状态总账 | 主统计统一，但 `proof_ledger.json` 仍旧 | 更新 `proof_ledger.json`，或在报告中明确其为历史账本 |
| ART-011 | 顶层状态已 PROVED，但 manifest 附属字段仍写 `missing_toolchain` / `interim evidence` | 清理 ART-011 的旧 limitation/notes 字段 |
| 对抗测试 | 31/31 通过属实；其中 2 个是 expected-known-blind-spot | 把 ADV-014a/b 标为 `expected_failure_documented` 或单列 defect tests |
| Benchmark | 13 条 manifest 属实 | 实现 runner 后才能写“期望输出已验证” |
| Lean | Mathlib 工程 build 属实 | 既有 Lean theorem 无 `sorry` 前保持 PENDING |
| theory 盘点 | 当前扫描不是 51 | 报告改为 53 root / 58 recursive，或注明 51 的过滤条件 |
| #94 数据 | CN_ONLY=30 属实，但总行数为 44 | 报告写“44 mappings，其中 30 CN_ONLY” |
| #95 数据 | 180 claims 属实 | 明确这些是结构化 claims，不等价于真实校准样本 |

---

## 1. 已完成工作明细

### 1.1 口径统一（Phase A-1）

**变更文件：**
- `docs/audit/theorem_status_matrix.md`：Audit Fix 2 → Audit Fix 3，日期 2026-06-11 → 2026-06-18
- `proofs/engineering_proof_artifacts/ARTIFACT_MANIFEST.json`：ART-011 状态 PENDING_TOOLCHAIN → PROVED

**口径差异根因：** ART-011（Graph Similarity Range Z3）在旧 manifest 中被标记为 PENDING_TOOLCHAIN（假设需要 Z3 binary），但 Python z3 bindings 可用，proof_run_results.json 实际运行结果为 PROVED。

**统一后口径：**

| 来源 | PROVED | REFUTED | PENDING | FAILED | 总计 |
|---|---:|---:|---:|---:|---:|
| proof_run_results.json | 10 | 3 | 4 | 0 | 17 |
| ARTIFACT_MANIFEST.json | 10 | 3 | 4 | 0 | 17 |
| theorem_status_matrix.md | 10 | 3 | 4 | 0 | 17 |

**二次审计补充：**

- `docs/audit/proof_ledger.json` 仍保留 `version: audit-fix-2`、`run_all_proofs_sandbox: 9/3/5`、`lean: no Mathlib` 等旧口径。若它继续作为总账使用，必须同步更新；若不再作为总账，应在文件头标记为 historical ledger。
- `ARTIFACT_MANIFEST.json` 中 ART-011 的顶层状态已是 `PROVED` / `SMT_PROVED_FINITE`，但仍残留 `missing_toolchain: Z3 Python bindings`、`Cannot be verified without Z3 Python bindings`、`interim evidence` 等旧字段。建议清理附属字段，避免状态自相矛盾。

### 1.2 全量 Proof Artifacts 验证（Phase A-2）

运行命令：`python proofs/engineering_proof_artifacts/run_all_proofs.py`

| ID | 名称 | 状态 | 证据等级 | 运行时间 |
|---|---|---|---|---:|
| ART-001 | Finite Galois Adjunction | PROVED | EXHAUSTIVE_FINITE_PROOF | 8.75s |
| ART-003 | Bounded Horn Correctness | PROVED | EXHAUSTIVE_FINITE_PROOF | 0.63s |
| ART-004 | Horn Termination Measure | PROVED | EXHAUSTIVE_FINITE_PROOF | 11.68s |
| ART-006 | Production Bounded Termination | PROVED | EXHAUSTIVE_FINITE_PROOF | 0.15s |
| ART-008 | Dung Grounded Extension | PROVED | EXHAUSTIVE_FINITE_PROOF | — |
| ART-009 | Stratified Correspondence | PROVED | EXHAUSTIVE_FINITE_PROOF | — |
| ART-010 | Graph Similarity Range | PROVED | SYMBOLIC_PROVED | — |
| ART-011 | Graph Similarity Range (Z3) | PROVED | SMT_PROVED_FINITE | — |
| ART-015 | Siegel Repeated Median | PROVED | EXHAUSTIVE_FINITE_PROOF | — |
| ART-016 | Banach Effective Nodes | PROVED | SYMBOLIC_PROVED | — |
| ART-012 | Graph Metric Counterexamples | REFUTED | REFUTED_BY_COUNTEREXAMPLE | — |
| ART-013 | DP Floor Clipping Analysis | REFUTED | REFUTED_BY_COUNTEREXAMPLE | — |
| ART-014 | Clipped Theil-Sen Refutation | REFUTED | REFUTED_BY_COUNTEREXAMPLE | — |
| ART-005 | Bounded Horn (Z3 .smt2) | PENDING | PENDING_TOOLCHAIN | — |
| ART-002 | Finite Galois Adjunction (Lean) | PENDING | PENDING_TOOLCHAIN | — |
| ART-017 | Banach Effective Nodes (Lean) | PENDING | PENDING_TOOLCHAIN | — |
| ART-007 | Evaluator Termination (TLA+) | PENDING | PENDING_TOOLCHAIN | — |

### 1.3 对抗性测试（任务 #96）

**文件：** `proofs/engineering_proof_artifacts/adversarial/adversarial_input_checks.py`
**结果：** `proofs/engineering_proof_artifacts/adversarial/adversarial_results.json`

31 个测试，8 个类别。注意：全部通过表示测试脚本按预期记录了行为，其中 ADV-014a/ADV-014b 是“已知盲区被确认存在”的通过，不等同于缺陷已修复。

| 类别 | 测试数 | 通过 | 发现 |
|---|---:|---:|---|
| 跨域误触发 | 2 | 2 | 刑事事实不触发民事规则 ✓ |
| 证据不足 | 3 | 3 | 单事实不触发多前提规则 ✓ |
| 噪声注入 | 3 | 3 | 有效 claim 保持，噪声触发 VOID 攻击 ✓ |
| 边界值 | 5 | 5 | 空字符串/10K字符/重复/Unicode/未知 namespace ✓ |
| 矛盾检测 | 5 | 5 | **确认 2 个已知盲区仍存在**（见 §2.1） |
| 退化规则集 | 4 | 4 | 空规则/重言式/循环例外 ✓ |
| 结构化输出 | 6 | 6 | DungFrame/InferenceChain 字段完整性 ✓ |
| Namespace 隔离 | 2 | 2 | 共享 token 不触发跨域规则 ✓ |

### 1.4 Benchmark Manifest（任务 #97 前半）

**文件：** `data/benchmarks/multi_model_cases.jsonl`

13 个 benchmark cases，覆盖 5 个法律域。二次审计确认 manifest 存在且有 13 行；但尚未发现多模型 comparison runner，因此这里的“期望”是静态 benchmark 标注，不是运行验证结论。

| Case ID | 域 | 难度 | 描述 | 期望 |
|---|---|---|---|---|
| BENCH-01 | contract | easy | 简单违约 | BREACH_ESTABLISHED |
| BENCH-02 | contract | medium | 不可抗力例外 | FORCE_MAJEURE_DEFENSE |
| BENCH-03 | criminal | easy | 犯罪构成 | CRIME_ESTABLISHED |
| BENCH-04 | criminal | medium | 正当防卫例外 | JUSTIFICATION_DEFENSE |
| BENCH-05 | contract | easy | 证据不足 | 无 claim |
| BENCH-06 | cross | medium | 跨域不误触发 | CRIME_ESTABLISHED only |
| BENCH-07 | tort | easy | 侵权全链 | TORT_LIABILITY |
| BENCH-08 | tort | medium | 受害人过错 | CONTRIBUTORY NEGLIGENCE |
| BENCH-09 | contract | hard | 三方例外链 | CLAIM_C（最深例外胜） |
| BENCH-10 | admin | medium | 行政许可撤销 | REVOCATION_UPHELD |
| BENCH-11 | data | medium | 数据跨境合规 | GDPR + PIPL |
| BENCH-12 | contract | easy | 零事实 | 无 claim |
| BENCH-13 | contract | medium | 噪声注入 | BREACH + NOISE |

### 1.5 Lean 4 + Mathlib 安装

**工程位置：** `proofs/lean/juris_lean/`

| 项目 | 值 |
|---|---|
| Lean 版本 | 4.30.0 |
| Mathlib 版本 | v4.30.0（rev c5ea003） |
| 传递依赖 | 9 个（mathlib, batteries, aesop, Qq, ProofWidgets4, Cli, plausible, importGraph, LeanSearchClient） |
| lake build | 2944/2944 通过 |
| 验证 | `example : 1 + 1 = 2 := by norm_num` ✓ |
| 磁盘占用 | .lake/ 约 2.6 GB |

**二次审计补充：** 在 `proofs/lean/juris_lean/` 重新运行 `lake build`，结果为 `Build completed successfully (2944 jobs).` 这只证明 Mathlib 工程可构建；现有 `proofs/lean/*.lean` 与 `proofs/engineering_proof_artifacts/*/*.lean` 中仍有可执行 `sorry`，不能因此把 Lean proof artifacts 从 `PENDING_TOOLCHAIN/PENDING_PROOF` 升级为已证明。

---

## 2. 已知问题与修复方案

### 2.1 `_contains_word_boundary` 分词盲区

**文件：** `theory/evidence_evaluation.py:123-134`
**严重性：** 中
**影响：** `detect_contradiction` 对下划线连接的 fact（如 `"contract_signed"`）无法检测矛盾

**根因：** `text.split()` 只按空格分词，`"contract_signed".split()` = `["contract_signed"]`，`"signed" not in ["contract_signed"]`。

**修复方案：**
```python
import re

def _contains_word_boundary(text: str, phrase: str) -> bool:
    if " " in phrase:
        return phrase in text
    tokens = re.split(r'[\s_\-]+', text.lower())
    return phrase.lower() in tokens
```

**验证：** 修复后 `_contains_word_boundary("contract_signed", "signed")` → True
**工作量：** 10 分钟
**回归风险：** 低，但不是零。必须新增回归用例确认 `"unsigned"` 不误匹配 `"signed"`，并确认 `not_signed`、`not-signed`、`not signed` 三种形式都能被一致处理。

### 2.2 `construct_frame` 无迭代前向推导

**文件：** `theory/argumentation_horn_unification.py:192-254`
**严重性：** 中
**影响：** 多跳规则链（r1→r2，r1 的结论是 r2 的前提）无法被 AAF 框架捕获

**根因：** `_premises_satisfied(rule)` 只检查初始事实集 `self.facts`，不追踪中间推导结论。`self.facts` 在 `__init__` 后从不修改。

**修复方案：**
```python
def _compute_forward_closure(self) -> Set[str]:
    """迭代前向链推导，计算所有可推导的事实。"""
    facts = set(self.facts)
    changed = True
    while changed:
        changed = False
        for rule in self.rules.values():
            if rule.head not in facts and all(p in facts for p in rule.premises):
                facts.add(rule.head)
                changed = True
    return facts

def construct_frame(self) -> DungFrame:
    closure = self._compute_forward_closure()
    # 后续用 closure 替代 self.facts 做前提检查
    ...
```

**影响范围：** BENCH-01 的 `LIABILITY_GRANTED` 将被正确捕获
**工作量：** 30 分钟
**回归风险：** 中。closure 应仅覆盖 strict Horn 层，不能把 rebuttal/exception 层提前混入单调闭包；同时需要对循环规则设置 “facts 只增不减、最多新增有限 head” 的终止断言。需同步更新 benchmark expected 值。

### 2.3 `model_status.py` 状态判定

**结论：准确，不需要修改。**

| Claim ID | 当前状态 | 判定依据 |
|---|---|---|
| A1_REAL_ROSETTA | DATA_INSUFFICIENT | 44 行数据，7 个 witness，无全域证明 |
| A1_TOY_ROSETTA | TOY_SYNTHETIC | 243 赋值，零满足，仅玩具模型 |
| C_REAL_BANACH | DATA_INSUFFICIENT | 225 观测为代理数据（费率表），0 真实时薪 |
| C_TOY_BANACH | TOY_SYNTHETIC | 仅标量收缩，多维未证明 |
| D_PRIVILEGE_EPSILON | REFUTED | Z3 UNSAT 证明不存在单调函数 |
| E_AAF_GROUNDED | PROVED | 66,066 穷举图，n≤4 |
| E_ORIGINAL_EVALUATOR_MONOTONE | REFUTED | 反例 6.2 |

---

## 3. 隐藏任务清单（Playbook 未覆盖）

### H1. DP Floor Clipping 无限隐私比 [CRITICAL]

**来源：** `docs/audit/counterexample_registry.json` CE-003
**问题：** `max(0.3*x, ...)` 机制产生无限隐私比，违反 ε-DP
**修复：** 替换为 smooth clipping（tanh/sigmoid）、Laplace mechanism on raw values、或 compose floor with epsilon-DP
**工作量：** 1 小时

### H2. Graph Similarity 不是度量 [HIGH]

**来源：** CE-001（反射性失败）、CE-002（同一性失败：C4 vs Star+Edge 得分 1.0）
**影响：** 所有将 similarity 用作 equality proxy 的调用方需要审计
**工作量：** 2 小时（审计 + 修复调用方）

### H3. trust_label_schema 未被程序强制 [HIGH]

**来源：** `docs/audit/trust_label_schema.json` 仅被 4 个文档文件引用
**问题：** `model_status.py` 有独立的 `EvidenceStatus` enum（7 值），与 schema 的 8 个标签部分重叠但不派生
**修复：** 统一为单一 Python enum，从 trust_label_schema.json 派生
**工作量：** 1-2 小时

### H4. 14+ 理论模块不在审计范围内 [MEDIUM]

以下模块存在于 `theory/` 但未被 proof_ledger 追踪：

| 模块 | 功能 | 验证状态 |
|---|---|---|
| bayesian_legal_reasoning.py | 序列贝叶斯更新 + BN 推理 | 有 demo，无正式证明 |
| argument_clustering.py | 法律论证聚类 | 有 demo |
| arbitration_reasoning.py | 仲裁推理 | 有 demo |
| criminal_sentencing.py | 量刑指南 | 有 demo |
| cross_border_data.py | GDPR/PIPL 碰撞检测 | 有 demo |
| compliance_monitoring.py | 合规监控 | 有 demo |
| ip_valuation.py | 知识产权估值 | 有 demo |
| interest_balancing.py | 利益平衡 | 有 demo |
| precedent_reasoning.py | 先例推理 | 有 demo |
| probabilistic_damages.py | 概率损害赔偿 | 有 demo |
| litigation_game_theory.py | 诉讼博弈论 | 有 demo |
| legal_interpretation.py | 法律解释方法 | 有 demo |
| case_retrieval.py | 案例检索 | 有 demo |
| data_quality_label.py | 数据质量标签 | 引用 model_status |

**建议：** 为每个模块定义最小验证标准（PBT / 穷举 / 符号），逐步纳入 proof_ledger。

### H5. 2 对完全重复文件 [LOW]

| 文件 A | 文件 B | md5 |
|---|---|---|
| `theory/kolmogorov_mdl_rules.py` | `theory/conjecture/kolmogorov_mdl_rules.py` | 9f04614... |
| `theory/hierarchical_bayes_alpha.py` | `theory/spec/hierarchical_bayes_alpha.py` | 相同 |

**建议：** 删除重复，保留 canonical 版本（根目录），conjecture/spec 目录改为引用。

### H6. 论文声称 18 positive results 但部分只是测试演示 [MEDIUM]

| 定理 | 论文声称 | 实际证据 |
|---|---|---|
| Theorem 7.4（temporal guard） | 形式化证明 | 3-world 时间线 + 100 随机对测试 |
| Theorem 11.2（CBL non-interference） | 60 条 CBL 规则 | 只演示了 6 US + 4 CN 概念 |
| Proposition 7.6（LTL 嵌入保持可达性） | 已证明 | LTL 算子已实现，但对应性证明缺失 |

**建议：** 论文中标注证据等级差异，或补充穷举验证。

### H7. Ontology L2 只实现了 contract law [MEDIUM]

**来源：** `docs/ontology/core_ontology.yaml`（1299 行）
**问题：** L0 定义了 corporate/labor/tort/family/IP 子类型，L2 只有 contract 的完整概念。`evolution_rules`（Instalments_Logic、Perished_Goods_Logic、NemoDat_Logic）定义了但未实现。

### H8. Temporal Reasoning 模块未集成 [MEDIUM]

**涉及文件：**
- `theory/temporal_law_engine.py`：双时间戳法律引擎
- `theory/temporal_kripke_ltl.py`：LTL 时态逻辑
- `theory/temporal_statute_law.py`：程序从新/实体从旧

**问题：** `governing_law_snapshot()` 从未被 evidence_evaluation 或 argumentation 模块调用。Horn closure 不考虑法律版本变更。

### H9. bridge/bridge_fixpoint.py 永远输出 "Bridge not available" [LOW]

**原因：** 尝试导入 `compiler_core.evaluator.FixpointEvaluator`，但 `compiler_core/` 目录不存在。

### H10. mutation_suite.py 未被 CI 调用 [LOW]

**位置：** `theory/mutation/mutation_suite.py`
**状态：** 变异测试框架已实现（inequality_swap / constant_corrupt / assert_delete / stub_return），但未被任何自动化流程触发。

---

## 4. 任务 #94（MDL vs FP）落地路径

### 4.1 原阻塞

"无 FP 标签，原路径 `tools/mdl_fp_analysis.py` 不存在"

### 4.2 发现的可用数据源

| 数据源 | 位置 | 可用作 | 条目数 |
|---|---|---|---:|
| `claim_mapping.csv` 的 `mapping_status` | `data/category_rosetta/` | CN_ONLY = 跨域 FP 风险代理 | 总 44；其中 CN_ONLY 30 |
| `obstruction_analysis.json` | `data/category_rosetta/` | COLLISION/ASYMMETRY = 映射失败证据 | 12 类型 |
| 法规文本 `*_statutes_v2.csv` | `data/cn_legal/` | 文本长度/条件数/例外数 → MDL 代理 | 45 CSV |
| AAF 异常结构 `yd_*.csv` | `data/aaf_legal/` | 含"但"/"除外"条款 → 复杂度指标 | 11 CSV |

### 4.3 已有计算函数

```python
# theory/kolmogorov_mdl_rules.py:59-93
class RuleComplexity:
    def minimum_description_length(self) -> float
    def false_positive_probability(self, wrong_domain_facts: int) -> float
```

### 4.4 最小可行方案

1. 从 `*_statutes_v2.csv` 提取法规文本，计算文本 MDL 代理（字符长度、条件数、例外词频）
2. 从 `claim_mapping.csv` 取 `mapping_status` 作为 FP 风险标签：CN_ONLY=1，其他=0
3. 用 `RuleComplexity.minimum_description_length()` 计算 MDL
4. Spearman 秩相关 + bootstrap CI
5. 输出 CSV 报告，含显著/不显著两种结论

**工作量：** 2-3 小时
**限制：** CN_ONLY 作为 FP 代理有噪声，需在报告中声明

---

## 5. 任务 #95（贝叶斯校准）落地路径

### 5.1 原阻塞

"无 calibration 数据集、无案例 manifest、预测目标未定义"

### 5.2 发现的可用数据源

| 数据源 | 位置 | 内容 | 条目数 |
|---|---|---|---:|
| `*_claims.json`（6 个文件） | `data/cn_legal/` | 结构化 claim + hard_case + positive_control + verification_status | 180 |
| `proof_run_results.json` | `proofs/engineering_proof_artifacts/` | PROVED/REFUTED 二元结果 | 17 |
| `aaf_validation_summary.json` | `data/aaf_legal/` | 18 个模式的稳定性比较 | 18 |
| `SIMULATED_CASES` | `theory/hierarchical_bayes_alpha.py` | 10 个标注案例 | 10 |

**二次审计补充：** 180 条 claims 的数量已复核，来源是 6 个 JSON 文件中各 30 条 `claims`。但这些是结构化 claim/control 样本，不等同于真实裁判结果校准集；用于 #95 时必须把结论写成“内部标签校准 / proxy calibration”，不能直接写成真实司法结果校准。

### 5.3 已有贝叶斯基础设施

```python
# theory/bayesian_legal_reasoning.py
class BayesianReasoning:
    def update(self, prior, likelihood_ratio) -> float
class BayesianNetwork:
    def compute_posterior(self, target, evidence) -> float

# theory/hierarchical_bayes_alpha.py
class HierarchicalAlphaModel:
    def simulate_posterior_draws(self, n_draws) -> List[float]
    def compute_bayesian_credible_interval(self, draws, level) -> Tuple
```

### 5.4 预测目标定义

| 目标 | 数据 | 描述 |
|---|---|---|
| 二元分类 | 180 条 claims | P(positive_control=true \| domain, hard_case) |
| 校准曲线 | 17 条 proof results | P(correct \| PROVED/REFUTED) |
| 稳定性预测 | 18 条 AAF stability | P(Dung_more_stable \| rule_features) |

### 5.5 最小可行方案

1. 创建 `data/calibration/case_manifest.jsonl`（合并 180 + 17 + 18 条）
2. 预测目标：二元分类（positive_control vs not）
3. 用 `BayesianReasoning` 计算后验：Prior = positive_control 比例，Likelihood 按 hard_case 区分
4. Bootstrap 替代 MCMC（n=180 不需要 PyMC）
5. 输出后验 + 校准曲线

**工作量：** 3-4 小时
**限制：** 180 条全标为 `confidence_expected: "high"`，无置信度梯度，需用 `hard_case` 代理区分

---

## 6. 理论模块全量盘点

### 6.1 核心数学证明（20 个，有 proof number）

| # | 模块 | 证据类型 | 外部依赖 |
|---|---|---|---|
| 1 | galois_reverse_index.py | 有限穷举 | 无 |
| 2 | bounded_horn_correctness.py | 有限穷举 | 无 |
| 2-A | hypothesis_horn_pbt.py | PBT | hypothesis |
| 3 | evidence_credibility_axioms.py | 公理化证明 | 无 |
| 3-A | sympy_evidence_proofs.py | 符号证明 | sympy |
| 4 | kripke_supersedes_corrects.py | Kripke 模型 | 无 |
| 4-A | z3_kripke_mutex.py | Z3 SMT | z3-solver |
| 5 | temporal_kripke_ltl.py | LTL 模型 | 无 |
| 5-A | z3_temporal_induction.py | Z3 归纳 | z3-solver |
| 6 | policy_expressiveness.py | CTRS 复杂度 | 无 |
| 7 | gradual_verification_soundness.py | 安全编译器 | 无 |
| 8 | trirail_complexity.py | TriRail P 完全 | 无 |
| 9 | argumentation_horn_unification.py | Horn-Dung 桥 | 无 |
| 10 | counts_as_institutional_facts.py | Searle counts-as | 无 |
| 11 | rough_set_discretionary.py | 粗糙集 | 无 |
| 12 | hierarchical_bayes_alpha.py | 层次贝叶斯 | 无（演示） |
| 13 | paradigm_incommensurability.py | 测度论不可通约 | 无 |
| 14 | deontic_procedural_justice.py | 道义逻辑 | 无 |
| 15 | non_interference_cbl.py | Bell-LaPadula | 无 |
| 16 | category_theory_rosetta.py | 范畴论 Rosetta | 无 |
| 17 | banach_pricing_contraction.py | Banach 收缩 | 无 |
| 18 | dp_legal_privilege.py | DP 特权映射 | 无 |
| 19 | abstract_interpretation_unified.py | 抽象解释统一 | 无 |
| 20 | kolmogorov_mdl_rules.py | MDL-Kolmogorov | 无 |

### 6.2 应用/领域模块（20+ 个，无 proof number）

| 模块 | 功能 | 数据依赖 |
|---|---|---|
| bayesian_legal_reasoning.py | 序列贝叶斯 + BN | 无 |
| evidence_evaluation.py | 证据评分 + 矛盾检测 + 推理链 | 无 |
| evidence_dependency_manager.py | 依赖图传播 | model_status |
| burden_of_proof_tracker.py | 举证责任转移 | 无 |
| temporal_law_engine.py | 双时间戳引擎 | 无 |
| temporal_statute_law.py | 程序从新/实体从旧 | 无 |
| litigation_game_theory.py | 诉讼博弈 | 无 |
| analogical_reasoning.py | 案例类比 | 无 |
| precedent_reasoning.py | 先例推理 | 无 |
| argument_strength_ordering.py | 论证强度排序 | 无 |
| probabilistic_damages.py | 概率损害 | 无 |
| case_retrieval.py | 案例检索 | 无 |
| dialectical_argumentation_tree.py | 辩证论证树 | 无 |
| legal_interpretation.py | 法律解释 | 无 |
| ip_valuation.py | 知识产权估值 | 无 |
| argument_clustering.py | 论证聚类 | 无 |
| compliance_monitoring.py | 合规监控 | 无 |
| arbitration_reasoning.py | 仲裁推理 | 无 |
| cross_border_data.py | GDPR/PIPL 碰撞 | 无 |
| aspic_plus_framework.py | ASPIC+ 框架 | 无 |
| criminal_sentencing.py | 量刑指南 | 无 |
| interest_balancing.py | 利益平衡 | 无 |
| damages_attribute_grammar.py | 损害属性文法 | 无 |
| formal_concept_analysis.py | 形式概念分析 | 无 |
| data_quality_label.py | 数据质量标签 | model_status |
| k3_empirical_analysis.py | k≤3 经验分析 | rules.yaml |

### 6.3 子目录模块

| 目录 | 文件 | 状态 |
|---|---|---|
| bridge/ | bridge_fixpoint.py | 永远 "Bridge not available"（compiler_core 不存在） |
| conjecture/ | kolmogorov_mdl_rules.py | **与根目录文件完全重复**（md5 相同） |
| spec/ | abstract_interpretation_unified.py | 更强版本（声称 18 定理可从 Galois 推导），根目录版本为审计后降级版 |
| spec/ | hierarchical_bayes_alpha.py | **与根目录文件完全重复**（md5 相同） |
| mutation/ | mutation_suite.py | 变异测试框架，未被 CI 调用 |

### 6.4 依赖关系

**所有模块自包含，无循环依赖。** 仅 3 个模块导入 `model_status.py`：
- `evidence_dependency_manager.py`
- `data_quality_label.py`
- `category_theory_rosetta.py`（可选）

**无模块导入其他 theory/*.py。**

---

## 7. 任务状态总览

### 7.1 Playbook 任务（#91-100）

| 任务 | 名称 | 优先级 | 状态 | 阻塞项 |
|---|---|---|---|---|
| #91 | Lean4 形式化 | P0 | **工具链前置完成**（Mathlib 安装并 build 通过） | 可执行 `sorry` 5 处待消除；旧 Lean artifact 仍不得升级 |
| #92 | 可解释性论文 | P0 | **部分前置完成**（主统计口径 + #96 产物） | 需 #97 runner + #93 checker + proof_ledger/manifest 残留口径清理 |
| #93 | 范畴论 obstruction | P1 | **可执行** | 需写 checker |
| #94 | MDL vs FP 实证 | P1 | **可执行**（找到 4 个数据源） | 需定义 MDL 代理 + FP 标签映射 |
| #95 | 贝叶斯校准 | P1 | **可执行但只能先做 proxy calibration**（180 条结构化 claims） | 需定义预测目标 + 合并 manifest + 标注非真实司法结果校准 |
| #96 | 对抗性测试 | P0 | **测试产物完成**（31 个按预期通过） | 2 个 known blind spots 尚未代码修复 |
| #97 | 多模型对比 | P0 | **manifest 完成** | 需写 comparison.py；runner 完成前不得称“期望输出已验证” |
| #98 | 知识图谱 | P2 | **可执行** | 需写 builder.py |
| #99 | 规则分类器 | P2 | **可执行** | 需定义标签映射 |
| #100 | 联邦学习 | P3 | **不可执行** | 无第二方数据、无 DPA |

### 7.2 隐藏任务（H1-H10）

| 任务 | 严重性 | 可执行 | 工作量 |
|---|---|---|---|
| H1 DP floor clipping | CRITICAL | 是 | 1h |
| H2 graph similarity 审计 | HIGH | 是 | 2h |
| H3 trust_label_schema 程序化 | HIGH | 是 | 1-2h |
| H4 14 模块证据化 | MEDIUM | 是 | 8-12h |
| H5 去重 2 对文件 | LOW | 是 | 10min |
| H6 论文声称校正 | MEDIUM | 是 | 2h |
| H7 ontology L2 扩展 | MEDIUM | 是 | 6-9h |
| H8 temporal 集成 | MEDIUM | 是 | 5-8h |
| H9 bridge 修复 | LOW | 否（需 compiler_core） | — |
| H10 mutation CI 集成 | LOW | 是 | 2h |

---

## 8. 建议执行顺序

### Phase B（立即，1-2 天）

0. 先清理审计口径：更新或标记 `proof_ledger.json`，清理 ART-011 manifest 残留旧字段，明确 51/53/58 theory 模块计数口径（30-45min）
1. 修复 `_contains_word_boundary`（10min）
2. 修复 `construct_frame` 前向推导（30min）
3. 写 `theory/multi_model_comparison.py`（#97，2h）
4. 写 `cross_jurisdiction/no_functor_finite_checker.py`（#93，2h）

### Phase C（本周，2-3 天）

5. #94 MDL vs FP 最小可行版（2-3h）
6. #95 贝叶斯校准最小可行版（3-4h）
7. 论文骨架 `paper/explainable_legal_reasoning.md`（3-5h）

### Phase D（下周，3-5 天）

8. Lean sorry 消除：Banach → Rosetta → Galois（3-5h）
9. #98 知识图谱（2-3h）
10. #99 分类器 baseline（3-4h）
11. H1 DP floor clipping 修复（1h）
12. H3 trust_label_schema 程序化（1-2h）

### Phase E（后续深化）

13. H8 temporal reasoning 集成（5-8h）
14. H6 CBL non-interference 穷举（3-4h）
15. H4 14 模块证据化（8-12h）

---

## 9. 红线（与 Codex 审计修订版一致）

- 不把完整 evaluator 写成 monotone。
- 不把 toy finite proof 写成真实法律全域 theorem。
- 不把 proxy/synthetic 数据写成真实实证结论。
- 不把缺工具链项写成已证明。
- 不把未发现的路径写成已存在。
- **新增：** 不把 `_contains_word_boundary` 的下划线盲区当作"已修复"，除非代码已实际修改。
- **新增：** 不把 14 个未追踪模块当作"已验证"，除非纳入 proof_ledger。
- **新增：** 不把论文的 18 positive results 当作全部铁证，除非标注每条的证据等级。

---

## 10. 审计签字

| 项目 | 状态 |
|---|---|
| 三份核心状态文件口径 | 主统计统一 ✓；`proof_ledger.json` 仍为旧口径，ART-011 附属字段待清理 |
| 17 个 proof artifacts | 全部可复现 ✓ |
| 31 个对抗性测试 | 31/31 按预期通过 ✓；其中 2 个为 known-blind-spot 记录，不是代码修复 |
| 13 个 benchmark cases | manifest 已存在 ✓；runner 验证待完成 |
| Lean + Mathlib | 安装完成，build 通过 ✓ |
| 理论模块盘点 | 当前扫描 53 root / 58 recursive；原 51 需说明筛选口径 |
| #94 落地路径 | 已找到数据源 ✓；`claim_mapping.csv` 为总 44 行、CN_ONLY 30 行 |
| #95 落地路径 | 已找到 180 条结构化 claims ✓；仅支持 proxy calibration 起步 |
| 隐藏任务 | 10 项已记录 ✓ |
| 代码缺陷 | 2 个已定位 + 修复方案 ✓；尚未实际修复 |
