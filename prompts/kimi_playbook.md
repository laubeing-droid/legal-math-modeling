# juris-calculus 最终 Playbook：先补证明，再落地完善

本 playbook 给 Kimi 多 agent 使用。目标是一次性完成：

1. 补完、修正或反例化未尽数学证明。
2. 根据证明结果做必要工程完善。
3. 把 proof artifacts、状态矩阵、工程闭环、测试结果全部交付到指定目录。

核心原则：**Proof first, engineering follows proof boundaries.**

## 0. 固定路径

```text
源码目录：D:\Codex\juris-calculus\源码
实验数据目录：D:\同步网盘\软件开发\论文\实验数据
日志目录：D:\同步网盘\软件开发\日志
最终成功交付目录：D:\Codex\juris-calculus\20260611kimi
证明交付目录：D:\Codex\juris-calculus\20260611kimi\proof_artifacts
```

创建目录：

```powershell
New-Item -ItemType Directory -Force -LiteralPath "D:\Codex\juris-calculus\20260611kimi"
New-Item -ItemType Directory -Force -LiteralPath "D:\Codex\juris-calculus\20260611kimi\proof_artifacts"
```

创建日志：

```powershell
$ts = Get-Date -Format "yyyyMMdd_HHmmss"
$log = "D:\同步网盘\软件开发\日志\kimi_proof_then_closure_$ts.md"
New-Item -ItemType File -Force -LiteralPath $log
```

## 0.1 PowerShell / 中文路径 / 编码注意事项

本项目路径包含中文目录：`D:\同步网盘\软件开发\论文\实验数据`、`D:\同步网盘\软件开发\日志`。在 Windows PowerShell 中，中文路径、中文输出、UTF-8 文件读取都容易出问题。必须遵守以下规则。

### 必须使用 `-LiteralPath`

对含中文、空格或特殊字符路径，使用：

```powershell
Get-Content -Raw -Encoding UTF8 -LiteralPath "D:\Codex\juris-calculus\juris_calculus_mathematical_modeling_report.md"
Get-ChildItem -Force -LiteralPath "D:\同步网盘\软件开发\日志"
Copy-Item -Force -LiteralPath $src -Destination $dst
```

不要依赖通配符路径或未加引号路径。

### 必须显式 UTF-8

读取中文 Markdown/YAML/JSON：

```powershell
Get-Content -Raw -Encoding UTF8 -LiteralPath $path
Set-Content -Encoding UTF8 -LiteralPath $path -Value $text
```

否则会出现乱码，例如中文报告被读成 `鏁板寤烘ā...`。

### 不要使用 Bash heredoc

PowerShell 不支持：

```bash
python - <<'PY'
print("hello")
PY
```

正确写法：

```powershell
@'
print("hello")
'@ | python -
```

### Python 模块导入要注意 cwd

如果从仓库根目录 `D:\Codex\juris-calculus` 运行：

```powershell
python -c "from legalos_services.legalos_pricing import LegalOSPricingEngine"
```

可能报：

```text
ModuleNotFoundError: No module named 'legalos_services'
```

原因是源码包在：

```text
D:\Codex\juris-calculus\源码
```

优先做：

```powershell
cd /d D:\Codex\juris-calculus\源码
python -c "from legalos_services.legalos_pricing import LegalOSPricingEngine; print('ok')"
```

或在脚本中：

```python
import sys
sys.path.insert(0, r"D:\Codex\juris-calculus\源码")
```

### 中文路径日志建议

写日志时使用绝对路径，并确认目录存在：

```powershell
New-Item -ItemType Directory -Force -LiteralPath "D:\同步网盘\软件开发\日志"
```

### 输出文件名建议

最终交付文件名用 ASCII：

```text
FINAL_REPORT.md
PROOF_LEDGER.json
THEOREM_STATUS_MATRIX.md
```

文件内容可以中文，但文件名尽量英文，降低工具链问题。

## 1. 总执行顺序

不得跳过顺序。

```text
Stage 1: Toolchain and theorem inventory
Stage 2: Proof completion / refutation
Stage 3: Theorem status matrix and proof ledger
Stage 4: Engineering closure based on proof results
Stage 5: Validation and delivery package
```

## 1.1 已知工程坑与经验

以下是前置审计中已经实际遇到过的问题。Kimi 多 agent 执行时必须吸收这些经验，避免重复踩坑。

### 经验 1：报告本身可能因编码读取乱码

PowerShell 默认读取中文 Markdown 可能乱码。审计报告、中文 README、YAML 都要显式 `-Encoding UTF8`。

### 经验 2：当前仓库没有本地 Lean/TLA+/Alloy/Dafny artifact

已检查 `源码/theory`，没有发现：

```text
*.lean
*.tla
*.als
*.smt2
*.dfy
```

因此任何“Lean 已证明”“TLA+ 已检查”“Dafny verified”的说法，在当前仓库内不能直接当真。必须生成 artifact 或标 `PENDING_TOOLCHAIN` / `EXTERNAL_REPORT_ONLY`。

### 经验 3：`theory/proven/` 是历史目录名，不等于真的证明

很多 `theory/proven/*.py` 仍然是 Python 演示、print、assert 样例或架构说明。不要因为路径包含 `proven` 就标 `PROVED`。

### 经验 4：Graph similarity 的空特征行为是当前设计边界

当前源码中空特征自相似不是 1.0，实测为：

```text
sim_empty_self = 0.4
sim_feature_self = 1.0
```

不要为了数学自反性直接把默认改成 1.0。法律案例检索里，“没有事实特征”不应默认强相似。若需要自反行为，必须通过 explicit `empty_feature_policy="reflexive"` 开启。

### 经验 5：Banach 证明只能做窄命题

旧审计曾发现 Banach 映射是恒等映射；后来源码已部分修为 fixed target 的指数平滑形式。现在可证明的只是：

```text
effective_nodes 单维
target 外生固定
f(x)=βT+(1-β)x
```

不能外推到 location/stage/travel/total_hours 全维定价模型。

### 经验 6：Fixpoint 的 Tarski 声明必须拆开

真实 evaluator 包含：

```text
rebuttal
confidence = 0
state_tracker mutation
constraint rules
CriticalClarityFailure
MAX_MODIFICATION_COUNT
```

这些会破坏全局单调性。只能把 pure Horn closure 和 production evaluator bounded termination 分开证明。

### 经验 7：Theil-Sen 当前实现是 clipped variant

`calibrate_theilsen()` 当前会过滤 slope 并 clamp output。它不是纯 Theil-Sen。证明任务应优先反例化“保留原始 Theil-Sen breakdown guarantee”的说法，再新增/验证 Siegel repeated median。

### 经验 8：DP ratio-preserving 不自动等于 tuple-level DP

当前 DP 模块默认 sensitivity 是硬编码 policy parameter，floor clipping 依赖原始 `x0`。不要把 instrumentation 或 ratio preservation 当作 DP proof。

### 经验 9：先 proof，再动工程

不要一上来大改主 evaluator。先完成 proof/refutation，再按证明结果做最小工程闭环。尤其 Dung/stratified evaluator 必须 shadow mode，不能替换默认路径。

### 经验 10：测试命令要兼容 stdlib

项目 `requirements.txt` 未必包含 pytest。新增测试最好用 `unittest`，pytest 可以作为可选补跑。

## 2. 什么叫“证明完成”

### 2.1 LEAN_PROVED 或 LEAN_PROVED_FINITE

要求：

- 有 `.lean` artifact。
- 能用 `lean` 或 `lake env lean` 检查。
- 不含 `sorry`、`admit`、未解释 `axiom`、`unsafe`、placeholder。
- checker 命令和输出写入 ledger。

### 2.2 SMT_PROVED_FINITE

要求：

- 有 `.smt2` 或 Python Z3 script。
- 通过 UNSAT/SAT 反证方式证明或给出反例。
- 明确 finite/bounded/abstract domain。
- checker 命令和结果写入 ledger。

### 2.3 EXHAUSTIVE_FINITE_PROOF

要求：

- Python 或其他脚本完整穷举有限域。
- 明确 domain size、枚举范围、前提条件。
- assert/gate 保护，失败时非零退出。
- 不得声称无限域证明。

### 2.4 MODEL_CHECKED

要求：

- TLA+/Alloy 等模型和配置文件存在。
- model checker 输出存在。
- 明确 scope/bounds。

### 2.5 REFUTED

如果原命题为假，完成方式是：

- 给出最小反例 artifact。
- 将原命题标为 REFUTED。
- 写出可证明的修正版。

### 2.6 PENDING_TOOLCHAIN

如果工具链不可用：

- 可以生成 artifact draft。
- 不能标为 proved。
- 写明缺失工具、安装/运行命令、预期结果。

## 3. 多 Agent 分工

### Proof Coordinator

- 扫描 `源码/theory` 与已有报告。
- 建立 theorem inventory。
- 维护 `THEOREM_STATUS_MATRIX.md` 和 `PROOF_LEDGER.json`。
- 合并各 agent 证明结果。
- 指挥工程闭环只围绕 proof 结果展开。

### Lean/Finite-Domain Agent

- Galois / reverse-index finite-domain proof。
- 优先 Lean；不可用时做 Python exhaustive finite proof + Lean draft。

### SMT/Z3 Agent

- graph similarity range。
- bounded Horn correctness。
- Kripke mutex / temporal invariant 等 SMT 目标。

### Fixpoint/AAF Agent

- pure Horn termination。
- production evaluator bounded operational termination。
- Dung AAF grounded extension。
- stratified correspondence。

### DP/Statistics Agent

- scalar Laplace mechanism。
- ratio-preserving DP 边界。
- floor clipping 分析。
- Banach limited theorem。
- clipped Theil-Sen refutation。
- Siegel repeated median verifier。

### Engineering Closure Agent

- 根据证明/反例结果修改必要代码和文档。
- 反例库、status schema、参数治理、trust metadata。
- 不得抢在 proof 之前乱改主语义。

### Artifact/Test Agent

- `proof_artifacts/run_all_proofs.py`
- `ARTIFACT_MANIFEST.json`
- 测试运行。
- 最终交付包。

## 4. Stage 1：工具链与定理盘点

### 4.1 工具链探测

运行：

```powershell
cd /d D:\Codex\juris-calculus\源码
python --version
python -c "import z3; print('z3 ok')" 2>$null
where.exe lean
where.exe lake
where.exe java
```

记录到：

```text
D:\Codex\juris-calculus\20260611kimi\TOOLCHAIN_STATUS.md
```

如果 `z3` 不可用：

- 可尝试使用 `z3-solver`，但不得破坏项目依赖。
- 若无法安装，生成 `.smt2` 和 runner stub，状态 `PENDING_TOOLCHAIN`。

### 4.2 定理盘点

扫描：

```powershell
Get-ChildItem -Recurse -File -LiteralPath "D:\Codex\juris-calculus\源码\theory" -Filter "*.py"
Select-String -Path "D:\Codex\juris-calculus\源码\theory\*.py" -Pattern "THEOREM|PROVEN|VERIFIED|CONJECTURE|proof"
```

生成：

```text
D:\Codex\juris-calculus\20260611kimi\THEOREM_STATUS_MATRIX.md
```

矩阵列：

```text
| ID | Existing file | Original claim | New status | Artifact | Checker command | Allowed claim | Notes |
```

## 5. Stage 2：Proof Completion / Refutation

Proof artifacts 统一放在：

```text
D:\Codex\juris-calculus\20260611kimi\proof_artifacts
```

建议结构：

```text
proof_artifacts/
  run_all_proofs.py
  ARTIFACT_MANIFEST.json
  galois/
  horn/
  fixpoint/
  aaf/
  graph_similarity/
  banach/
  dp/
  statistics/
```

### 5.1 P0-A Galois / Reverse Index

不要沿用旧总命题：

```text
alpha(d) ⊆ {a} ⇔ d ∈ gamma(a)
```

该命题在 `alpha(d)` 可返回多个 atom 时有语义风险。应证明两个正确命题。

#### 5.1.1 Incidence theorem

```text
alpha_one(d) : set Atom
gamma_one(a) = { d | a ∈ alpha_one(d) }

∀ d a, a ∈ alpha_one(d) ⇔ d ∈ gamma_one(a)
```

#### 5.1.2 Powerset Galois connection

```text
Alpha(S) = ⋃ { alpha_one(d) | d ∈ S }
Gamma(B) = { d | alpha_one(d) ⊆ B }

Alpha(S) ⊆ B ⇔ S ⊆ Gamma(B)
```

Artifact：

```text
proof_artifacts/galois/finite_galois_adjunction.py
proof_artifacts/galois/FiniteGaloisAdjunction.lean
proof_artifacts/galois/README.md
```

要求：

- Lean 可用则无 sorry 检查。
- Lean 不可用则 Python 完整穷举小型 finite fixture，并对真实 `US_Adapter.yaml` 做 consistency check。
- 若真实数据规模太大，不得抽样冒充证明；抽样只能标 TESTED_PROPERTY。

### 5.2 P0-B Bounded Horn Correctness

证明目标：

```text
For finite strict Horn KB with no cycles or bounded zero-cycle condition,
operational forward chaining output equals denotational least closure.
```

Artifact：

```text
proof_artifacts/horn/bounded_horn_correctness.py
proof_artifacts/horn/horn_termination_measure.py
proof_artifacts/horn/README.md
```

要求：

- 定义 abstract denotational closure。
- 定义 operational closure。
- 穷举 finite atom universe、rule fixture family、all initial facts。
- assert equality。
- 明确条件：strict Horn、finite、acyclic/zero-cycle、no rebuttal/constraint/confidence zeroing。

### 5.3 P0-C Fixpoint Termination Boundary

拆成两个命题。

#### Pure Horn termination

```text
claims 单调增长，有限 universe，因此有限步停止。
```

Artifact：

```text
proof_artifacts/horn/horn_termination_measure.py
```

#### Production evaluator bounded operational termination

不得声称 Tarski global monotone fixpoint。

证明/验证：

```text
iteration_count <= max_iterations
rules_applied grows monotonically
exception visited set blocks recursion cycles
CriticalClarityFailure is absorbing
MAX_MODIFICATION_COUNT bounds rebuttal mutation
```

Artifact：

```text
proof_artifacts/fixpoint/production_bounded_termination.py
proof_artifacts/fixpoint/evaluator_termination_model.tla
proof_artifacts/fixpoint/README.md
```

如果 TLA+ 不可用：

- TLA 文件标 `PENDING_TOOLCHAIN`。
- Python bounded finite-state checker 必须能运行。

### 5.4 P0-D Dung AAF

证明目标：

```text
For finite AAF, grounded extension exists, is unique, deterministic, and finite iteration reaches fixpoint.
```

Artifact：

```text
proof_artifacts/aaf/dung_grounded_extension.py
proof_artifacts/aaf/stratified_correspondence.py
proof_artifacts/aaf/README.md
```

要求：

- 穷举所有 n<=4 或 n<=5 的 directed attack graphs。
- 验证 conflict-free、admissibility、fixpoint、determinism。
- 对 legal stratified fixture 验证 exception/rebuttal -> attack 后输出一致。
- 若 full correspondence 不成立，保存反例并给修正版。

### 5.5 P0-E Graph Similarity

证明：

```text
score = 0.6*jaccard + 0.4*size_ratio
size_ratio = 0.5*vertex_ratio + 0.5*edge_ratio
若 jaccard, vertex_ratio, edge_ratio ∈ [0,1]，则 score ∈ [0,1]
```

Artifact：

```text
proof_artifacts/graph_similarity/graph_similarity_range_z3.py
proof_artifacts/graph_similarity/graph_similarity_range.smt2
proof_artifacts/graph_similarity/metric_counterexamples.py
proof_artifacts/graph_similarity/README.md
```

必须反例化：

```text
strict reflexivity under conservative empty-feature policy
metric identity claim
```

若搜索到 triangle inequality 反例，一并保存。若没找到，不得称 metric，只说未证明且 identity 已失败。

### 5.6 P1-F Banach Pricing Limited Theorem

只证明窄命题：

```text
f(x) = βT + (1-β)x
0 < β <= 1
d(x,y)=|x-y|
d(f(x), f(y)) = |1-β| d(x,y)
```

Artifact：

```text
proof_artifacts/banach/banach_effective_nodes.py
proof_artifacts/banach/BanachEffectiveNodes.lean
proof_artifacts/banach/README.md
```

不得外推：

```text
full pricing vector contraction
location/stage/travel calibrated
legal reasonableness of fixed point
```

### 5.7 P1-G DP Mechanism

拆分：

#### Standard scalar Laplace

```text
M(D)=f(D)+Lap(Δ/ε) satisfies ε-DP under L1 sensitivity Δ.
```

Artifact：

```text
proof_artifacts/dp/laplace_scalar_mechanism.md
```

可引用标准 theorem，但必须明确 assumptions。

#### Ratio-preserving boundary

如果 ratios 是公开量或已发布量，deterministic scaling 是 post-processing。若 ratios 来自 private vector，则可能泄漏结构。

Artifact：

```text
proof_artifacts/dp/ratio_preserving_boundary.md
```

#### Floor clipping

当前形式：

```text
max(0.3*x0, x0 + Lap(...))
```

floor 依赖原始 `x0`，不能直接当作 released noisy value 的 post-processing。必须：

- 证明受限条件下仍满足 DP；或
- 给出风险/反例并降级。

Artifact：

```text
proof_artifacts/dp/dp_floor_clipping_analysis.py
```

### 5.8 P1-H Theil-Sen / Siegel

#### Clipped Theil-Sen refutation

证明当前 estimator 不是纯 Theil-Sen：

```text
it filters slopes and clamps output
```

Artifact：

```text
proof_artifacts/statistics/clipped_theilsen_refutation.py
```

用 crafted dataset 证明 pure median slope 与 clipped estimator 不同。

#### Siegel repeated median

定义：

```text
s_i = median_{j != i} (h_j - h_i)/(n_j - n_i)
s = median_i s_i
```

Artifact：

```text
proof_artifacts/statistics/siegel_repeated_median_verifier.py
```

验证实现与定义一致。不得无引用声称通用 50% breakdown proof。

## 6. Stage 3：状态矩阵和 Proof Ledger

输出：

```text
D:\Codex\juris-calculus\20260611kimi\THEOREM_STATUS_MATRIX.md
D:\Codex\juris-calculus\20260611kimi\PROOF_LEDGER.json
D:\Codex\juris-calculus\20260611kimi\FAILED_OR_REFUTED_THEOREMS.md
```

`PROOF_LEDGER.json` 示例：

```json
{
  "source_dir": "D:\\Codex\\juris-calculus\\源码",
  "delivery_dir": "D:\\Codex\\juris-calculus\\20260611kimi",
  "proof_artifacts_dir": "D:\\Codex\\juris-calculus\\20260611kimi\\proof_artifacts",
  "theorems": [
    {
      "id": "galois_powerset_finite",
      "statement": "Alpha(S) subset B iff S subset Gamma(B)",
      "status": "EXHAUSTIVE_FINITE_PROOF",
      "artifact": "proof_artifacts/galois/finite_galois_adjunction.py",
      "checker_command": "python proof_artifacts/galois/finite_galois_adjunction.py",
      "assumptions": ["finite description set", "finite atom set"],
      "limitations": ["not infinite-domain unless Lean artifact passes"]
    }
  ]
}
```

`FAILED_OR_REFUTED_THEOREMS.md` 每条包含：

```text
Original claim
Why it fails
Counterexample
Corrected theorem
Artifact path
Engineering implication
```

## 7. Stage 4：基于证明结果的工程完善

只做由证明/反例直接推出的工程闭环。

### 7.1 Evidence governance

新增/更新：

```text
源码/theory/STATUS.md
源码/theory/trust_label_schema.json
源码/theory/artifacts/README.md
源码/tools/theory_status_audit.py
```

目标：

- 所有 theorem 文件有状态。
- 没 artifact 的不许叫 PROVED。
- `theory/proven/` 目录名不再等于证明状态。

### 7.2 Counterexample registry

新增：

```text
源码/theory/engine_safety/counterexamples/
源码/tests/unit/test_counterexamples.py
```

至少纳入：

```text
CE-001 graph empty-feature strict reflexivity refuted
CE-002 clipped Theil-Sen robustness caveat
CE-003 evaluator non-monotonicity / bounded termination boundary
CE-004 DP floor clipping boundary if refuted/risky
```

### 7.3 Fixpoint / Dung engineering closure

如果 AAF proof 完成，新增 shadow mode，不替换主 evaluator：

```text
源码/compiler_core/argumentation.py
源码/compiler_core/stratified_evaluator.py
源码/tests/unit/test_argumentation_grounded_extension.py
源码/tests/unit/test_stratified_evaluator_shadow.py
```

规则：

- 现有 `FixpointEvaluator` 默认路径不替换。
- shadow evaluator 输出 diff。

### 7.4 Graph similarity closure

修改/新增：

```text
源码/legalos_services/legalos_pricing.py
源码/theory/engine_safety/graph_similarity_model.md
源码/tests/unit/test_graph_similarity_properties.py
```

要求：

- 保留旧 `compute_graph_similarity` wrapper。
- 新增或文档化 `ContextualOverlapScore`。
- 默认 empty feature policy 保守，不改成 1.0。
- 明确 not metric / not kernel。

### 7.5 Pricing closure

修改：

```text
源码/legalos_services/peripheral_models.py
源码/tests/unit/test_pricing_calibration.py
```

要求：

- `calibrate_theilsen` 保留兼容 wrapper。
- 新增/命名 `calibrate_clipped_pairwise_median`。
- 新增或验证 `calibrate_siegel_repeated_median`。
- 文档不再声称 clipped estimator 保留纯 Theil-Sen breakdown guarantee。

### 7.6 DP closure

新增：

```text
源码/theory/engine_safety/dp_privacy_boundary.md
源码/tests/unit/test_dp_mechanism_boundary.py
```

要求：

- 标准 Laplace theorem 与当前 ratio/floor 实现分开。
- epsilon <= 0 的 release 语义明确；ABSOLUTE privilege 应 block release，不是 epsilon=0.1 近似。

### 7.7 Parameter / metadata closure

新增：

```text
源码/configs/model_parameters.yaml
源码/tools/parameter_audit.py
```

可选但建议：

```text
源码/compiler_core/types.py
源码/compiler_core/evaluator.py
源码/compiler_core/batch_processor.py
源码/mcp_server.py
源码/tests/unit/test_claim_trust_metadata.py
```

目标：claim/MCP 输出携带 `epistemic_status`：

```json
{
  "trust_label": "EXHAUSTIVE_FINITE_PROOF",
  "rule_maturity": "L1_REVIEWED",
  "mathematical_basis": "bounded Horn finite-domain equivalence",
  "verification_artifacts": [],
  "known_limits": []
}
```

## 8. Stage 5：run_all_proofs.py

创建：

```text
D:\Codex\juris-calculus\20260611kimi\proof_artifacts\run_all_proofs.py
```

要求：

- 运行所有 Python proof artifacts。
- 尝试 Z3 scripts。
- 尝试 Lean files，如果 lean 可用。
- 工具链不可用时记录 `PENDING_TOOLCHAIN`，不要伪造 PASS。
- 已标 proved 的 artifact 失败时整体 fail。
- 生成：

```text
D:\Codex\juris-calculus\20260611kimi\proof_artifacts\proof_run_results.json
```

结果格式：

```json
{
  "artifacts": [
    {
      "id": "galois_powerset_finite",
      "status": "PASS",
      "proof_level": "EXHAUSTIVE_FINITE_PROOF",
      "command": "python galois/finite_galois_adjunction.py",
      "exit_code": 0
    }
  ],
  "summary": {
    "pass": 0,
    "fail": 0,
    "pending_toolchain": 0,
    "refuted": 0
  }
}
```

## 9. 最终交付文件

写入：

```text
D:\Codex\juris-calculus\20260611kimi
```

必须包含：

```text
FINAL_REPORT.md
THEOREM_STATUS_MATRIX.md
PROOF_LEDGER.json
FAILED_OR_REFUTED_THEOREMS.md
ENGINEERING_CLOSURE.md
TEST_RESULTS.md
TOOLCHAIN_STATUS.md
DELIVERY_MANIFEST.json
proof_artifacts\
proof_artifacts\ARTIFACT_MANIFEST.json
proof_artifacts\run_all_proofs.py
proof_artifacts\proof_run_results.json
```

`FINAL_REPORT.md` 必须按“先 proof、后工程完善”结构：

```text
1. Executive summary
2. Proofs completed
3. Theorems refuted
4. Theorems downgraded or pending
5. Engineering closures derived from proof results
6. Default semantics changed? yes/no
7. How to rerun proof artifacts
8. How to rerun source tests
```

`ENGINEERING_CLOSURE.md` 必须说明：

```text
Which code/docs/tests were changed because of which proof/refutation.
Which suggested engineering changes are intentionally left as future work.
Whether FixpointEvaluator default semantics changed.
Whether graph similarity default empty-feature policy changed.
Whether pricing default estimator changed.
```

`DELIVERY_MANIFEST.json` 示例：

```json
{
  "source_dir": "D:\\Codex\\juris-calculus\\源码",
  "experiment_data_dir": "D:\\同步网盘\\软件开发\\论文\\实验数据",
  "log_dir": "D:\\同步网盘\\软件开发\\日志",
  "delivery_dir": "D:\\Codex\\juris-calculus\\20260611kimi",
  "proof_artifacts_dir": "D:\\Codex\\juris-calculus\\20260611kimi\\proof_artifacts",
  "completed_proofs": [],
  "refuted_theorems": [],
  "engineering_closures": [],
  "test_commands": [],
  "changed_files": [],
  "log_files": [],
  "default_evaluator_replaced": false,
  "graph_similarity_default_policy": "conservative",
  "timestamp": ""
}
```

## 10. 最终验收命令

必须运行：

```powershell
cd /d D:\Codex\juris-calculus\20260611kimi\proof_artifacts
python run_all_proofs.py
```

尽量运行：

```powershell
cd /d D:\Codex\juris-calculus\源码
python -m unittest discover -s tests
```

可选：

```powershell
python -m pytest tests
```

结果写入：

```text
D:\Codex\juris-calculus\20260611kimi\TEST_RESULTS.md
D:\同步网盘\软件开发\日志\kimi_proof_then_closure_<timestamp>.md
```

## 11. 最终回答格式

Kimi 最终必须回答：

```text
1. Proof completion summary
2. Theorems proved and proof levels
3. Theorems refuted or downgraded
4. Theorems pending due to toolchain/data limits
5. Engineering closures completed
6. Source code default semantics changed? yes/no
7. run_all_proofs.py result summary
8. source tests result summary
9. log file path
10. delivery directory file list
```

## 12. 常见失败模式

避免：

- 先做一堆工程重构，最后没有 proof artifact。
- 为了增加 PASS 数，把命题偷偷改弱但不记录。
- 把 falsified theorem 留成“未来工作”而不给反例。
- 把空特征 graph similarity 默认改成 1.0。
- 直接替换主 evaluator。
- 把 `theory/proven` 当作已证明。
- Lean/TLA/Z3 不可用时假装已验证。
- 修改实验数据原始文件。

允许：

- 原命题为假时，用反例完成。
- 原命题过强时，降级为可证明修正版。
- 工具链不可用时，生成 artifact draft 并标 `PENDING_TOOLCHAIN`。
- 工程完善只覆盖 proof 结果暴露出的最小必要边界。
