# juris-calculus 数学证明增强实验流程与记录方案

生成日期：2026-06-09  
状态：仅为实验设计，尚未执行实验  
目标项目：`D:\Codex\juris-calculus\源码`  
外援仓库目录：`D:\Codex\Git数学证明外援`  
建议交付目录：`D:\juris_calculus_verification_runs`

## 1. 实验目标

本实验不是为了“证明所有报告里的定理都是真的”，而是建立一条可重复、可审计、可逐步升级的数学证明增强流程。

核心目标分为四层：

1. 反例发现：用 Hypothesis、CrossHair、Alloy、TLA+ 快速找出伪定理、边界错误和状态机异常。
2. 不变量证明：用 Z3/pySMT 证明有限域、线性约束、范围约束、可满足性约束。
3. 状态机验证：用 TLA+ 建模 evaluator、rebuttal、oscillation guard、critical halt 等运行语义。
4. 机器检查数学证明：用 Lean 4/mathlib 承接 Galois connection、lattice/fixpoint、Banach contraction、category theory 等真正数学命题。

原则：先让每个 theorem 有可信度标签，再决定是否进入证明器。禁止把 print、单例测试、经验拟合包装成 proof。

## 2. 工具分层

| 层级 | 工具 | 本地目录 | 用途 |
| --- | --- | --- | --- |
| Python 性质测试 | Hypothesis | `D:\Codex\Git数学证明外援\hypothesis` | 批量生成输入，发现反例 |
| Python 符号执行 | CrossHair | `D:\Codex\Git数学证明外援\CrossHair` | 检查函数 contracts，找 counterexample |
| SMT 求解 | Z3 | `D:\Codex\Git数学证明外援\z3` | 证明范围、不变量、有限域命题 |
| SMT 抽象层 | pySMT | `D:\Codex\Git数学证明外援\pysmt` | 统一生成/导出 SMT-LIB |
| 状态机模型 | TLA+ / TLC | `D:\Codex\Git数学证明外援\tlaplus` | evaluator 状态机与 temporal invariant |
| 结构反例 | Alloy | `D:\Codex\Git数学证明外援\alloy` | 关系结构、互斥性、映射反例 |
| 证明语言 | Lean 4 | `D:\Codex\Git数学证明外援\lean4` | 机器检查数学证明 |
| 数学库 | mathlib4 | `D:\Codex\Git数学证明外援\mathlib4` | order theory、lattice、category、analysis |
| 可验证实现 | Dafny | `D:\Codex\Git数学证明外援\dafny` | 长期重写核心算法或证明 loop invariant |

## 3. 实验目录结构

建议创建：

```text
D:\juris_calculus_verification_runs\
  README.md
  manifest.yaml
  00_baseline\
    source_snapshot.txt
    git_status.txt
    file_hashes.json
    theorem_inventory.csv
  01_property_tests\
    tests\
    results\
    counterexamples\
  02_smt_z3\
    specs\
    smt2\
    results\
    unsat_cores\
  03_crosshair\
    contracts\
    results\
    counterexamples\
  04_tla\
    specs\
    configs\
    traces\
    results\
  05_alloy\
    models\
    instances\
    results\
  06_lean\
    JurisCalculus\
    build_logs\
    proof_status\
  07_report\
    daily_log.md
    final_summary.md
    theorem_status_matrix.csv
```

每次实验必须有独立 run id：

```text
RUN_ID = YYYYMMDD-HHMMSS-tool-topic
示例：20260609-213000-z3-galois-reverse-index
```

## 4. 命题可信度标签

每个 theorem 或 claim 先打标签，再决定实验路线。

| 标签 | 含义 | 允许进入报告的措辞 |
| --- | --- | --- |
| `CODE_FACT` | 直接从源码读出的事实 | “源码实现为...” |
| `TESTED_PROPERTY` | 已通过性质测试但非证明 | “在生成样本下未发现反例...” |
| `SMT_PROVED_FINITE` | 有限域或约束域内由 SMT 证明 | “在给定抽象域内已证明...” |
| `MODEL_CHECKED` | TLA+/Alloy 有界模型检查通过 | “在模型边界内未发现违反...” |
| `LEAN_PROVED` | Lean 机器检查通过 | “已形式化证明...” |
| `EMPIRICAL_HYPOTHESIS` | 经验拟合或统计观察 | “经验假设...” |
| `CONJECTURE` | 尚无证明 | “猜想...” |
| `REFUTED` | 找到反例或源码不支持 | “不成立...” |

禁止使用：

```text
print 输出 => proof
单个例子 => universal theorem
经验阈值 => mathematical constant
模型草图 => machine-checked proof
```

## 5. 总体实验流程

### Phase 0：冻结基线

目的：保证后续任何实验都能追溯到具体源码版本。

记录：

1. `git status --short`
2. `git rev-parse HEAD`，若 `源码/` 不是 Git tracked，也记录目录 hash。
3. 关键文件 SHA256：
   - `compiler_core/evaluator.py`
   - `compiler_core/constraint_validator.py`
   - `legalos_services/legalos_pricing.py`
   - `legalos_services/differential_privacy.py`
   - `extractors/zh_CN/semantic_fact_matcher.py`
   - `theory/*.py`
4. Python 版本、pip freeze、外援仓库 HEAD。

输出：

```text
00_baseline/source_snapshot.txt
00_baseline/file_hashes.json
00_baseline/tool_versions.json
```

### Phase 1：定理盘点与分流

目的：把报告中的 theorem 拆成可执行任务。

输入：

1. `D:\juris_calculus_math_reverse_engineering.md`
2. `D:\juris_calculus_math_reverse_engineering_audit.md`
3. `D:\juris_calculus_20_proof_audit_report.md`
4. `D:\juris_calculus_handoff_codex_response.md`

输出表字段：

```csv
id,file,claim,source_location,current_evidence,target_tool,expected_artifact,trust_label,status,notes
```

示例：

```csv
T01,galois_reverse_index.py,"alpha/gamma form Galois connection",theory file,finite Python check,Z3+Lean,smt proof + lean theorem,SMT_PROVED_FINITE,pending,
T17,banach_pricing_contraction.py,"pricing is Banach contraction",theory file,suspect constant,Z3+Hypothesis,counterexample search,CONJECTURE,pending,
```

### Phase 2：Hypothesis 性质测试

优先目标：

1. `compute_formalizable()`：
   - 输出在 `[0,1]`
   - 对 coverage 单调
   - Non-Horn smoothing 不产生硬断层
2. `compute_graph_similarity()`：
   - 输出在 `[0,1]`
   - 对称性
   - 自反性边界
   - 三角不等式反例搜索
3. `RatioPreservingDP`：
   - 输出非负
   - `dp_diagnostics` 字段完整
   - rounding 后 ratio error 是否低于声明阈值
4. `FixpointEvaluator`：
   - 有限随机规则集下不超过 `max_iterations`
   - mutual exception 不导致递归溢出

每个性质测试必须记录：

```yaml
property_id:
  function:
  invariant:
  input_strategy:
  max_examples:
  seed:
  result: pass|fail|error
  counterexample_path:
  runtime_seconds:
```

失败时保存最小反例：

```json
{
  "property_id": "PBT-GRAPH-TRIANGLE",
  "input": {},
  "expected": "triangle inequality holds",
  "actual": "violated",
  "shrunk_by": "hypothesis",
  "source_file": "",
  "reproduce_command": ""
}
```

### Phase 3：Z3 / pySMT 不变量证明

优先目标：

1. Galois reverse index：
   - 有限 domain 上验证 `alpha(d) <= a iff d <= gamma(a)`。
   - 明确 vacuous branch 是否只是空真，还是遗漏反向证明。
2. Scoring bounds：
   - `compute_formalizable()` 抽象表达式在输入域内是否总在 `[0,1]`。
3. Graph similarity：
   - 证明范围 `[0,1]`。
   - 自动生成非 metric 反例。
4. Constraint guard：
   - 超过 `MAX_MODIFICATION_COUNT` 后 `triggered=False`。
5. Horn bounded evaluator：
   - 小规模 finite KB 中 Python evaluator 与抽象 Horn semantics 等价。

记录格式：

```yaml
smt_case_id:
  theorem_id:
  solver: z3|pysmt-z3
  logic: QF_LIA|QF_LRA|AUFLIA|custom
  assumptions:
  query:
  result: sat|unsat|unknown
  model_path:
  unsat_core_path:
  smt2_path:
  runtime_seconds:
  interpretation:
```

规则：

1. `unsat` 证明“不存在反例”时，必须保存 SMT-LIB。
2. `sat` 时必须保存 model 作为反例。
3. `unknown` 不得写成 PASS。

### Phase 4：CrossHair contracts

适用对象：纯函数或接近纯函数的 Python 逻辑。

优先函数：

1. `_smooth_sigmoid_cap`
2. `compute_formalizable`
3. `LegalOSPricingEngine.compute_graph_similarity`
4. `RatioPreservingDP.anonymize_amounts`

记录：

```yaml
crosshair_case_id:
  function:
  contract_style: pep316|asserts|icontract
  preconditions:
  postconditions:
  result: confirmed|refuted|unknown|analysis_error
  counterexample:
  limitations:
```

注意：CrossHair 会执行 Python 代码，只允许用于无 IO、无网络、无文件删除、无真实业务副作用的函数。

### Phase 5：TLA+ 状态机模型

优先模型：

1. Fixpoint evaluator loop
2. Exception recursion visited set
3. ConstraintValidator oscillation guard
4. CriticalClarityFailure absorbing halt

核心变量：

```text
facts
claims
rulesApplied
iteration
rebuttalCount
halted
visited
```

候选不变量：

```text
iteration <= MaxIterations
rulesApplied \subseteq Rules
halted => UNCHANGED claims
rebuttalCount[c] > 3 => no further modification for c
visited prevents exception recursion cycles
```

记录：

```yaml
tla_case_id:
  spec:
  config:
  constants:
  invariants:
  temporal_properties:
  result: passed|failed|error
  trace_path:
  state_count:
  diameter:
  runtime_seconds:
```

失败 trace 必须转写为 Python 单测或 Hypothesis regression seed。

### Phase 6：Alloy 结构反例

适用：

1. `R_supersedes` 与 `R_corrects` 互斥。
2. counts-as institutional facts 映射。
3. CN 到 US 的自然变换不存在。
4. Policy 层 stratifiable CTRS 结构边界。

记录：

```yaml
alloy_case_id:
  model:
  command:
  scope:
  result: instance|no_instance|error
  instance_path:
  interpretation:
```

原则：

1. Alloy 的 `no instance` 只是给定 scope 内无反例，不是无限域证明。
2. 找到 instance 时优先作为审计报告的致命反例。

### Phase 7：Lean 4 / mathlib 机器证明

只挑真正数学定理进入 Lean。

第一批候选：

1. Galois connection skeleton：
   - 定义 finite preorder。
   - 定义 `alpha`、`gamma`。
   - 证明 adjunction。
2. Abstract interpretation：
   - lattice、monotone function、least fixpoint 的抽象定理。
   - 不直接声称 18 个源码 theorem 全部推出。
3. Banach contraction：
   - 定义 metric space 上 contraction。
   - 对 pricing map 证明或找出无法证明的条件。
4. Graph similarity：
   - 证明 symmetry。
   - 给出 triangle inequality 反例，不称 metric。

Lean 记录：

```yaml
lean_case_id:
  theorem:
  file:
  imports:
  proof_status: proved|sorry|failed|not_started
  axiom_count:
  sorry_count:
  build_command:
  build_log:
  notes:
```

合格标准：

```text
lake build 成功
无 sorry
无非预期 axiom
#print axioms 检查通过
```

### Phase 8：Dafny 可验证实现探索

Dafny 不作为第一阶段主线。仅在以下情况启用：

1. Python 函数太复杂，SMT/CrossHair 难以稳定证明。
2. 需要 loop invariant 和 termination proof。
3. 准备把某个核心算法重写成可验证伪实现。

候选：

1. bounded Horn evaluator。
2. graph similarity。
3. scoring function。

记录：

```yaml
dafny_case_id:
  source_python:
  dafny_model:
  ensures:
  invariants:
  decreases:
  verification_result:
  compile_target:
```

## 6. 实验执行顺序

建议顺序：

1. Phase 0：冻结基线。
2. Phase 1：生成 theorem inventory。
3. Phase 2：跑 Hypothesis，快速找反例。
4. Phase 3：对无反例的性质写 Z3/pySMT。
5. Phase 4：给纯函数补 CrossHair contracts。
6. Phase 5：对 evaluator 状态机写 TLA+。
7. Phase 6：对关系结构写 Alloy。
8. Phase 7：只把稳定、抽象、数学性强的命题送入 Lean。
9. Phase 8：必要时用 Dafny 重写小核心。

每一阶段都必须产生：

```text
输入清单
命令清单
输出 artifact
结论标签
反例或证明路径
下一步动作
```

## 7. 通过/失败判定

### PASS

满足任一：

1. Lean 无 sorry 证明通过。
2. SMT 查询返回 `unsat`，且反例编码正确、SMT-LIB 已保存。
3. TLA+/Alloy 在声明 scope 内通过，报告明确 scope。
4. Hypothesis/CrossHair 未发现反例，但只能标为 `TESTED_PROPERTY` 或 `unknown-safe`，不得升级为完全 proof。

### FAIL

满足任一：

1. 找到 counterexample。
2. 源码行为与 theorem statement 不一致。
3. proof artifact 只有 print/docstring。
4. solver 返回 `unknown` 却被报告写成 proved。
5. Lean 使用 `sorry`、未声明 axiom 或绕过证明。

### CONDITIONAL

满足任一：

1. 只在有限 scope 内检查。
2. theorem 依赖额外前提，但报告原文未声明。
3. 证明的是抽象模型，不是源码实现。
4. 工具链暂缺运行时，无法复现。

## 8. 记录文件模板

### manifest.yaml

```yaml
project: juris-calculus
run_root: D:\juris_calculus_verification_runs
source_root: D:\Codex\juris-calculus\源码
external_tools_root: D:\Codex\Git数学证明外援
created_at: 2026-06-09
status: planned
experiments_executed: false
operator: Codex
```

### theorem_status_matrix.csv

```csv
theorem_id,source_file,claim,tool,status,trust_label,artifact_path,counterexample_path,notes
T01,galois_reverse_index.py,alpha-gamma Galois connection,Z3,pending,CONJECTURE,,,
T02,bounded_horn_correctness.py,k<=3 evaluator equivalence,Hypothesis+Z3,pending,CONJECTURE,,,
```

### experiment_result.json

```json
{
  "run_id": "",
  "theorem_id": "",
  "tool": "",
  "command": "",
  "started_at": "",
  "finished_at": "",
  "exit_code": null,
  "result": "not_run",
  "trust_label_before": "CONJECTURE",
  "trust_label_after": null,
  "artifacts": [],
  "counterexamples": [],
  "limitations": []
}
```

### counterexample.json

```json
{
  "counterexample_id": "",
  "theorem_id": "",
  "found_by": "",
  "input": {},
  "observed": {},
  "expected": "",
  "reproduce_command": "",
  "source_location": "",
  "minimal": false
}
```

### daily_log.md

```markdown
# Daily Log

## YYYY-MM-DD

### Planned

### Executed

### New Counterexamples

### Proofs Promoted

### Blockers

### Next Actions
```

## 9. 第一批建议实验任务

| 优先级 | theorem/file | 工具 | 目标 |
| --- | --- | --- | --- |
| P0 | `legalos_pricing.compute_graph_similarity` | Hypothesis + Z3 | 证明范围与对称性，生成非 metric 反例 |
| P0 | `evaluator.compute_formalizable` | Hypothesis + CrossHair | 检查范围、单调性、Non-Horn 平滑边界 |
| P0 | `constraint_validator` guard | TLA+ + Python regression | 证明超限不继续修改 |
| P0 | `galois_reverse_index.py` | Z3 + Lean | 区分 vacuous truth 与真正双向伴随 |
| P1 | `bounded_horn_correctness.py` | Hypothesis + Z3 | 穷举小规模 KB，而不是单例测试 |
| P1 | `banach_pricing_contraction.py` | Hypothesis + Z3 + Lean | 找 contraction factor 是否实际为 1 的反例 |
| P1 | `differential_privacy.py` | Hypothesis + SMT sketch | 检查 ratio/floor/rounding，并降级 DP theorem |
| P2 | `abstract_interpretation_unified.py` | Lean | 只证明抽象解释骨架，不证明 18 个 theorem 自动推出 |

## 10. 审计交付标准

每轮实验结束后输出一份报告：

```text
D:\juris_calculus_verification_runs\07_report\final_summary.md
```

报告必须包含：

1. 本轮实际跑了哪些实验。
2. 哪些 theorem 被提升可信度。
3. 哪些 theorem 被降级或反驳。
4. 所有 counterexample 的复现命令。
5. 所有 proof artifact 的路径。
6. 工具链缺失或无法复现项。
7. 下一轮修复建议。

## 11. 当前注意事项

1. 本文件只是实验设计；尚未执行任何证明实验。
2. Python 验证链可优先启动；Lean/TLA+/Alloy/Dafny 需确认运行时依赖。
3. 对 `D:\Codex\juris-calculus` 当前 Git 状态要谨慎：此前观察到根目录存在大量 deleted 项，而 `源码/` 可能是未跟踪目录。实验前必须冻结目录 hash。
4. 不要把 Hypothesis/CrossHair 的“未发现反例”写成数学证明。
5. 不要把 Alloy/TLA+ 有界检查写成无限域证明。
6. 不要在 Lean 中保留 `sorry` 后声称已证明。

## 12. 建议审批点

请先审以下决策：

1. 是否采用 `D:\juris_calculus_verification_runs` 作为统一实验输出目录。
2. 是否同意先跑 P0 四项：graph similarity、formalizable score、constraint guard、Galois connection。
3. 是否允许为 Python 侧补测试依赖：`pytest`、`hypothesis`、`z3-solver`、`crosshair-tool`。
4. Lean/TLA+/Alloy/Dafny 是否只做模型与脚手架，等运行时补齐后再执行。

## 13. 外部审计意见整合

收到的外部审计意见整体认可本计划的分层渐进路线，特别肯定了四点：

1. 从反例发现到机器证明的分层目标符合形式化验证工程落地规律。
2. 工具链与项目形态匹配，Python 源码验证优先，Lean/TLA+/Alloy/Dafny 承接更高层验证。
3. 基线冻结、模板化记录、run id 和 artifact 路径能满足可追溯审计。
4. 可信度标签可以有效防止 “print 输出即 proof”“单例测试即 universal theorem” 等虚假证明。

外部审计同时指出五类风险：

| 风险 | 影响 | 本计划修订 |
| --- | --- | --- |
| 依赖缺失 | TLA+/Alloy/Lean/Dafny 不能完整执行 | 增加依赖补齐计划与 `03_check_dependencies.ps1` |
| 执行门槛高 | 工具使用错误可能导致结论失真 | 增加各工具极简模板 |
| 基线冻结不足 | 未跟踪目录变动难以复现 | 增加目录 snapshot 脚本与 SHA256 |
| Lean 落地风险 | 证明进度可能慢，定理表述可能不规范 | 先做 Lean proof skeleton，再逐步去除 `sorry` |
| 记录不规范 | 审计链断裂 | 增加记录完整性校验脚本 |

## 14. 依赖补齐计划

| 缺失依赖 | 目标版本/建议 | 影响工具 | 优先级 | 验证命令 |
| --- | --- | --- | --- | --- |
| Java | OpenJDK 17 或 21 | TLA+、Alloy | P1 | `java -version` |
| Maven | 3.9+ | TLA+ 源码构建 | P1 | `mvn -version` |
| Gradle | 8.x | Alloy 源码构建 | P1 | `gradle -version` |
| Lean/Lake | 通过 elan 安装稳定版 Lean 4 | Lean/mathlib4 | P1 | `lean --version`; `lake --version` |
| .NET SDK | .NET 8 SDK | Dafny 源码构建 | P2 | `dotnet --list-sdks` |
| MSVC Build Tools | C++ Build Tools | CrossHair 本地 editable build | P3 | `cl` 或 VS Build Tools 检测 |

执行策略：

1. 短期只依赖已 ready 的 Python 验证链，不阻塞 P0 任务。
2. Java/Lean 作为第一批补齐对象，因为它们分别解锁 TLA+/Alloy 和 Lean/mathlib。
3. .NET SDK 与 MSVC Build Tools 放在第二阶段；Dafny 和 CrossHair 源码开发暂不作为短期关键路径。

## 15. 极简操作模板要求

为降低执行门槛，每个工具链必须先有最小模板，再进入正式实验。

应准备：

```text
01_property_tests\tests\test_graph_similarity_template.py
02_smt_z3\specs\galois_connection_smt_template.py
03_crosshair\contracts\graph_similarity_contract_template.py
04_tla\specs\EvaluatorSkeleton.tla
04_tla\configs\EvaluatorSkeleton.cfg
05_alloy\models\RelationsSkeleton.als
06_lean\JurisCalculus\GaloisConnectionSkeleton.lean
```

模板必须满足：

1. 不直接修改源码。
2. 默认不运行正式实验，只展示结构。
3. 包含记录字段提示：theorem_id、command、artifact_path、trust_label_before/after。
4. 如果模板中含未完成证明，必须明确标注 `skeleton_only` 或 `sorry_not_proof`。

## 16. 基线冻结增强

若 `源码/` 不是 Git tracked 状态，仅记录部分关键文件 hash 不足以复现完整目录。

新增要求：

1. 每轮实验前生成源码目录文件清单。
2. 每轮实验前生成源码目录压缩包或至少生成全量文件 hash manifest。
3. snapshot artifact 必须记录到 `experiment_result.json` 的 `artifacts` 字段。

建议输出：

```text
00_baseline\source_tree_manifest.csv
00_baseline\source_tree_hashes.json
00_baseline\source_snapshot.zip
00_baseline\source_snapshot.sha256
```

如果用户批准，也可为 `源码/` 单独初始化实验用 Git baseline。但在当前共享工作区中，不应擅自 `git init/add/commit`。

## 17. 交叉检查制度

每个 Phase 完成后，必须做一次交叉检查：

```text
Phase executor: 运行实验并填写记录
Reviewer: 独立读取 artifact，复现至少一个关键命令
Decision: PASS / NEEDS_FIX / INVALID
```

检查项：

1. `experiment_result.json` 字段是否完整。
2. 命令是否可复现。
3. PASS 是否有 proof artifact 或明确 scope。
4. FAIL 是否有 counterexample 和 reproduce command。
5. Hypothesis/CrossHair 结果是否被错误升级为 proof。
6. Lean 是否存在 `sorry` 或未声明 axiom。

## 18. 记录完整性自动校验

新增脚本要求：

```text
scripts\05_validate_records.ps1
```

校验目标：

1. 每个 run 目录必须有 `experiment_result.json`。
2. `run_id`、`tool`、`command`、`result` 不得为空。
3. 若 `result=pass`，必须有 artifact。
4. 若 `result=fail` 或 `refuted`，必须有 counterexample 或说明。
5. 若 `trust_label_after=LEAN_PROVED`，必须有 Lean build log，并检查无 `sorry`。
6. 若 `trust_label_after=SMT_PROVED_FINITE`，必须有 `.smt2` 或 solver transcript。

## 19. 时间线建议

| 时间 | 目标 | 产出 |
| --- | --- | --- |
| 第 1-2 周 | Python P0 验证链 + Java/Lean 依赖补齐 | graph/formalizable/guard/DP 初步结果，依赖状态报告 |
| 第 2-4 周 | TLA+/Alloy 模型检查 | evaluator 状态机、关系结构反例/通过记录 |
| 第 4 周以后 | Lean/Dafny 深水区 | Galois skeleton 到无 sorry 证明，Dafny 小核心探索 |

优先级保持：先反例发现，再有限域证明，再模型检查，最后机器数学证明。

## 20. 算法与源码改进闭环

外部实验不能只记录“怎么跑”，还必须记录“发现问题后如何改进算法、如何改源码、如何证明改动有效”。因此新增一个 ARV 闭环：

```text
Audit Finding -> Algorithm Diagnosis -> Repair Proposal -> Source Patch -> Regression/Proof -> Promotion/Demotion
```

### 20.1 算法改进记录

算法改进面向数学模型、评分函数、语义定义和证明前提，不一定立即改源码。

记录位置：

```text
07_report\algorithm_improvement_log.md
07_report\algorithm_improvement_backlog.csv
```

每条记录必须回答：

1. 原算法声称什么性质。
2. 实验或审计发现了什么问题。
3. 问题属于数学错误、边界漏洞、经验参数、证明前提缺失，还是实现偏差。
4. 建议的算法替代方案是什么。
5. 替代方案需要哪些新不变量或证明义务。
6. 是否会改变对外 API 或历史结果。

算法改进分类：

| 类型 | 示例 | 记录要求 |
| --- | --- | --- |
| `THEOREM_DOWNGRADE` | Banach contraction 降级为 empirical heuristic | 必须说明原 theorem 不成立的原因 |
| `MODEL_REFORMULATION` | DP tuple-level privacy 重新定义 adjacency | 必须列出新数学前提 |
| `SCORING_SMOOTHING` | Non-Horn hard cap 改 sigmoid shoulder | 必须记录连续性、单调性、范围 |
| `SIMILARITY_REDEFINITION` | graph similarity 加入 edge ratio | 必须记录 symmetry/range/non-metric |
| `PARAMETER_EXTERNALIZATION` | threshold/weights 下沉到 adapter | 必须记录默认值和校准方式 |
| `PROOF_OBLIGATION_ADDED` | Galois 双向伴随补充反向证明 | 必须记录目标工具与 artifact |

### 20.2 源码改进记录

源码改进面向具体 patch。任何源码修改都必须先有 patch proposal，再有验证结果。

记录位置：

```text
07_report\source_change_proposals\
07_report\source_change_log.md
07_report\repair_validation_matrix.csv
```

每个 patch proposal 使用固定模板：

```yaml
change_id:
theorem_or_finding_id:
target_files:
change_type: bugfix|refactor|algorithm_change|instrumentation|test_only|docs
problem:
algorithm_rationale:
source_rationale:
expected_behavior_before:
expected_behavior_after:
compatibility_risk:
proof_obligations:
tests_required:
rollback_plan:
status: proposed|implemented|validated|rejected
```

### 20.3 修复验证矩阵

每个源码改动都必须映射到验证项：

```csv
change_id,target_file,claim_fixed,validation_tool,validation_artifact,result,trust_label_after,residual_risk
```

示例：

```csv
SRC-0001,legalos_services/legalos_pricing.py,empty feature similarity no longer defaults to 0.5,Hypothesis+Z3,,pending,CONJECTURE,
SRC-0002,compiler_core/evaluator.py,Non-Horn cap is continuous at 0.4,Hypothesis+CrossHair,,pending,TESTED_PROPERTY,
```

### 20.4 改进报告必须分算法和源码

最终报告不得只说“测试通过”。必须分两节：

```text
Algorithm Improvements
- 数学模型层面的改动
- 定理降级/重述
- 新增证明义务

Source Code Improvements
- 具体文件和函数
- patch 摘要
- 回归测试和证明 artifact
- 兼容性风险
```

### 20.5 禁止事项

1. 不能把源码 patch 当成数学证明。
2. 不能把算法设想写成已实现。
3. 不能把通过测试写成 theorem 已证。
4. 不能只记录最终 diff，不记录为什么改。
5. 不能只记录算法建议，不说明落到哪些源码文件。
