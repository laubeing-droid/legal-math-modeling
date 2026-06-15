# juris-calculus 数学证明逻辑总审计任务

请你审计 juris-calculus 当前数学证明逻辑，重点不是看代码能不能跑，而是判断“哪些数学定理真的被证明了，哪些只是测试、模型草图、经验假设或反例已推翻”。

## 背景

项目目录：

```text
D:\Codex\juris-calculus\源码
```

实验记录目录：

```text
D:\juris_calculus_verification_runs
```

最新实验总报告：

```text
D:\juris_calculus_full_verification_run_report.md
```

最新 run 目录：

```text
D:\juris_calculus_verification_runs\07_report\runs\20260609-214205-full-suite-all-verification
```

已完成的验证工具链包括：

- Python / Hypothesis
- Z3
- CrossHair
- TLA+
- Alloy
- Lean
- Dafny

## 已知实验结果摘要

1. Python/Hypothesis 性质测试通过：6 passed。
2. Z3 证明 graph similarity 抽象范围不越界：
   - `sim < 0`：unsat
   - `sim > 1`：unsat
3. finite Galois sanity check：0 violations。
4. CrossHair 对 graph similarity contract 返回 `Not confirmed`，不能算证明。
5. TLA+ oscillation guard skeleton：No error found。
6. Alloy relation disjoint skeleton：UNSAT。
7. Lean Galois skeleton：编译通过，但只是 identity skeleton，不是完整 juris-calculus 定理。
8. Dafny graph range model：1 verified, 0 errors。
9. 项目 unit tests：32 passed。
10. 项目 full pytest 因 `configs/en_US/rules.yaml` 缺失而 collection 失败，此问题暂不处理。

## 关键反例

`compute_graph_similarity()` 的严格自反性被反例推翻：

```text
G = (v=1, e=0, features=empty set)
sim(G, G) = 0.4
```

因此不能全局声称：

```text
sim(G, G) = 1
```

请重点分析：这是实现 bug，还是空特征保守语义导致的定理降级？

## 审计目标

请你对整个数学证明逻辑做一次分级审计。

请不要只说“通过”或“不通过”，而是给每个定理/证明声称打标签：

| 标签 | 含义 |
| --- | --- |
| `CODE_FACT` | 只是源码事实 |
| `TESTED_PROPERTY` | 测试通过，但不是证明 |
| `SMT_PROVED_FINITE` | 有限域或抽象域 SMT 证明 |
| `MODEL_CHECKED` | TLA+/Alloy 有界模型检查 |
| `LEAN_PROVED_SKELETON` | Lean 骨架通过，但不是完整证明 |
| `LEAN_PROVED` | Lean 无 sorry 完整证明 |
| `EMPIRICAL_HYPOTHESIS` | 经验假设 |
| `CONJECTURE` | 尚未证明 |
| `REFUTED` | 已有反例 |
| `INCONCLUSIVE` | 工具无法确认 |

## 请重点审计以下数学逻辑

### 1. Galois connection

检查：

- 当前 finite sanity check 是否足够？
- Lean identity skeleton 是否过弱？
- 真正的 alpha/gamma 伴随还缺哪些定义？
- 是否存在 vacuous truth 掩盖反向证明的问题？

### 2. Fixpoint / 收敛性

检查：

- evaluator 的收敛性是否能直接套 Tarski？
- `rules_applied`、`max_iterations`、exception recursion、critical halt 是否改变了单调性？
- TLA+ skeleton 是否只证明了 guard 小模型，而非完整 evaluator？

### 3. Graph similarity

检查：

- `[0,1]` 范围是否已被充分证明？
- 对称性是否只是测试还是可证明？
- 严格自反性是否应降级？
- 是否还能称 metric？
- 当前反例如何影响数学报告？

### 4. Non-Horn formalizable score

检查：

- sigmoid smoothing 是否改善了硬截断？
- 目前只是测试通过，还是有数学证明？
- 权重 `(0.2,0.2,0.4,0.2)` 是否仍是经验参数？

### 5. DP ratio-preserving mechanism

检查：

- `dp_diagnostics` 只是审计 instrumentation，不等于 DP 证明。
- 当前机制能否声称 tuple-level differential privacy？
- adjacency、sensitivity、floor clipping、rounding 是否都需要重述？

### 6. Constraint / oscillation guard

检查：

- TLA+ skeleton 证明的是什么？
- 是否足以说明真实 `ConstraintValidator` 一定不会振荡？
- 还缺哪些状态变量？

### 7. Category / Banach / abstract interpretation 等高阶定理

检查：

- 哪些只是数学比喻？
- 哪些能进入 Lean？
- 哪些应该降级为 conjecture？
- Banach contraction 是否可能被反例推翻？

### 8. Core Inference Safety Boundary

请专门从“法律推理机器会不会乱跑”的角度审计核心推理安全边界。

重点检查：

- fixpoint 是否必然终止？
- rule firing 哪些部分是单调的，哪些不是？
- exception recursion 是否有 visited/depth 保护？
- confidence/formalizable_score 是否永远在 `[0,1]`？
- graph similarity 哪些性质成立，哪些已被反例推翻？
- DP 机制到底保护 principal、tuple，还是只提供审计 instrumentation？

请输出一张表：

| 安全边界 | 当前证据 | 风险 | 推荐标签 | 下一步证明方式 |
| --- | --- | --- | --- | --- |

### 9. Practical Legal Application Interface

请从“未来接真实案卷时如何诚实输出”的角度审计实务接口。

重点检查：

- 哪些规则可以标为已证明？
- 哪些只是可测试性质？
- 哪些是经验参数？
- 哪些需要真实案例校准？
- 哪些命题已被反例推翻？
- 系统输出法律结论时应如何附带 trust label？
- 是否需要 rule maturity 分级？
- 当前 `US_Adapter.yaml` 是否只能视为术语层，而不是规则层？

请输出一张表：

| 输出对象 | 当前成熟度 | 推荐 trust label | 是否需要人工复核 | 原因 |
| --- | --- | --- | --- | --- |

## 输出格式

请按以下格式输出：

```markdown
# juris-calculus 数学证明逻辑审计报告

## 1. 总体结论

## 2. 可信度标签总表

| 定理/模块 | 当前证据 | 推荐标签 | 是否可称 proof | 原因 |
| --- | --- | --- | --- | --- |

## 3. 已被证明或部分证明的内容

## 4. 已被反例推翻的内容

## 5. 只是测试通过但不能称证明的内容

## 6. 只是 proof skeleton 的内容

## 7. 仍是 conjecture / empirical hypothesis 的内容

## 8. 对数学模型的修正建议

## 9. 对源码实现的修正建议

## 10. 对未来 Lean/Z3/TLA+ 证明路线的建议

## 11. 核心推理安全边界审计

## 12. 未来实务应用接口审计

## 13. 最终评级
```

## 审计原则

1. 不要把 print/docstring 当 proof。
2. 不要把单例测试当 universal theorem。
3. 不要把 Hypothesis 通过当数学证明。
4. 不要把 Lean skeleton 当完整 Lean proof。
5. 不要把 Alloy/TLA+ 有界检查当无限域证明。
6. 找到反例时，必须明确降级或反驳原命题。
7. 如果一个命题只有工程直觉，没有 proof artifact，请标记为 `CONJECTURE` 或 `EMPIRICAL_HYPOTHESIS`。
8. 如果一个结论只在抽象模型成立，请明确写出模型边界。
