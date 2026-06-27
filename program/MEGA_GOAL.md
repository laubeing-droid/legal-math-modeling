# MEGA GOAL — legal-math-modeling

## 项目总目标

构建一套经过形式化验证的法律推理数学模型，实现从法律事实到决策的可审计推理链。

## 当前状态

**FORMAL_CORE_RELEASED**

| 指标 | 数值 |
|------|------|
| Lean 唯一定理 | 94（43 core + 51 supporting） |
| sorry 数量 | 0 |
| `lake build JurisLean` jobs | 2954 |
| Lean 源文件 | 25 个 |
| Python 理论模块 | 59 个 |
| 规范类型 | 11 个 |

## Track 结构

### Track A: 发布真实性

- A0: test-count and clean-build audit — **完成**
- A1: formal-core release gate — **完成**
- A2: executable refinement baseline — 进行中

### Track B: Banach 完备空间（独立 worktree）

- B0: weighted metric completion
- B1: ContractingWith bridge
- B2: fixed-point and error bounds
- B3: BanachCertificate

### Track C: 证书与流水线

- C0: pipeline no-upgrade — 进行中
- C1: certificate soundness — 进行中
- C2: argument preservation
- C3: attack preservation
- C4: compile certificate integration

### Track D: 增量验证

- D0: provenance graph
- D1: safe rule-change impact
- D2: affected-region theorem
- D3: incremental equals full

### Track E: 最小支撑集

- E0: minimal support
- E1: minimal rebuttal
- E2: minimum-cost intervention
- E3: minimality certificate

## 执行规则

- 每个写 Track 使用独立 worktree
- 同一文件只允许一个 writer
- subagent 只承担只读审计、测试、API 搜索和互不冲突任务
- 禁止 sorry/admit/自定义 axiom/True theorem/削弱命题
- UNKNOWN/TIMEOUT/SKIP fail-closed
- 证书 checker 不得调用主求值器
- 增量验证失败必须 fallback 全量重算
- 不伪造数据、不自动发布、不 force push

## 失败策略

- 单项阻塞时保存最小复现、proof state 和日志
- 继续执行不依赖任务
- 不得以外围功能代偿核心门禁
- 不得重新修改已封板的有限单调/AAF/Horn theorem，除非出现真实反例或构建失败

## 合法最终状态

- NIGHT_RUN_COMPLETE
- NIGHT_RUN_PARTIAL
- FORMAL_CORE_RELEASED_BANACH_BLOCKED
- PRODUCTION_ASSURANCE_BLOCKED
- FAILED
