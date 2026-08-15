# legal-math-modeling 理论成果全量吸收施工方案

日期：2026-08-15  
适用基线：`main@f521b5b9f61bd947a004e6d39a1bac71f8df9e2f`  
方案性质：本仓独立施工规范；不代表代码、证明或构建已经完成  
理论输入：已冻结，只工程化既有成果，不重启理论研究

## 0. 结论

LMM 定位：整套系统的形式语义、数学模型、编译正确性义务、反例、独立 checker 和 proof-release authority。它不是法律检索器、案件工作流或生产运行时。

本方案废止旧方案中“五项完成即停”“时态/数值只在消费者触发后施工”“仅补任务有界薄层”的 scope 限制。新目标是把冻结理论 P01—P09 对形式层提出的全部要求建成完整先进底座：

```text
source-bound legal contracts
  -> LegalSpec typed semantics
  -> Legal-IVL formal core
  -> Horn / DDL / Argumentation / Temporal / Exact Numeric
  -> ASP / SMT proof obligations and checkable witnesses
  -> verified lowering contracts
  -> independent runtime refinement
  -> commit-bound formal release
```

既有窄实验、反例和负结果继续作为验证资产，但不得被解释为否决双 IR、多后端或完整形式架构。所有施工波次都是交付范围；Gate 只控制依赖、正确性和发布状态，不是提前收工点。

## 1. 当前基线

### 1.1 Git 与源码事实

- 当前分支基线：`main`
- 当前提交：`f521b5b9f61bd947a004e6d39a1bac71f8df9e2f`
- tree：`9ff1d16a34831951f679aa1e2bb0407185208cd4`
- upstream：`origin/main`
- 当前 main 领先 upstream 1 个提交
- 当前工作树在建方案前 clean
- Lean/Mathlib 锁定：Lean 4.30.0 / Mathlib4 v4.30.0
- 静态清点：32 个 `.lean` 文件、126 个 `theorem` 声明
- 静态禁词扫描：未发现 `sorry`、`admit`、自定义 `axiom` 或 `theorem ... : True`

静态数量和禁词扫描不等于 current-head Lean build、axiom audit 或形式发布证书。本方案编写时没有取得新的 `lake build` 证据。

### 1.2 当前红灯

HEAD `f521b5b` 新增了以下 acceptance tests，但对应实现尚不存在：

- `CertificateEnvelopeV2` 内容绑定和 mutation rejection；
- Horn -> AAF `TranslationWitness`；
- 外部 `RuntimeRefinementReceipt`；
- 自动 Lean source/theorem inventory。

因此当前状态是“测试规格已写、实现未闭合”，不是完成。

### 1.3 可继承资产

1. `FiniteMonotoneIteration`、`DungFixedPoint`、`HornFixedPoint`、`WeightedSupNorm` 等已证明核心。
2. 当前 Dung grounded fixed-point、Horn least fixed-point 和有限迭代证明。
3. 当前四 slice 的 DDL 定义和三个已闭合 theorem。
4. 11 个 canonical type 的 v1 Python 语义词表。
5. 当前 certificate/checker、Horn/AAF contract、TemporalKripke 和 runtime differential 的原型与反例。
6. Lean toolchain、Mathlib commit、guard rule、SORRY ledger 和正式发布文档框架。

以上资产只能按其精确证明范围继承，不能外推为整个 JC 已形式验证。

### 1.4 必须替换或升级

1. v1 canonical types 过薄，缺来源、准入、版本、双 IR、精确数值、solver 和 receipt 语义。
2. `Certificate` 依赖生产者自报布尔值，正例允许 empty trace。
3. Horn/AAF contract 未证明 expected edge 完整、无伪造边和 priority 方向。
4. `TemporalKripke` 不足以承载来源版本、事件时点、观察时点、适用时点和修订链。
5. runtime differential 旧模型可由同一侧写入两个状态，不是跨实现证据。
6. release inventory、axiom audit、proof ledger 和 current-head 构建证据未形成一份可独立验证的正式证书。
7. 旧方案 L3/L4 的 DEFERRED 决定与完整工程目标冲突，由本方案取消。

## 2. 本仓职责边界

### 2.1 必须负责

1. 版本化 canonical semantic universe。
2. `LegalSpec` 与 `Legal-IVL` 的数学定义、well-formedness、归一化和 lowering contract。
3. Horn、DDL、argumentation、attack、exception、permission、priority、cycle 的形式语义。
4. 双时态/多时点适用性和精确数值语义。
5. ASP/SMT backend 的输入语义、模型/证明见证和 TCB 边界。
6. 来源、解释、事实准入三门的形式隔离和 taint noninterference。
7. proposal-only Agent、人工 receipt 和正式事实之间的权限不提升定理。
8. 编译器翻译见证、语义保持义务、反例和 mutation oracle。
9. 独立 certificate checker、solver witness checker、runtime refinement verifier。
10. commit/tree/toolchain/source-bound formal release certificate。

### 2.2 绝对不负责

- 不抓取或判定现实法源权威。
- 不认定个案事实真实。
- 不保存私人案件或律师策略。
- 不实现 Deli 的 Agent/RAG/研究调度。
- 不实现 JC 的生产运行时、CLI、MCP 或审计存储。
- 不组织 Legal Harness 的律师批准流程。
- 不把 Python/SMT 测试冒充 Lean theorem。
- 不把 Lean 对抽象模型的证明冒充现实法律正确性。

## 3. P01—P09 全量吸收矩阵

| 研究项 | LMM 形式化任务 | 必须输出 |
| --- | --- | --- |
| P01 | 人工 receipt 的身份、scope、输入同一性和授权不提升 | `HumanResearchReceiptContract`、same-task binding theorem、缺席/过期反例 |
| P02 | source/constraint bundle 完整性的结构性质和 digest binding | `SourceBundleSpec`、completeness predicate、tamper counterexample |
| P03 | cyclic attack、exception、permission、priority、grounded/其他语义关系 | typed AAF/defeat semantics、termination/fixed-point/priority theorem、cycle counterexample corpus |
| P04 | direct/Horn/argumentation/closed-form/ASP/SMT backend 的共同语义与路由义务 | `BackendContract`、model/witness checker、UNKNOWN/TIMEOUT fail-closed theorem |
| P05 | LLM/Agent proposal taint 与正式域 noninterference | `ProposalEnvelopeSpec`、no-escalation theorem、false accept/false reject fixtures |
| P06 | 法源有效期、观察、事件、裁判基准、修订/撤回的时态语义 | `TemporalApplicability`、bitemporal/version theorem、边界反例 |
| P07 | `LegalSpec -> Legal-IVL -> targets` 完整编译与逐跳见证 | typed AST、lowering relation、translation witness、soundness/completeness obligations |
| P08 | 跨文书 `source_path` 的有向关系、断链、环和适用性边界 | `SourcePathSpec`、path integrity theorem、retrieval-not-applicability theorem |
| P09 | source/interpretation/fact 三门分离及正式 attestation 精确绑定 | `FactAdmissionSpec`、gate independence、taint noninterference、revocation theorem |

## 4. 冻结负结果的正确工程用法

1. 来源结构抽取先于表示选择：`LegalSpec` 必须保留来源层级和 locator，不能只接平面文本。
2. 简单 DOM 候选失败：source structure contract 包含正文边界、条/款/项层级、附件、版本和内容哈希。
3. flat Horn/retrieval-only 在冲突、例外和优先级任务上失败：完整 argumentation/DDL 语义必须进入正式模型。
4. argumentation 不应无条件增加运行成本：`Legal-IVL` 统一语义，JC 可用经证明的无冲突优化定理走快路。
5. 旧窄任务未观察到多层 IR 净收益：该结果成为性能/复杂度 benchmark 和 regression，不成为架构否决。
6. 双 IR 仍是正式目标；LMM 必须给出逐跳语义、验证条件和可检查见证，使先进架构不是标签。
7. checker 只能证明 checker contract；Lean theorem、solver witness、runtime refinement、法律审核保持分证据域。
8. LLM false accept/false reject：proposal taint 不能被共识、置信度或重复运行洗白。
9. source authority、fact reliability、interpretation fidelity、translation fidelity、logical correctness、execution correctness 分别建模。
10. UNKNOWN、TIMEOUT、SKIP、NOT_RUN、BACKEND_UNAVAILABLE、ERROR 全部 fail-closed。

## 5. 目标分层架构

```text
Layer 0  IDs, digests, versions, scopes, canonical serialization
Layer 1  SourceBundle / SourcePath / Evidence / Admission contracts
Layer 2  LegalSpec typed source-oriented semantics
Layer 3  Legal-IVL backend-neutral formal semantics
Layer 4  Horn + DDL + Argumentation + Temporal + Exact Numeric algebras
Layer 5  Horn / Grounded / ASP / SMT target semantics and witness checkers
Layer 6  Translation and refinement theorems/counterexamples
Layer 7  CertificateEnvelopeV2 + independent checkers
Layer 8  RuntimeRefinementReceipt + mismatch classification
Layer 9  FormalReleaseCertificate + reproducible proof release
```

每层都有：版本、输入、well-formedness、canonical form、failure state、receipt、独立检查器和允许/禁止声明。

## 6. Canonical Semantics v2

v1 的 11 个 canonical types 作为兼容层保留；v2 扩充为完整类型宇宙，不在原类上偷偷塞自由字典。

### 6.1 基础身份类型

- `LegalId kind`
- `ContentDigest`
- `SchemaVersion`
- `SemanticsVersion`
- `CommitId` / `TreeId` / `BuildId`
- `CaseScope` / `RunScope`
- `SourceLocator`
- `TimePoint` / `TimeInterval`
- `ExactAmount` / `ExactRate` / `RoundingPolicy`

### 6.2 来源与准入类型

- `SourceSnapshotRef`
- `SourceVersionEdge`
- `SourcePath`
- `EvidenceRef`
- `InterpretationRef`
- `FactCandidate`
- `FactAdmissionAttestation`
- `ProposalEnvelope`
- `HumanResearchReceipt`

### 6.3 规则与推理类型

- `LegalFact`
- `LegalRule`
- `LegalNorm`
- `LegalClaim`
- `Argument`
- `Attack`
- `Priority`
- `Permission`
- `Exception`
- `Violation`
- `Reparation`
- `DecisionStatus`
- `ProofTrace`

### 6.4 编译与后端类型

- `LegalSpec`
- `LegalIVL`
- `ProofObligation`
- `BackendKind`
- `BackendProblem`
- `BackendWitness`
- `TranslationWitness`
- `CheckerReceipt`
- `SolverReceipt`
- `ProofReceipt`
- `RuntimeRefinementReceipt`

Python 与 Lean 名称、字段语义和枚举由机器可读 manifest 对齐；Python 可序列化合同不取得 Lean 定义 authority。

## 7. M0：基线、工具链和 authority 收敛

### 动作

1. 冻结 branch、HEAD、tree、dirty、toolchain、Mathlib commit、Python interpreter 和依赖。
2. 重建 Lean source/theorem inventory；静态数量不写成永久产品事实。
3. 找到或安装项目锁定 Lean toolchain；没有真实 `lake clean && lake build` 就保持 BLOCKED。
4. 收口当前红测试：确认失败原因均是缺实现，不是 import path、环境或测试自身错误。
5. 为 canonical v1、四 slice、proven core、现有 Python reference、旧 runtime differential 建立 authority map。
6. 将 `260810_legal-math-modeling必要补充施工方案.md` 标为 superseded input；保留历史，不删除证据。
7. 重写 task_plan/findings/progress 的当前状态，历史日志与当前 authority 分开。
8. 固定 P01—P09 formal fixture manifest；expected、actual、oracle 和 mutation producer 分离。

### Gate

- Lean/Python/manifest 任一真实基线不明：停止 M1；
- current red/green 状态必须有命令、退出码和 collection manifest；
- 不允许从 AGENTS、README 或旧报告复制数量宣告构建成功。

## 8. M1：ID、digest、well-formedness 与 canonicalization

### 计划新增 Lean 模块

以下均是计划文件，当前不存在：

- `LegalIds.lean`
- `LegalModelV2.lean`
- `LegalWellFormed.lean`
- `CanonicalSerialization.lean`
- `FailureStatus.lean`

### 定理/义务

1. typed ID kind 不可交叉替换。
2. canonical collection 无重复 ID、顺序确定。
3. well-formedness 对引用闭包、方向、scope、version 和类型完整。
4. canonicalization 幂等。
5. serialization round-trip 保持 canonical semantic value。
6. digest 被作为可信函数参数建模；证明只覆盖绑定关系，不假装证明 SHA-256 密码学安全。
7. 未知 schema/semantics/version 映射为 fail-closed，而不是默认旧版本。

### Python 对照

- 升级 `theory/spec/canonical_semantics.py` 为 v2 package；
- 自动生成/校验 enum/type manifest；
- 属性测试覆盖顺序、重复、未知字段、Unicode、空值和 tamper。

### Gate

- v1 -> v2 migrator 有明确 loss report；
- Lean/Python manifest 一致；
- round-trip 和 mutation tests 通过；
- proven core 不因重构被修改。

## 9. M2：P02、P06、P08 来源、路径与时态

### 模块

- `SourceBundleSpec.lean`
- `SourcePathSpec.lean`
- `TemporalApplicability.lean`
- `theory/spec/source_bundle.py`
- `theory/spec/source_path.py`
- `theory/spec/temporal_applicability.py`

### 完整时态模型

区分：

- publication time
- effective interval
- event time
- observed time
- as-of/research time
- decision time
- correction/retraction time
- supersession chain

### 定理/义务

1. source bundle 的结构完整性和引用闭包。
2. 内容或 locator 改变使旧绑定失效。
3. source path 每条边有类型、方向和 witness；断链和未知边失败关闭。
4. retrieval relevance 不蕴含 source authority 或 legal applicability。
5. 版本适用只在时间区间、修订链和 decision context 一致时成立。
6. observed-at 不得晚于允许的 as-of；未来信息不得回流。
7. retracted/corrected/superseded source 的旧 certificate 失效。
8. 区间端点、时区、日期粒度和 unknown 均显式。
9. source-path cycle 可被检测；允许的引用环与非法依赖环分型。

### Gate

- 边界时点、同名异文、版本断链、撤回、未来信息、路径反向和循环 mutation 全部被拒；
- `TemporalKripke.lean` 保留原证明范围，新模型通过 refinement/embedding 连接，不静默改写；
- LMM 不宣称具体来源具备现实法律权威。

## 10. M3：P09 三门准入与 taint noninterference

### 模块

- `FactAdmissionSpec.lean`
- `TaintNoninterference.lean`
- `ReceiptAuthority.lean`
- `theory/spec/fact_admission.py`
- `theory/spec/receipt_authority.py`

### 三门

```text
source gate != interpretation gate != fact gate
```

每门独立状态：`PASS | FAIL | BLOCKED | DISPUTED`。

### 定理/义务

1. source PASS 不蕴含 interpretation PASS。
2. interpretation PASS 不蕴含 fact PASS。
3. hash/content binding 不蕴含 source authority。
4. rule/checker/solver PASS 不蕴含 fact reliability。
5. candidate、user-assumed、disputed、revoked、expired attestation 不能进入 decisive premise set。
6. attestation 必须绑定 exact fact/source/interpretation/case/run/signer authority。
7. 跨案、跨 run、跨版本重放不保留准入。
8. tainted input 对 formal certificate noninterference：不能通过后续 Horn、AAF、solver 或多数 Agent 转成正式事实。
9. revocation 单调地撤销相关 decisive certificate，不自动撤销无关结论。

### Gate

- proposal injection、self-issued verified、跨案 replay、过期、撤销和 partial evidence mutation 全部 fail-closed；
- 反例机器可重放；
- LMM 只证明抽象准入合同，不认定现实事实。

## 11. M4：P03 完整 DDL 与 argumentation 语义

### 模块

- 升级 `DDLDefinitions.lean`
- 升级 `DungDefinitions.lean` / `DungFixedPoint.lean`
- 新增 `TypedAttack.lean`
- 新增 `DefeasiblePriority.lean`
- 新增 `PermissionConflict.lean`
- 新增 `ArgumentCompilerSpec.lean`
- 新增 `ArgumentSemanticsRegistry.lean`

### 语义范围

1. Horn derivation 与 rule applicability。
2. obligation、prohibition、permission、constitutive。
3. contrary-to-duty、violation、reparation chain。
4. rebuttal、undercut、exception、premise challenge、priority defeat。
5. rule/argument priority、conditional priority、priority cycle。
6. self attack、mutual attack、odd/even cycle、unattacked chain。
7. grounded 作为 JC 受保护默认语义。
8. preferred/stable/complete 等语义在 LMM 中形成显式 registry 和关系定理；JC 是否启用由版本化合同决定，不能默切。

### 关键定理/义务

- argument identity 对来源 premise 和 rule version 稳定。
- 每个 argument 有有效 derivation。
- 每个 typed attack 有合法 witness。
- expected attack 不遗漏、spurious attack 不产生、方向不反转。
- grounded operator monotone、有限终止、least fixed point 继续成立。
- 无冲突 `Legal-IVL` 子语言与 Horn least model 等价。
- conflict feature absent 时优化快路与完整 argument graph claim projection 等价。
- permission 不被普通正命题吞并。
- exception 作用于 applicability/defeat 的指定层级。
- priority cycle 产生规定的 undecided/blocked 语义，不能依迭代顺序任意决胜。

### Gate

- P03 cycle/exception/permission/priority 全套 fixture 与有限枚举 oracle 对齐；
- omission、spurious、direction、cycle-order、claim-collapse mutation 全部被独立 checker 捕获；
- 不弱化已有 fixed-point theorem；发现原命题错误时保存反例并修订合同。

## 12. M5：P04 精确数值、完整时态和多 solver 合同

### 模块

- `ExactNumericContract.lean`
- `TemporalArithmetic.lean`
- `BackendContract.lean`
- `ASPWitness.lean`
- `SMTWitness.lean`
- `SolverRouting.lean`
- Python reference 与 witness checker 对照模块

### 精确数值

- 整数最小货币单位；
- 有理数比例/利率；
- currency、unit、scale；
- rounding node/mode/precision；
- interval and bound；
- division-by-zero、out-of-range、overflow；
- Int/Real/BitVec sort 显式；
- 禁止 binary float 混入 formal path。

### 多 backend

完整定义：Horn、argumentation、closed-form temporal/numeric、ASP、SMT。另定义 direct reference/oracle contract，用于和双 IR 正式链差分。

### 定理/义务

1. routing 对 typed feature 完整且确定。
2. unsupported feature 不得落入错误 backend。
3. closed-form 与 SMT 在共同可表达域结果一致。
4. fixed-width backend 只有在范围证明成立时与精确整数一致。
5. rounding policy 缺失时不得 decisive。
6. ASP stable-model witness 可独立重验；不存在 witness 不等于 UNSAT。
7. SMT SAT model 可重验；UNSAT 只有可接受 proof/TCB receipt 才能升级。
8. UNKNOWN/TIMEOUT/BACKEND_UNAVAILABLE 不映射为 FALSE、REFUTED 或 PASS。
9. solver identity、options、seed、limits 和 problem digest 属于 receipt identity。

### Gate

- boundary、rounding、overflow、calendar、leap day、timezone、timeout、UNKNOWN、wrong sort mutation 全通过；
- solver 与 checker 物理分离；
- 所有计划 backend 均有正式合同、reference fixture 和 failure semantics，不以 direct 简单样例替代完整建设。

## 13. M6：P07 正式双 IR 与编译正确性

### `LegalSpec`

来源导向的 typed AST，完整保留：source locator、定义作用域、主体/客体、条件、结论、模态、时间、数值、例外、许可、优先级、引用、解释选择和不确定字段。

### `Legal-IVL`

backend-neutral 形式核心，包含：typed atom、rule、norm、guard、attack、priority、temporal constraint、exact numeric constraint、proof obligation、failure state。

### 计划模块

- `LegalSpec.lean`
- `LegalIVL.lean`
- `LegalSpecWellFormed.lean`
- `LegalIVLWellFormed.lean`
- `LegalSpecNormalize.lean`
- `LegalSpecToIVL.lean`
- `IVLToHorn.lean`
- `IVLToAAF.lean`
- `IVLToASP.lean`
- `IVLToSMT.lean`
- `TranslationWitness.lean`
- `TranslationRefinement.lean`

### 证明计划

1. normalization termination、idempotence 和 well-formedness preservation。
2. lowering determinism。
3. source locator、ID、modality、guard、exception、permission、priority、time/numeric constraint 保持。
4. supported fragment soundness：target 结论可回到 IVL/LegalSpec derivation。
5. supported fragment completeness：应生成的 argument/attack/constraint 不遗漏。
6. no-spurious：无输入 witness 的节点/边/约束不产生。
7. typed error totality：不支持结构返回结构化错误，不 panic/默认吞掉。
8. direct oracle 与双 IR 正式链在共同语义域等价。
9. 增量编译与 clean compilation 在声明范围内等价。
10. translation witness 对每一跳的 source/target digest、mapping、lost/defaulted field 和 proof obligation 完整。

### 工程验证

- exhaustive finite models；
- property-based generation；
- mutation：删条件、翻例外、改模态、反优先级、移时间、改单位；
- metamorphic：重排无序集合、alpha-renaming、等价规范化；
- differential：direct oracle、Lean executable spec、Python reference、JC runtime；
- counterexample minimization 与永久 registry。

### Gate

- 双 IR 是正式生产语义架构，不是 shadow 文件；
- 任何 lost/defaulted semantic field 阻止 decisive compilation；
- 未闭合 theorem 保持 `UNPROVED`，禁止 `sorry`/弱化命题；
- 编译器、reference evaluator 和 checker 不能共享同一实现自证。

## 14. M7：P01、P05 权限和 proposal noninterference

### 模块

- `ProposalEnvelopeSpec.lean`
- `HumanResearchReceiptSpec.lean`
- `AuthorityLattice.lean`
- `ProposalNoninterference.lean`

### 权限格

```text
UNTRUSTED_PROPOSAL
  < SOURCE_BOUND_CANDIDATE
  < HUMAN_REVIEWED_CANDIDATE
  < ADMITTED_FORMAL_INPUT
```

层级不能由数量、置信度、模型身份或重复运行自动提升；晋级需要独立且 scope-bound 的外部 authority receipt。

### 定理/义务

1. LLM/Agent proposal 不能签发 fact attestation、certificate 或 `DecisionStatus`。
2. 多 Agent 共识不自动提高 formal authority。
3. human receipt 只证明指定人员/角色对指定输入完成指定动作，不证明法律结论正确。
4. P01 人工/自动比较必须绑定同任务输入、时间、工具权限和输出标准。
5. receipt 缺失、跨任务复用、过期、撤销、签发者权限不足 fail-closed。
6. false accept/false reject 被保存为模型行为反例，不进入 theorem 前提规避。

### Gate

- prompt injection、self-approval、receipt swap、majority laundering、confidence laundering mutation 全部失败；
- 与 M3 taint theorem 组合后，proposal 不能穿透到 formal premise。

## 15. M8：Certificate/Checker v2 与证据域分离

### 立即闭合当前红测试

- `theory/spec/certificate_schema.py`
- `tests/spec/test_certificate_v2.py`
- Lean `CertificateV2.lean`
- Lean `CertificateCheckerV2.lean`
- `docs/spec/certificate_checker_boundary.md`

### `CertificateEnvelopeV2`

绑定 expected/used facts、expected/discharged obligations、rules、arguments、attacks、accepted set、source snapshots、rule pack、semantics、non-empty trace、producer commit、checker identity。

生产者不得提交可信的 `wellFormed`、`requiredFactsPresent`、`proofObligationsPresent` 布尔量；checker 独立重算。

### 证据域

- `LeanProofReceipt`
- `FiniteModelCheckReceipt`
- `SolverWitnessReceipt`
- `TranslationReceipt`
- `RuntimeRefinementReceipt`
- `HumanLegalReviewReceipt`
- `FormalReleaseCertificate`

每类有不同 subject、issuer、checker 和允许声明；digest 只证明内容绑定。

### 定理/义务

1. checker acceptance 蕴含已编码 well-formedness 和 obligation completeness。
2. v1 可读但永不取得 v2 decisive 状态。
3. empty trace、unknown semantics/checker、duplicate/unstable IDs、tamper、stale source、candidate evidence 均拒绝。
4. checker 与 builder/evaluator 无实现依赖。
5. certificate status 不超出最弱证据域。

### Gate

- 当前 v2 mutation tests 全部变绿；
- Lean checker 相关定理经 build/axiom audit；
- Python checker 和 Lean spec 有独立 refinement fixture；
- 禁止把 checker acceptance 写成法律正确或 runtime 完整证明。

## 16. M9：真实跨仓 runtime refinement

### 三方分离

1. LMM 生成 content-addressed expected fixture、formal semantics version 和 reference result。
2. JC 通过正式公共入口执行，生成 actual runtime receipt。
3. LMM 独立 verifier 比较 expected/actual；Deli 可提出新反例，但不能改写两端结果。

### Receipt 绑定

- LMM commit/tree/build
- JC commit/tree/build/package
- fixture/source/rule-pack digest
- LegalSpec/Legal-IVL/target translation receipt
- runtime options
- actual canonical result/audit digest
- checker/solver receipt
- execution status and timestamps

### mismatch 分类

- `SPEC_MISMATCH`
- `IMPLEMENTATION_MISMATCH`
- `TRANSLATION_MISMATCH`
- `PROJECTION_MISMATCH`
- `ORACLE_UNRESOLVED`
- `ENVIRONMENT_BLOCKED`

不得通过修改 expected 迎合 actual；每个 mismatch 必须有最小反例、authority owner 和回归测试。

### 覆盖

- P01—P09 全部 fixture；
- positive、negative、unknown、conflict、cycle、timeout、tamper；
- direct oracle 与双 IR；
- Horn、argumentation、temporal/numeric、ASP、SMT；
- CLI/JCClient/MCP 只由 JC 自己证明接口 parity，LMM 只验证收到的正式 receipt。

### Gate

- actual receipt 必须来自外部进程和正式入口，不是 same-process shadow；
- 缺 receipt、commit/digest mismatch、unknown mapping、execution error 一律 blocked；
- 只有指定 commits + fixtures 的一致性可声明，不外推整个 runtime refinement。

## 17. M10：形式发布、CI、性能和可持续演进

### `FormalReleaseCertificate`

绑定：subject commit/tree/dirty、OS/arch、Lean/Elan/Lake、Mathlib/dependencies、全部正式源 hash、theorem inventory、clean build、guard、axiom audit、Python collection/full tests、mutation/refinement、限制和证书 digest。

### 发布流水线

```text
generate source inventory
  -> lake clean
  -> lake build
  -> public theorem axiom audit
  -> forbidden-token/True-theorem guard
  -> Python collection + full tests
  -> mutation/property/finite-model suite
  -> external runtime refinement
  -> generate certificate
  -> independent verifier
  -> allowed/forbidden claim audit
```

### 先进工程能力

1. Lean module dependency DAG 和增量构建指标。
2. proof obligation 并行调度，但同一 Lean 文件保持单 writer。
3. content-addressed fixture、counterexample、receipt 和 theorem inventory。
4. 自动 counterexample shrinking 和 regression promotion。
5. schema/Lean/Python manifest drift gate。
6. theorem provenance：文件、行号、声明、imports、axioms、source digest、toolchain。
7. benchmark 分开记录 proof time、compile time、checker time、solver time、memory 和 cache hit；性能失败不靠降低语义完整性解决。
8. 发布证书由 CI 作为 artifact 生成，避免证书证明包含自身的同一 commit。

### Gate

- clean build、全测、guard、axiom、manifest、mutation、refinement、独立 verifier 全通过；
- UNKNOWN/TIMEOUT/SKIP/NOT_RUN/BACKEND_UNAVAILABLE/ERROR 任一存在时 release blocked；
- 不推送、不 tag、不 release，除非用户当轮授权。

## 18. 文件级施工地图

| 位置 | 施工内容 |
| --- | --- |
| `theory/spec/canonical_semantics.py` | 升级为 canonical v2 兼容入口 |
| `theory/spec/canonical_v2/` | Python reference types、canonicalization、schemas |
| `theory/spec/certificate_schema.py` | CertificateEnvelopeV2 与独立 checker |
| `theory/spec/translation_witness.py` | 双 IR/target translation witness |
| `theory/spec/runtime_differential.py` | expected-only fixture 与外部 actual receipt verifier |
| `theory/spec/temporal_applicability.py` | 完整多时点/版本 reference semantics |
| `theory/spec/exact_numeric_contract.py` | 精确数值、单位、舍入、范围 reference semantics |
| `proofs/lean/juris_lean/JurisLean/LegalIds.lean` | planned typed IDs/digests/scopes |
| `proofs/lean/juris_lean/JurisLean/LegalModelV2.lean` | planned canonical semantic universe |
| `proofs/lean/juris_lean/JurisLean/LegalWellFormed.lean` | planned 全模型 well-formedness |
| `proofs/lean/juris_lean/JurisLean/LegalSpec.lean` | planned source-oriented typed AST |
| `proofs/lean/juris_lean/JurisLean/LegalIVL.lean` | planned backend-neutral formal IR |
| `proofs/lean/juris_lean/JurisLean/LegalSpecToIVL.lean` | planned normalization/lowering |
| `proofs/lean/juris_lean/JurisLean/IVLTo*.lean` | planned Horn/AAF/ASP/SMT targets |
| `proofs/lean/juris_lean/JurisLean/TranslationRefinement.lean` | planned 逐跳 soundness/completeness obligations |
| `proofs/lean/juris_lean/JurisLean/FactAdmissionSpec.lean` | planned P09 三门和 attestation |
| `proofs/lean/juris_lean/JurisLean/TaintNoninterference.lean` | planned proposal/admission noninterference |
| `proofs/lean/juris_lean/JurisLean/TemporalApplicability.lean` | planned 版本/多时点语义 |
| `proofs/lean/juris_lean/JurisLean/ExactNumericContract.lean` | planned 精确数值语义 |
| `proofs/lean/juris_lean/JurisLean/BackendContract.lean` | planned 多 backend/solver 义务 |
| `proofs/lean/juris_lean/JurisLean/CertificateV2.lean` | planned 内容绑定证书 |
| `proofs/lean/juris_lean/JurisLean/CertificateCheckerV2.lean` | planned 独立 checker 定理 |
| `proofs/lean/juris_lean/JurisLean.lean` | 只在模块 build 后纳入正式 root |
| `runtime/refinement_cases/` | P01—P09 fixtures、mutations、counterexamples |
| `runtime/receipts/` | schema；真实 receipt 作为 CI artifact，不提交机器产物 |
| `scripts/generate_formal_release_certificate.py` | 自动 inventory/release generator |
| `scripts/verify_formal_release_certificate.py` | 独立 verifier |
| `docs/formal-release/` | 当前证书 schema、claim boundary、raw evidence pointers |
| `docs/spec/` | v2、双 IR、多后端、准入、证据域规范 |
| `tests/spec/` | Python contracts、mutation、property、differential |
| `.github/workflows/lean-build.yml` | 完整 release gate 和 artifact |

## 19. 测试与证明门

### 每个 Lean 模块

1. 写精确 statement/definition；
2. 先建正反 fixture；
3. helper lemma 后立即单文件编译；
4. 目标模块 build；
5. 对应 Python reference/differential；
6. axiom audit；
7. 禁止 token scan；
8. theorem manifest 更新。

### 全仓最终顺序

1. Python `--collect-only` manifest；
2. Python full tests；
3. property/mutation/metamorphic/finite model；
4. Lean source/theorem manifest；
5. `lake clean && lake build`；
6. `AxiomAudit.lean` 全公共声明；
7. guard scan；
8. 多 solver witness tests；
9. 外部 JC runtime refinement；
10. FormalReleaseCertificate 生成；
11. 独立 verifier；
12. allowed/forbidden claim audit；
13. Git diff/status 和 artifact 污染检查。

固定 regression 只证明 backend health；SMT/Python/finite model 不替代 Lean theorem；Lean theorem 不替代 runtime 或法律审核。

## 20. 迁移、回滚与 Git

- 每个 M 波独立本地 checkpoint commit；不 hard reset。
- v1/v2 并存一个明确迁移窗口；v1 永不取得 v2 decisive authority。
- proven core 无反例或 build failure 不重写；通过 embedding/refinement 扩展。
- theorem 无法证明时标记 `UNPROVED` 并保留反例/阻塞，不用 `sorry`、`admit`、`axiom` 或弱化 statement。
- solver/checker/refinement 失败时保留完整先进目标，回退的是 release 状态和入口开关，不是架构范围。
- generated `.olean`、`.ilean`、`.lake`、trace、hash 和机器 cache 不提交。
- 任何跨仓工作严格串行，先冻结两端 HEAD/tree，receipt 绑定 exact commits，防止 Git 版本污染漂移。
- 不推送、不 tag、不发布，除非用户当轮明确授权。

## 21. Definition of Done

以下全部满足才算本仓完整吸收冻结理论：

- canonical semantics v2、Lean/Python manifest 和 v1 migration 完整。
- P01—P09 每项都有正式类型、proof obligation、正例、反例、mutation 和 receipt。
- `LegalSpec -> Legal-IVL -> Horn/AAF/Temporal-Numeric/ASP/SMT` 是真实构建和执行的形式链，不是文档标签。
- 双 IR 逐跳 soundness/completeness/no-spurious/typed-error 义务按声明范围闭合；未闭合项明确 `UNPROVED`。
- P03 attack/exception/permission/priority/cycle 有完整 typed semantics、有限反例和 checker。
- P04 数值、时态和多 backend 合同完整，UNKNOWN/TIMEOUT 全部 fail-closed。
- P05 proposal 与 P09 formal admission 之间 noninterference 已证明到声明范围。
- source、fact、interpretation、translation、logic、execution 六个证据域物理和语义分离。
- CertificateEnvelopeV2 不接受 empty trace、自报布尔、tamper、stale source 或 candidate evidence。
- runtime refinement 使用 JC 正式外部回执，所有 mismatch 分类并留永久反例。
- FormalReleaseCertificate 绑定 current commit/tree/toolchain/source/build/test/axiom/refinement，可独立重验。
- 32/126 等数量仅由 current inventory 生成，不写成永久事实。
- 全量 Lean/Python/release Gate 通过，Git clean，无构建污染。
- 文档没有“完整 JC 已被 Lean 证明”“checker 等于法律正确”等越界声明。

## 22. 施工顺序

```text
M0 -> M1 -> M2 -> M3 -> M4 -> M5 -> M6 -> M7 -> M8 -> M9 -> M10
```

M0 收口 current truth；M1—M3 建完整身份、来源、时态和事实准入；M4—M7 建 DDL/argumentation、多 backend、正式双 IR 和权限 noninterference；M8—M10 收口证书、跨仓 refinement 和形式发布。前一 Gate 未过不伪造 PASS，但授权开始施工后必须继续解决阻塞并做到 M10/Definition of Done，不得用旧方案的“完成五项即停”或局部 fixture 通过缩减范围。

### [我违规之处]

- 无
