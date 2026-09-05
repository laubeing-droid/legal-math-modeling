# 事实盘点与设计依据

## 用户要求

- 全量盘点仍需完善的“证明指导工程”的数学理论。
- 把详尽施工方案真实写回工作区。
- 不把工程落地扩大成全实现形式证明。
- 工程门禁、算法和有限组件证据可以转化为理论层的证明义务、反例或依赖阻断。

## 已确认仓库事实

- 实际 Git 根：`D:\Codex\1.法律工作区\legal-math-modeling工作区\legal-math-modeling`。
- 当前分支：`main`，相对 `origin/main` ahead 2；工作树在本轮写入前无已跟踪修改。
- 主证明技术栈：Lean 4.30.0 + Mathlib4 v4.30.0；Python 3.12 用于契约测试、桥接和独立检查。
- 本机禁止运行 Lean；GitHub Actions 是 Lean 构建与证明状态的唯一权威。
- 禁止 `sorry`、`admit`、自定义 `axiom`、`theorem : True` 和把结论塞入前提。
- 现有已证明核心模块不得在无反例或构建失败时重写。
- 2026-08-30 静态回读：`proofs/lean/juris_lean/JurisLean/` 当前有 72 个 `.lean` 文件、341 个行首 `theorem` 声明；这是源码清点，不是 CI 证明通过数。
- 根模块 `JurisLean.lean` 当前只导入 16 个模块；其余波次模块尚未自动进入根构建权威面。
- `README.md`、`proofs/README.md`、`proofs/lean/README.md` 中仍存在 25/33 个文件、94/141 个定理等历史数字；方案不得以这些叙述数字代替当前源码清点或 CI 证书。
- 当前 72 个文件已出现可复用骨架：`LegalSpec`、`LegalIVL`、`LegalSpecToIVL`、`TranslationRefinement`、`BackendContract`、`SolverRouting`、`FailureStatus`、`SourceBundleSpec`、`SourcePathSpec`、`TemporalApplicability`、`FactAdmissionSpec`、`ExactNumericContract`、`ReceiptAuthority`、`AuthorityLattice`、Horn/AAF 固定点和证书检查器。
- 唯一 CI 工作流为 `.github/workflows/lean-build.yml`；包含模块矩阵、根 clean build、AxiomAudit、Python 全测试、guard scan、release certificate 与 final gate。
- push/full-release 的模块矩阵会用 `changed_lean_modules.py --all` 单独构建全部 Lean 模块；根 clean build 仍只覆盖 `JurisLean.lean` 的导入闭包。两者都要通过才可扩大权威面。
- `changed_lean_modules.py` 已能按 import 图展开反向依赖，可直接复用到每个理论包的 changed-module 门。
- 当前工作流对证书生成器和独立验证器使用 `|| true`，final gate 只检查 job 结果；施工前必须核实报告状态是否另有硬门，不能把“job 成功”直接当独立验证通过。
- 外部研究仓库当前 HEAD：`juris-calculus-theory@c06d897b40ad03923a1a93036d224cf12a265dab`；有一个现存未跟踪 tar.gz，本方案不得触碰。
- 外部工程仓库当前 HEAD：`juris-calculus@386e9c989fbf48919ad74c392ccb546df0aabffa`，当前工作树 clean；它只提供工程需求/观察，不作为 Lean 理论权威。
- `juris-calculus-theory/AGENTS.md` 明确三仓只是被审计案例，并要求分离法源权威、翻译忠实、内部逻辑、执行正确与事实可靠性；本方案沿用这一边界。
- JC 当前形式边界明确：runtime test、spec-shadow fixture、有限 SMT、上游 Lean 定理、heuristic 是五类不同证据；不得互相冒充。
- JC V4 状态矩阵给出 73 类型、6,720 组合、115 个可达终态及四条状态不变量；这些只作为 T04/C04 的工程观察输入，不要求在本方案中证明 V4 Python 全实现。
- theory R10 综合提供 27 条最小路由假说和大量反例：检索相关不等于版本/法源/适用；缺时间窗、舍入政策、范围、攻击投影或来源局部性时应 `DEFER`；它们是 T02/T05/T06/T11/T12/T14/T17/T18 的反例种子，不是定理前提。
- theory R7 汇总确认 145 条原始证明义务全部保持 `UNRUN`；直接映射 19、未选可执行形式化 126、accepted 0。施工不得把这 145 条原样全部塞入 Lean，而应先映射到 T01—T19/C01—C04，合并语义重复项并保留来源 ID。
- R7 的 recovery classes 可直接作为迁移分组：authority/source lifecycle、compiler/translation/runtime、formal checker/solver、human/institutional、learned/RAG/agent、rule/logic/argumentation、update/state/rollback 等。
- R14 明确保留 zero acceptance、架构不排名、跨学科候选全 defer 等残余；本方案不会把旧 145 条义务的“终态阻断”冒充已完成定理。

## 初步设计决定

| 决定 | 理由 |
|---|---|
| 正式方案写入 `docs/theory/统一法律工程数学理论施工方案.md` | 用户要求独立施工方案，不能把内部 `task_plan.md` 当交付物 |
| 在 `.planning/unified-legal-engineering-math-theory/` 使用独立作用域 | 只用于内部进度、发现和恢复 |
| 本轮只写计划文件 | 用户要求施工方案，不授权改理论/工程代码 |
| 统一理论落在 LMM 仓库 | 该仓库已有 LegalSpec、LegalIVL、Lean 与证明证据边界 |
| 另外两个仓库只作输入 | 防止研究材料、工程实现反向冒充定理权威 |

## 19 个理论包的源码级初判

| ID | 理论包 | 当前可复用模块 | 初判 |
|---|---|---|---|
| T01 | 统一状态—迁移—观测内核 | `UnifiedModel`、`LegalModelV2` | 缺统一抽象；现有更多是类型登记与局部对应 |
| T02 | 任务层级与安全路由 | `BackendContract`、`SolverRouting`、`ArgumentSemanticsRegistry` | 部分覆盖；缺路由完备性、保守性与组合性质 |
| T03 | 认识论/信任准入格 | `FactAdmissionSpec`、`TaintNoninterference`、`ReceiptAuthority`、`AuthorityLattice` | 部分覆盖；缺单一格结构与跨层传播定理 |
| T04 | 失败/结果代数与 fail-closed | `FailureStatus`、`BackendContract`、`LegalIVL` | 部分覆盖；缺统一代数、组合律和错误传播闭包 |
| T05 | 法源身份、谱系、权限图 | `LegalIds`、`SourceBundleSpec`、`SourcePathSpec` | 部分覆盖；摘要绑定是抽象关系，缺版本图闭包与权限/适用性分离组合定理 |
| T06 | 多时点、版本与适用性演算 | `TemporalApplicability`、`TemporalArithmetic`、`TemporalKripke` | 部分覆盖；缺事件/观察/as-of/裁判多时钟统一模型及版本链组合 |
| T07 | LegalSpec→Legal-IVL→Target 精化与损失演算 | `LegalSpec*`、`LegalIVL*`、`Translation*`、`IVLTo*` | 骨架已在；缺端到端语义保持/保守失败的总组合定理 |
| T08 | 类型、单位与定义域理论 | `LegalSyntax`、`LegalIds`、`ExactNumericContract` | 部分覆盖；存在平行类型宇宙和字符串句柄，缺单位安全与跨层唯一表示 |
| T09 | Horn、开放世界与固定点 | `HornDefinitions`、`HornFixedPoint`、`FiniteMonotoneIteration` | 固定点核较强；开放世界/撤回下语义仍缺 |
| T10 | 规范模态 | `DDLDefinitions`、`PermissionConflict` | 仅四竖切最小核；缺一般化语义、冲突与补救组合 |
| T11 | 例外、攻击、优先级、证明责任 | `TypedAttack`、`DefeasiblePriority`、`AttackDecision`、Dung 模块 | 局部安全性质已有；缺统一击败关系和 burden 转移演算 |
| T12 | 多源链接、范围、优先级与许可 | `SourcePathSpec`、`PermissionConflict`、`LegalSpec` | 部分覆盖；缺跨来源 scope/priority/permission 的联合判定定理 |
| T13 | 增量、撤销、失效与回滚 | `FactAdmissionSpec.revokeAttestation` | 只有局部撤销 frame；缺依赖闭包、增量=全量重算条件与回滚正确性 |
| T14 | 精确法律计量与舍入 | `ExactNumericContract`、`TemporalArithmetic` | 基础合同已有；缺分段计息、舍入顺序、累计误差零漂移等一般定理 |
| T15 | 解释/谱系对应 | `CertificateV2`、`SourcePathSpec`、`CanonicalSerialization` | 部分覆盖；缺结论—理由—来源的完备/无伪造对应 |
| T16 | 定理、检查器、证明回执与证据等级 | `CertificateChecker*`、`ReceiptAuthority`、`AxiomAudit` | 部分覆盖；缺证据等级偏序与 checker soundness 的统一组合 |
| T17 | LLM/RAG/神经符号候选门禁 | `ProposalEnvelopeSpec`、`ProposalNoninterference`、`TaintNoninterference` | 安全边界已起步；缺候选召回/漏失对正式结论的条件化影响理论 |
| T18 | 架构比较、证据成本、停止与采用 | `SolverRouting`、`BackendContract` | 基本空白；路由规则不等于成本/停止/采用理论 |
| T19 | 人、机构权限与程序 | `AuthorityLattice`、`ReceiptAuthority`、`HumanResearchReceiptSpec` | 部分覆盖；缺角色委托、撤销、职责分离和程序组合 |

## 关键结构问题

- 现有模块多数证明“坏输入被拒”“定义字段保持”或有限竖切实例，尚未构成统一理论的组合闭包。
- 同一概念存在平行表示，例如 `LegalSyntax.Modality` 与 `PermissionConflict.NormKindM4`、多个数值/状态句柄；施工应先建立适配定理，不直接重写已证明核心。
- `EndToEnd.lean` 的 end-to-end 只覆盖四竖切证书门，不是“法源—文本—实现—事实”的全链条证明。
- `HumanResearchReceiptSpec.human_receipt_does_not_imply_conclusion` 目前只是回传原绑定命题；它表达边界但不是关于任意法律结论的非蕴含元定理。
- `SourceBundleSpec` 中摘要绑定是模型内等式契约，不证明现实哈希实现、来源权威或文本真实性。
- `TranslationRefinement.lean` 已明确登记 `full soundness` 与 `incremental` 为 `UNPROVED`；C02/C03 不是新臆造任务，而是现有正式欠账的升级与拆解。
- `LegalSpecToIVL.lowerSpec` 当前会把 `version` 置空，且 atoms/guards/attacks/obligations 为空；即使若干字段局部保持，也不能直接推出 LegalSpec→IVL 的观察等价。
- `ReceiptAuthority` 已有四级权限秩与单级回执，但缺通用层函数的非升级定义及串行/多输入组合。
- `FactAdmissionSpec` 的撤销只修改单条 attestation；对其派生事实、攻击、证书、解释和缓存的传递失效尚未建模。

## 当前 CI 证书链硬阻断

- `generate_formal_release_certificate.py` 的必需证据包含 `mutation-property-report.json`，但 `.github/workflows/lean-build.yml` 未生成或上传该文件。
- 同一生成器还把 `independent-verifier-report.json` 设为生成 release certificate 的前置证据；工作流却在生成 certificate 之后才运行 independent verifier，形成循环依赖。
- 生成器与 verifier 命令均带 `|| true`；final gate 只看 job success，没有读取证书/验证器 verdict。按当前源码结构，即使证书保持 blocked，工作流 job 仍可能成功。
- `AxiomAudit.lean` 只审计旧的固定点/范数核心，未覆盖 40 个波次模块及未来 C01—C04。
- 决定：施工 Wave 0 必须先把 CI 证据 DAG 改成 `build/test/guard/mutation → provisional certificate → independent verifier → final certificate/final verdict`，否则后续 Lean 证明即使通过模块编译也无法形成可信总验收。

## 用户指定的四条 P0 组合定理

- C01：信任非升级组合定理。
- C02：IR/目标观察保持组合定理。
- C03：增量更新—全量重算等价定理。
- C04：失败状态、解释和证据等级不被跨层强制转换定理。
- 决定：四条均作为贯穿 T01—T19 的硬验收门；不得被单文件局部性质、Python 测试或有限样例替代。

## 待核实

- 现有 72 个 Lean 模块对 19 个理论缺口的覆盖、部分覆盖和空白。
- 现有 CI、证明证书、清单脚本和跨仓库桥接的可复用入口。
- 最小新增文件与既有模块修改边界。
- 各现有模块的定理是否只证明了定义展开、有限特例或真正的组合性质；不能仅凭文件名/定理数判定覆盖完成。
- CI 工作流的实际 module-matrix/full-release 输入、产物和根模块纳入门。

## 问题记录

| 问题 | 处理 |
|---|---|
| 初次把正式施工正文写入内部 `task_plan.md` | 已迁移到独立 `docs/theory/统一法律工程数学理论施工方案.md`；`task_plan.md` 恢复为元进度 |
| 初次读取 JC 形式边界时误写为 `docs/formal/` | 用 `rg --files` 定位到实际 `docs/contracts/`，后续只用已验证路径 |
| 预期的 `output/proofs/proof_ledger.json` 不存在 | 已定位实际 R7 汇总与 terminal projection；原 source ledger 仅以汇总记录的 `catalog/proof_obligations.jsonl` 身份出现，不继续猜工作区路径 |
