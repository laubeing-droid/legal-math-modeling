# legal-math-modeling 必要补充施工方案

> 状态：SUPERSEDED INPUT（2026-08-15）
>
> 本方案已被 `20260815_legal-math-modeling理论成果全量吸收施工方案.md` 取代。
> 其中的“五项完成即停”“时态/数值只在消费者触发后施工”“仅补任务有界薄层”
> 等 scope 限制已被新方案明确废止。本文件保留历史证据，不再作为施工依据。
>
> 版本：2026-08-10
>
> 目标仓库：`D:\Codex\1.法律工作区\legal-math-modeling`
>
> 核查基线：`a3a015941f75091c87d57aa956e712f1546dd7d4`，`main` 与 `origin/main` 对齐，工作树干净
>
> 定位：任务有界的形式规格、证明、反例和运行时 refinement 证据；不是主产品

## 0. 结论

LMM 不需要扩大理论版图。必要施工只有五项：

1. 把 Lean 源码库存升级为绑定当前提交、工具链、依赖、源码哈希和真实执行日志的 `FormalReleaseCertificate`。
2. 把依赖生产者自报布尔值的证书 checker 升级为内容绑定、可独立重算的 v2 checker。
3. 把 Horn -> AAF 的字段保持补成任务有界的翻译见证，并检测遗漏边、伪造边和方向反转。
4. 只为真实消费者所需补最小时态适用性、精确数值/舍入规格。
5. 把写死 shadow 状态的 differential fixture 改为消费真实运行回执的 refinement 检查。

五项完成即停。不得以“形式化完整”为由扩建通用法律本体、规则库、Agent、RAG、SMT 服务或旧研究支线。

## 1. 当前证据边界

本轮只做静态、只读核查，未运行 `lake build`、pytest 或会写缓存的命令。因此以下是源码事实，不是 current-head 构建证明。

| 发现 | 证据 | 含义 |
|---|---|---|
| 32 个 Lean 模块、126 个 `theorem` 声明 | `README.md:19` 与静态清点 | 源码库存，不是构建/证明发布证书 |
| manifest 状态为 `source_inventory_not_release_certificate` | `docs/formal-release/theorem_manifest.json:2-7` | 当前 fail-closed 叙述正确，不能改成已发布 |
| Lean/Mathlib 版本已锁 | `lean-toolchain`、`lake-manifest.json:4-12` | 可作为证书输入，但仍需真实执行 |
| CI 只显式 clean build 与 guard scan | `.github/workflows/lean-build.yml:37-45` | 缺 current-head 证书生成、独立验证、完整 axiom/Python 门禁 |
| 外部构建记录字段过少 | `scripts/request-external-build.ps1`、`scripts/finalize-external-build.py` | 未绑定全部源码、依赖、定理清单、axiom、测试和 refinement |
| axiom audit 不是全公共接口实跑证据 | `AxiomAudit.lean:1-19`、`docs/formal-release/axiom_audit.txt` | 固定少数定理且说明文冒充 `.txt` 运行物 |
| SORRY 台账漂移 | `SORRY_LEDGER.md:13-30` | 多个列名在当前 Lean 源码不存在 |
| checker 接受可信布尔值 | `LegalSyntax.lean:179-188`、`CertificateChecker.lean:23-31` | 生产者可自报满足关键义务 |
| 正向证书使用空 trace | `EndToEnd.lean:11-49` | 只证明布尔模型内洽，不是内容绑定验证 |
| Horn/AAF 证明尚非无遗漏/无伪造 | `HornAAFContract.lean:19-80` | 只证明部分字段/类型保持，不能宣称编译完整性 |
| 时间模型过薄 | `TemporalKripke.lean:19-62` | 未覆盖有效期、观察时间、裁判基准、撤回/更正 |
| differential 没有调用真实运行时 | `runtime_differential.py:136-240` | `jc_shadow_status` 是同源写入，不是跨实现证据 |
| 缺精确金额/比例规格 | 全仓静态核查 | 无单位、scale、舍入、溢出和 solver sort 合同 |

## 2. 必须保持的边界

- 11 个 canonical legal types、4 个 DDL modality、4 个既有 slice 不随本方案自动扩张。
- `DecisionStatus`、verified fact、Horn、attack、exception、permission、priority、checker 和 fail-closed 语义不弱化。
- `FiniteMonotoneIteration`、`DungFixedPoint`、`HornFixedPoint`、`WeightedSupNorm` 无反例或构建失败不得重写。
- LMM 只定义规格、证明边界、独立 checker、反例和 refinement 合同；外部运行时负责实现。
- LMM 自身 release certificate 与外部 runtime refinement receipt 是两个不同产物。
- source digest 只能证明内容绑定，不能证明法源权威、翻译忠实或实体结论正确。
- Lean 证明规格层性质，不自动证明 Python、Z3、哈希实现或外部系统正确。

## 3. 明确不做

- 不新增完整法律本体、法条库、法律检索、案件产品接口。
- 不把时间、金额、来源版本新增为 canonical legal type；优先使用 versioned sidecar。
- 不新增 preferred、stable、CF2 等语义，除非出现具体反例且 grounded 无法满足任务。
- 不把四个 demo slice 推广成“中国法已形式化”。
- 不追求 theorem 数量。
- 不恢复 DP、图相似度、Banach pricing、贝叶斯工时、跨法域 Rosetta 等支线。
- 不实现 LLM、Agent、RAG、通用 SMT 服务。
- 不宣称 runtime 已被 Lean 完整 refinement-proved。

## 4. L0：current-head 形式发布证书

优先级：P0。可独立施工。

### 4.1 文件范围

- `docs/formal-release/theorem_manifest.json`
- `docs/remediation/lean_manifest.json`
- `docs/audit/proof_ledger.json`
- `scripts/request-external-build.ps1`
- `scripts/finalize-external-build.py`
- `scripts/scan_lean_guards.py`
- `.github/workflows/lean-build.yml`
- `proofs/lean/juris_lean/JurisLean/AxiomAudit.lean`
- `SORRY_LEDGER.md`

最小新增：

- `docs/formal-release/formal_release_certificate.schema.json`
- `scripts/generate_formal_release_certificate.py`
- `scripts/verify_formal_release_certificate.py`

### 4.2 证书内容

- subject commit、tree hash、dirty 状态；
- OS/架构、Lean/Elan/Lake 版本；
- `lean-toolchain`、`lakefile.lean`、`lake-manifest.json` 摘要；
- 正式模块路径、SHA-256；
- 自动提取的 theorem 名称、路径、行号、数量；
- `lake clean && lake build` 命令、退出码、起止时间、原始日志摘要；
- guard scan 原始结果；
- 公共定理 axiom audit 原始输出和受信基础；
- pytest collection manifest、全量测试结果；
- `UNKNOWN/TIMEOUT/SKIP/NOT_RUN/BACKEND_UNAVAILABLE/ERROR` 全部保留；
- 证书自身 digest 和限制性声明。

### 4.3 存储规则

- 源仓提交 schema、生成器和独立 verifier。
- current-head 证书由 CI 生成，作为不可变 artifact/release asset 发布，名称含 subject commit。
- 不把证书提交到它所证明的同一个 commit，避免自指改变 HEAD。
- 本机 ignored `build-logs/` 只算 provisional evidence。
- `theorem_manifest.json` 继续是自动生成的 SourceInventoryManifest，不改名冒充 release certificate。

### 4.4 台账修复

- SORRY ledger 与当前源码定理集合自动比对；旧名删除或明确标为 historical/nonexistent。
- 说明性 `axiom_audit.txt` 改为 `.md`；真正 `.txt` 只由命令输出。
- `AxiomAudit.lean` 改为公共声明清单驱动，覆盖 checker、四切片安全定理、Horn/AAF 合同及固定点核心。

### 4.5 Gate

clean build、Python tests、guard、axiom audit、manifest 重建和独立 verifier 全通过。任一未跑或失败，状态继续为 `source_inventory_not_release_certificate`。

## 5. L1：Certificate/Checker v2

优先级：P0。任何新消费者启用 LMM certificate 前必须完成。

### 5.1 施工范围

- `LegalSyntax.lean`
- `CertificateChecker.lean`
- `SafetyTheorems.lean`
- `EndToEnd.lean`
- `theory/spec/certificate_schema.py`
- `tests/spec/test_spec_transition.py`
- `docs/spec/certificate_checker_boundary.md`

### 5.2 数据设计

保留 v1 只读兼容，新增 `CertificateEnvelopeV2`。关键字段：

- expected/used fact IDs；
- expected/discharged obligation IDs；
- rule、argument、attack IDs；
- source snapshot IDs 与内容摘要；
- rule-pack digest；
- semantics ID/version；
- non-empty trace digest；
- producer commit、checker version。

`wellFormed`、`requiredFactsPresent`、`proofObligationsPresent` 必须由 checker 重算，生产者不得提交可信布尔结果。

### 5.3 状态规则

- 空 trace、未知 source snapshot、digest mismatch、义务不完整、未知 semantics、candidate evidence：拒绝 decisive acceptance，返回结构化 `UNDECIDED/TAINTED` 或更严格状态。
- Python checker 与 builder/evaluator 物理分离，只读 schema 和输入内容。
- Lean 定理只声明：内容绑定前提成立时，checker acceptance 蕴含对应前提；不宣称外部 digest 算法正确。

### 5.4 强制变异测试

- 空 trace + 旧三个布尔量为 true；
- 修改一个 fact/rule/source digest；
- 删除一个 obligation；
- accepted argument 不在 constructed set；
- priority attack 方向翻转；
- candidate 改写 `verified=true`；
- 未知 schema/semantics/checker version；
- 重放过期 source snapshot；
- 重复 ID、不稳定序列化。

Gate：以上变异全部被拒；v1 输入可解析但不能取得 v2 decisive 状态。

## 6. L2：Horn -> AAF 翻译见证

优先级：P1。由真实翻译消费者触发。

### 6.1 文件范围

- `HornAAFContract.lean`
- `HornOperationalRefinement.lean`
- `theory/spec/horn_aaf_contract.py`
- `theory/spec/reference_semantics.py`
- `tests/spec/test_spec_transition.py`
- `docs/spec/horn_to_aaf_contract.md`

可新增：

- `proofs/lean/juris_lean/JurisLean/TranslationWitness.lean`
- `theory/spec/translation_witness.py`
- `runtime/refinement_cases/*.json`

### 6.2 Witness 内容

- 输入规则/事实/例外/优先关系 digest；
- 输出 argument/attack 的来源映射；
- 每条输出边的 input witness；
- 每个应生成边的 expected relation；
- ID 映射与方向；
- argumentation semantics；
- 被拒或无法翻译输入及原因。

### 6.3 有界证明目标

- 结论、支持事实、规则 ID 保持；
- 每个输出 argument 有输入 derivation；
- 每个 attack 有 exception/priority/rebuttal witness；
- 声明范围内 expected edge 不遗漏；
- 无 input witness 的 edge 不产生；
- priority 方向不反转；
- 未知 edge kind、重复 ID、循环策略缺失时 fail-closed。

Gate：omission、spurious edge、direction reversal 三类 mutation 全部被独立 checker 阻断。结论只限固定 input language、semantics 和 fixture 范围。

## 7. L3：最小时态适用性规格

优先级：P1。仅在消费者开始使用法源版本或事件状态更新时施工。

保留 `TemporalKripke.lean` 作为既有有限时间线模型；新增独立 sidecar：

- `proofs/lean/juris_lean/JurisLean/TemporalApplicability.lean`
- `theory/spec/temporal_applicability.py`
- `runtime/refinement_cases/temporal/*.json`

字段：

- `valid_from`、`valid_to`
- `observed_at`
- `as_of`
- `event_time`
- `supersedes/retracted/corrected`
- 区间端点规则和 unknown 状态

最小规则：

- `valid_from <= event_time < valid_to`；
- `observed_at <= as_of`；
- retracted/corrected 旧版本不得生成 decisive certificate；
- 有效期缺失、边界不明、版本冲突不得默认适用；
- source snapshot 改变使旧 certificate 失效；
- 增量与 clean rebuild 等价只在已证明或指定 fixture 差分通过时声明。

不形式化完整诉讼期限体系、所有溯及力规则或通用 LTL 法律语义。

## 8. L4：最小精确数值规格

优先级：P1。只有消费者暴露金额、比例、利息或 solver 分支时接入。

可新增：

- `proofs/lean/juris_lean/JurisLean/ExactNumericContract.lean`
- `theory/spec/exact_numeric_contract.py`
- `runtime/refinement_cases/numeric/*.json`

合同必须明确：

- 数值域：整数最小货币单位或有理数；
- unit、scale、currency；
- solver sort：Int/Real，不得静默切到有限位 BitVec；
- 可接受范围；
- 舍入节点、模式、精度；
- 除零、范围外、不可表示；
- 同一计算链禁止混用 binary float 与精确值。

缺单位/scale/舍入政策时返回 `UNDECIDED/DEFERRED`。固定位宽后端必须有不溢出证明或运行时范围证书；wraparound 与精确整数不同即拒绝。

## 9. L5：真实 runtime refinement receipt

优先级：P0/P1。依赖外部运行时提供稳定正式入口和回执格式。

### 9.1 责任分离

- LMM 生成 content-addressed input fixture 与 reference expected result。
- 外部运行时通过其正式链执行并输出 actual receipt。
- LMM 独立 verifier 比较 reference/actual。
- 调度器可启动流程，但不得生成或改写 expected/actual。

### 9.2 修改范围

- `theory/spec/runtime_differential.py` 不再生成 `jc_shadow_status`。
- 新增 `runtime_refinement_receipt.schema.json`。
- `runtime/legal_math_four_slice_differential.json` 降为 historical fixture 或 expected-only。
- `HornOperationalRefinement.lean` 写清精确合同，不暗示已存在真实 differential。
- 测试必须注入实际 receipt；缺 receipt、commit mismatch、digest mismatch、运行失败、状态映射未知全部 fail-closed。

### 9.3 声明边界

该产物叫 `RuntimeRefinementReceipt`，不得叫 `FormalReleaseCertificate`。允许声明仅为：“指定 LMM/runtime 提交在指定 fixture 上一致”。禁止外推为完整 runtime refinement。

## 10. 阶段、依赖与估算

| 阶段 | 内容 | 依赖 | 通过条件 | 失败处理 |
|---|---|---|---|---|
| L-A | current-head 发布证书 | 无 | clean build、全测、guard、axiom、独立 verifier | 保持 source inventory 状态 |
| L-B | checker v2 | L-A | 空轨迹/伪造布尔/digest 变异均拒绝 | v1 只读，v2 不启用 |
| L-C | 翻译见证 | L-B、输入协议冻结 | omission/spurious/direction mutation 拦截 | `UNPROVED/DEFERRED` |
| L-D | runtime receipt | L-C、正式入口 | actual 非硬编码，commit/digest 一致 | 只阻止跨实现对齐声明 |
| L-E | 时态/数值合同 | 真实任务触发 | 边界、撤回、舍入、溢出负测通过 | 不接正式路径 |
| L-F | 文档/release | 前述通过 | 证书、台账、允许/禁止声明一致 | 不 tag/release |

估算：[中等] (50-80%) L-A 2—3 人日；L-B 3—5 人日；L-C/L-D 4—7 人日；L-E 4—7 人日。L-E 未被真实任务触发时不施工。

## 11. 完整验证顺序

1. 生成 pytest collection manifest。
2. 全量 Python tests。
3. 重建正式 Lean 模块和 theorem manifest。
4. `lake clean && lake build`。
5. `lake env lean JurisLean/AxiomAudit.lean` 并保存原始输出。
6. guard scan。
7. checker/translation/temporal/numeric mutation tests。
8. 正式 runtime cross-implementation run。
9. 独立验证 FormalReleaseCertificate。
10. 独立验证 RuntimeRefinementReceipt。
11. 复核允许/禁止声明。
12. 用户确认后方可 tag/release。

证据保存：命令、退出码、起止时间、collection/pass/fail/skip、subject commit/tree、关键输入输出 digest、runner/toolchain/dependency、未运行项和 rollback commit。

## 12. 回滚

- 每阶段独立本地提交；不用 hard reset。
- v1/v2 schema 并存一个明确兼容窗口，消费方未通过 v2 前不删 v1 reader。
- Lean 命题无法闭合时保留为未证明目标或撤回阶段，不弱化命题。
- checker v2 误阻塞时回退接入开关，不回退内容绑定要求。
- refinement 失败置 `INCONCLUSIVE`，不得修改 expected 迎合 actual。
- 时态/数值合同不成熟时不接入，不 silent fallback。
- release certificate 生成失败继续公开声明“源码库存，非 current-head 发布证书”。

## 13. Definition of Done

- [ ] 存在绑定明确 subject commit 的真实 FormalReleaseCertificate，并可独立重验。
- [ ] theorem manifest 自动生成，名称、路径、行号、摘要和数量与源码一致。
- [ ] SORRY ledger 不引用不存在的当前定理。
- [ ] 公共定理 axiom audit 有原始运行输出。
- [ ] checker 不接受“空 trace + 自报布尔 true”的 decisive certificate。
- [ ] Horn -> AAF omission、spurious edge、priority 反向 mutation 均被阻断。
- [ ] differential 结果来自正式执行回执，不是 LMM 写死的 shadow 状态。
- [ ] 两端 commit、fixture、source/rule-pack、输出 digest 可追溯。
- [ ] 时态 unknown/撤回、舍入缺失、溢出/位宽不符 fail-closed。
- [ ] LMM release certificate 与 runtime refinement receipt 物理、语义分离。
- [ ] 未经独立授权不改变 11 canonical types、4 modalities、4 slices。
- [ ] 文档只出现任务有界声明，不出现“运行时已被完整形式验证”等禁称。

### [我违规之处]

- 无。
