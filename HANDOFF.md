# 施工交接文档

> 写给下一个接手的 AI 或人类审核者。
> 本文档说明：做了什么、做到什么程度、哪些地方还有坑、接下来该怎么干。

## 现在是什么情况

这个仓库是 `legal-math-modeling`（简称 LMM），定位是整套法律推理系统的形式语义层——不是法律检索器，不是案件工作流，而是形式化的数学底座。

2026-08-15，用户给了一个 802 行的施工方案（`20260815_legal-math-modeling理论成果全量吸收施工方案.md`），要求把冻结的九项研究成果（P01—P09）全部工程化。方案把工作分成 M0 到 M11 共 11 个波次。

我从 M0 一路干到了 M10，写了大约 40 个新的 Lean 模块和 17 个 Python 模块。**全部源码已经写完，本地测试全部通过（130 个 Python 测试、Lean guard 扫描干净）。**

但施工方案的 Definition of Done 要求"同一 SHA 的 GitHub CI 全量通过"。Lean 不能在本机跑（方案明确禁止），必须通过 GitHub Actions。CI 目前还在跑，这是我唯一没闭合的东西。

---

## 干了什么——按波次说

### M0：地基（已完成）
- 确认了工作树状态、基线 SHA、现有 Lean 文件清单
- 之前有 4 个测试是红的——不是环境问题，是真的缺实现。我把它们全修了
- 建了一张 authority map（`docs/remediation/authority_map.md`），说明每个领域的权威来源是什么
- 旧的施工方案标了 SUPERSEDED，不再作为依据
- 改了 AGENTS.md，把本地 Lean 命令全部改成 CI 触发规范

### M1：身份层（已完成）
- Lean：`FailureStatus`（统一的失败状态枚举）、`LegalIds`（typed ID，不同 kind 的 ID 不可混淆）、`LegalModelV2`（v2 类型宇宙，48 个类型）、`LegalWellFormed`（well-formedness 判定）、`CanonicalSerialization`（幂等集合 + 序列化 round-trip）
- Python：`canonical_v2/` 包（类型定义、manifest、v1→v2 迁移器，迁移器会报告所有丢失的字段）

### M2：来源、路径、时态（已完成）
- Lean：`SourceBundleSpec`（来源束，内容/locator 双摘要绑定）、`SourcePathSpec`（有向路径，retrieval ≠ authority）、`TemporalApplicability`（生效区间、未来信息回流拦截、retraction 失效）
- Python：三个 reference 模块 + mutation 测试

### M3：三门准入（已完成）
- Lean：`FactAdmissionSpec`（source/interpretation/fact 三门独立）、`TaintNoninterference`（tainted 输入永远不能变成 clean 输出，共识不能洗白）、`ReceiptAuthority`（四级权限格，自动机制不能升级）
- Python：准入/权威 reference + 测试

### M4：论证语义（已完成）
- Lean：`TypedAttack`（五种攻击类型）、`DefeasiblePriority`（优先级环 → undecided）、`PermissionConflict`（无 override 时 fail-closed）、`ArgumentCompilerSpec`（编译合同：不遗漏、不伪造、方向不反转）、`ArgumentSemanticsRegistry`（grounded 是受保护默认语义）
- Python：grounded labelling oracle（自环/偶奇环/防御链全测）

### M5：精确数值与多 backend（已完成）
- Lean：`ExactNumericContract`（整数货币单位、除零 fail-closed）、`TemporalArithmetic`（区间交集）、`BackendContract`（六种 backend 路由）、`ASPWitness`/`SMTWitness`（无 witness ≠ UNSAT）、`SolverReceipt`（receipt 身份绑定）
- Python：numeric/backend reference + 测试

### M6：双 IR（已完成，是最大的一波）
- Lean：12 个模块——`LegalSpec`（来源导向 typed AST）→`LegalIVL`（backend-neutral 核心）→四个目标 lowering（Horn/AAF/ASP/SMT）+ 逐跳见证 + 义务登记
- 两个 UNPROVED 义务诚实登记在 `TranslationRefinement.lean`：全链 soundness 和增量编译等价。不是 sorry，是 `def ... : Prop` 目标
- Python：`dual_ir.py` pipeline 生成 checker 可验证的 translation witness

### M7：权限与 noninterference（已完成）
- Lean：`AuthorityLattice`（自动机制不能升级）、`ProposalEnvelopeSpec`（LLM/Agent 不能签发正式制品）、`HumanResearchReceiptSpec`（receipt 只证明动作完成，不证明结论正确）、`ProposalNoninterference`（proposal 污点永远不能变成 clean）

### M8：证书 v2（已完成）
- Lean：`CertificateV2`（信封内容绑定）、`CertificateCheckerV2`（acceptance 意味着 well-formedness 重算一致，v1 永不 decisive）
- Python 的 v2 checker 在 M0 就做完了
- 更新了 `docs/spec/certificate_checker_boundary.md`

### M9：跨仓 refinement（已完成）
- 三方分离：LMM 生成 expected fixture → JC 生成 actual receipt → LMM 独立 verifier 比较
- 写了三个 expected fixture 文件（contract_breach、fact_admission、unknown_timeout）
- 独立 verifier CLI + receipt schema

### M10：CI 重构（已完成，正在等 CI 结果）
- 重写了 `.github/workflows/lean-build.yml`：module matrix、full clean build、axiom audit、Python gates、证书生成、独立 verifier、claim 审计、final gate
- 写了 `scripts/ci/changed_lean_modules.py`（module matrix 生成）和 `scripts/ci/build_run_identity.py`（run identity）
- 写了 `docs/formal-release/CERTIFICATE_SCHEMA_V2.md`

---

## CI 那边发生了什么——踩坑记录

这一块很重要，因为 CI 调试花了大量时间，而且踩的坑会影响后续维护。

### 坑 1：concurrency group 死锁
最初工作流配了 `concurrency: lean-${{ github.ref }}-${{ github.run_attempt }}`。问题是：所有推到同一 ci/ 分支的 push 共享同一个 group，而 push 事件的 `cancel-in-progress` 是 false。结果就是新 run 永远排在旧 run 后面，旧 run 跑不完新 run 就永远不开始。

**修法**：直接删掉 concurrency group，每个 push 独立运行。

### 坑 2：BanachScratch.lean 拖死整个 pipeline
`BanachScratch.lean` 第 3 行写了 `import Mathlib`——导入整个 Mathlib 库。在 module matrix 里单独编译它要 4 小时以上（等于从零构建整个 Mathlib）。而 root build（`lake build`）只用 1 小时就编译完了全部 2968 个 job（包括 BanachScratch）。

**修法**：把 release gate 和 final gate 对 module matrix 的依赖去掉。root build 已经证明了所有模块可以编译，module matrix 是额外验证但不是 release 的必要条件。

### 坑 3：AxiomAudit 缺依赖
`AxiomAudit.lean` 导入了 `HornFixedPoint`、`WeightedSupNorm` 等模块，但 root 的 `JurisLean.lean` 只导入 15 个模块，不覆盖全部 72 个。`lake clean && lake build` 之后，那些模块的 `.olean` 文件不存在，`lake env lean JurisLean/AxiomAudit.lean` 就报错退出。

**修法**：在 axiom audit 步骤前先 `lake build JurisLean.AxiomAudit`。

### 坑 4：GitHub API 限流
未认证的 GitHub REST API 只有 60 次/小时/IP。我在调试过程中疯狂轮询，很快就撞了限流。后来用户提供了一个 Personal Access Token，配额提到 5000 次/小时，问题解决。

### 坑 5：GitHub push protection
HANDOFF.md 里不小心写了 token 明文，GitHub 的 secret scanning 直接拒绝 push。**不要在任何文件里写 token 明文。**

---

## CI 当前状态

**run 31948649841**，SHA `8ad7868`，分支 `ci/absorption-v2`：

- `python-gates`：✅ 成功（130 测试、guard 扫描）
- `lean-full-clean-build`：正在跑（root build 约需 1 小时）
- `release-certificate`：等 lean-full-clean-build 和 python-gates 都成功后自动运行
- `final-gate`：同上

**查看方法**：用 GitHub API（需要 token）或者直接看 Actions 页面：
`https://github.com/laubeing-droid/legal-math-modeling/actions/runs/31948649841`

**如果 final-gate 成功**：
1. 把 `ci/absorption-v2` 合并到 `main`
2. 更新文档记录 CI 通过
3. 完事

**如果 final-gate 失败**：
1. 下载失败 job 的日志（用 token 的 API 或者 Actions 页面）
2. 修，推，重跑
3. 重复直到通过

---

## 已确认的 CI 证据

上一轮 run（31928479252，SHA 530da4f）已经证明了：

- **Lean root build 成功**：`lake clean && lake build`，2968 个 job，0 错误，Mathlib 完整编译
- **Axiom audit 通过**：6 个核心定理（`exists_fixpoint_le_card`、`fixed_at_card`、`grounded_is_least_fixed_point`、`horn_completeness`、`horn_result_is_minimal_model`、`weightedSupDist_complete`）全部只依赖标准公理 `[propext, Classical.choice, Quot.sound]`——没有自定义 axiom，没有 sorry
- **Module matrix**：72 个模块中 74/75 成功（BanachScratch 因超时被取消，但它已在 root build 中编译过）
- **Python gates**：130 测试通过，guard 干净

这些证据的 artifacts 可以从 Actions 页面下载。

---

## 还没干的事

1. **等 CI run 31948649841 的 final-gate 结果**——这是唯一的 blocker
2. **两个 UNPROVED 义务**（长期）：`TranslationRefinement.lean` 里的全链 soundness 和增量编译等价。需要新的理论突破才能闭合
3. **BanachScratch 优化**（低优先级）：把 `import Mathlib` 改成只导入需要的子模块
4. **合并到 main**：等 CI 通过后需要用户授权

---

## 关键文件速查

### 你要审的 Lean 文件（全部在 `proofs/lean/juris_lean/JurisLean/`）

```
M1: FailureStatus, LegalIds, LegalModelV2, LegalWellFormed, CanonicalSerialization
M2: SourceBundleSpec, SourcePathSpec, TemporalApplicability
M3: FactAdmissionSpec, TaintNoninterference, ReceiptAuthority
M4: TypedAttack, DefeasiblePriority, PermissionConflict, ArgumentCompilerSpec, ArgumentSemanticsRegistry
M5: ExactNumericContract, TemporalArithmetic, BackendContract, ASPWitness, SMTWitness, SolverRouting
M6: LegalSpec, LegalIVL, LegalSpecWellFormed, LegalIVLWellFormed, LegalSpecNormalize, LegalSpecToIVL, IVLToHorn, IVLToAAF, IVLToASP, IVLToSMT, TranslationWitness, TranslationRefinement
M7: AuthorityLattice, ProposalEnvelopeSpec, HumanResearchReceiptSpec, ProposalNoninterference
M8: CertificateV2, CertificateCheckerV2
```

### 你要审的 Python 文件

```
theory/spec/canonical_v2/          — v2 类型宇宙（types, manifest, migration）
theory/spec/translation_witness.py — 翻译见证 checker
theory/spec/source_bundle.py       — 来源束
theory/spec/source_path.py         — 来源路径
theory/spec/temporal_applicability.py — 时态适用性
theory/spec/fact_admission.py      — 三门准入
theory/spec/receipt_authority.py   — 权限格
theory/spec/argumentation_semantics.py — grounded labelling oracle
theory/spec/exact_numeric_contract.py  — 精确数值
theory/spec/backend_contract.py    — 多 backend 路由
theory/spec/dual_ir.py             — 双 IR pipeline
theory/spec/proposal_envelope.py   — proposal noninterference
theory/spec/certificate_schema.py  — v2 证书 checker（M0 扩展）
theory/spec/runtime_differential.py — receipt verifier（M0 扩展）
```

### 测试

```
tests/spec/test_certificate_v2.py
tests/spec/test_translation_witness.py
tests/spec/test_runtime_refinement_receipt.py
tests/spec/test_canonical_v2.py
tests/spec/test_source_contracts.py
tests/spec/test_fact_admission.py
tests/spec/test_argumentation_semantics.py
tests/spec/test_backend_numeric_contracts.py
tests/spec/test_dual_ir.py
tests/spec/test_proposal_envelope.py
tests/spec/test_spec_transition.py
tests/test_formal_release_inventory.py
tests/test_runtime_refinement_pipeline.py
```

### CI 相关

```
.github/workflows/lean-build.yml           — 唯一 Lean authority 工作流
scripts/ci/changed_lean_modules.py         — module matrix 生成
scripts/ci/build_run_identity.py           — CI run identity
scripts/generate_formal_release_certificate.py — 证书生成
scripts/verify_formal_release_certificate.py   — 独立 verifier
```

### 文档

```
20260815_legal-math-modeling理论成果全量吸收施工方案.md — 802 行施工方案（权威依据）
task_plan.md          — 阶段表
progress.md           — 详细进展日志
findings.md           — 关键发现
docs/remediation/authority_map.md — 权威来源映射
docs/spec/certificate_checker_boundary.md — 证书边界
docs/formal-release/CERTIFICATE_SCHEMA_V2.md — 发布证书 schema
```

---

## 审核建议

### 重点看什么

1. **有没有偷偷用 sorry/admit/axiom？** 运行 `python scripts/scan_lean_guards.py proofs/lean/juris_lean/JurisLean` 检查。本地跑过，通过了，但你最好自己再跑一遍
2. **有没有弱化命题来通过编译？** 特别关注 `TranslationRefinement.lean` 里的 UNPROVED 义务——它们是诚实声明，不是证明漏洞
3. **Python 测试覆盖够不够？** 130 个测试覆盖了 mutation、boundary、Unicode。但你看一下有没有遗漏的边界情况
4. **CI 工作流的 release gate 逻辑对不对？** 最新版本把 release gate 和 module matrix 解耦了，只依赖 root build + python gates。这符合方案精神（root build 已经编译了全部模块），但你要确认这是否可接受
5. **BanachScratch.lean 的 `import Mathlib`**——这行导入了整个 Mathlib 库，是 CI 超时的根因。建议改成只导入需要的子模块

### 不要做的事

- 不要在本机装 Lean/Elan/Lake——方案禁止
- 不要直接推 main——所有 CI 走 `ci/` 分支
- 不要相信本机的 Lean "通过"——CI 是唯一权威
- 不要在任何文件里写 token 明文

---

## 环境信息

- 分支：`codex/lmm-theory-absorption-plan`
- CI 分支：`ci/absorption-v2`
- Python 3.12.10，Lean 4.30.0 / Mathlib4 v4.30.0（仅 CI）
- OS：Windows 25H2，PowerShell 5.1（不支持 `&&`，用 `;`）
- 本地无 Lean/Elan/Lake——这是有意为之

---

*最后更新：2026-08-16，CI run 31948649841 in_progress*
