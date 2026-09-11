# ROOT01–ROOT08 施工记录（2026-09-10 执行轮）

执行者：施工 Agent。执行入口：`20260910 ULM_V21_TO_BUSINESS_ROOT_FROZEN` 固化包。
范围声明：本记录只关闭**有限合成双文件本金任务**（`SYNTHETIC_EXACT_PRINCIPAL_ANALYTICS_TWO_FILES/1`）。
不关闭：D001–D134、全领域规则、真实胜率/校准、法律审核、JC/Harness 生产接线、任意 DOCX 语义。

## 波次A：安装与参考证据（本轮完成）

- `python -B tools/verify_package.py` → PASS，272 文件（包内一份 mimosa 插件会话残留文件
  已移出 payload 后通过；该文件不属于包内容）。
- `INSTALL.py --role lmm/jc/harness --apply` → 三仓均 APPLIED，无覆盖冲突
  （LMM 128 文件全部 create；JC/Harness 各 1 个任务说明文件）。
- `run_all.py`（包内与仓内）→ v21 232、business_root_reference 85、ext_math_probes 12、
  business_semantics_probes 16 全部 0 失败 0 跳过；consolidation 24 项中 23 通过，
  1 项（`test_symlink_refused`）在 Windows 本机因缺少符号链接特权（WinError 1314）报 ERROR，
  属宿主 OS 限制，GitHub ubuntu CI 为该测试的权威运行环境。
- `validate_plan.py --repo-root .` → PASS（57 任务、134 需求、84 种子、保留源锁全部一致）。

## 波次B：ROOT01–ROOT06（本轮完成；CI 绿，证据见文末）

### 保证级别（按 ROOT_REFINEMENT §4 记录）

采用**可检查执行见证＋已证独立 checker**路径：Lean 侧（kernel 检查）证明镜像算法的独立语义；
Python↔Lean 对应为交叉测试证据（crossCheckOnly）；字节级 UTF-8/JSON 词法在 Python TCB 侧，
Lean 侧为闭合类型化行/字段文法。两侧 TCB 边界已写入各 Lean 文件头与 `root_witness.py`。

### ROOT01 独立语义 — DONE（CI 绿）

- 文件：`proofs/lean/juris_lean/JurisLean/BusinessRoot/Semantics.lean`。
- 内容：`Guard`/`denote`、`DomainOf`（Ω(I0)=形状∧F 扩张∧Γ 成立，独立于 solver）、
  `WorldsMatch`、`JointSem`（守恒+互补四条件，不含 max 定义）、`TaskSat`（权重恰覆盖、
  期望/事件/区间/格全部对独立和定义）、`Protected`/`protectedOf`。均不引用 check 布尔或 renderer。
- Python 侧：`tools/business_relations/root/test_root_refinement.py::Root01JointSemanticsTests`
  （逐世界守恒互补、权重恰覆盖）。

### ROOT02 I0 宿主来源与无损编码 — DONE（CI 绿）

- 文件：`BusinessRoot/InputCodec.lean`（codec_roundtrip、encode_injective、binding_exact、
  binding_refuses_changed、changed_is_different）。
- Python 侧：`root_witness.py::HostInputStore`（宿主选择时保存快照，生产者只能读取不能选择/替换；
  同版本换参数拒绝 SELECTED_INPUTS_CHANGED；合法新输入开新任务入库）+ 对应测试。

### ROOT03 条件栈/枚举覆盖/checker 反射 — DONE（CI 绿）

- 文件：`BusinessRoot/GuardMachine.lean`（compile/exec；`exec_compile` 归纳证明栈机=denote；
  `machine_reflection`/`machine_boolean`）、`BusinessRoot/PrincipalChecker.lean`
  （`decomposition_unique` 守恒+互补唯一给出 max 分解；`domain_pair_exact` 枚举域两侧精确）。
- Python 侧：`root_witness.py::root03_checks`——solver 栈机/checker 位掩码/暴力 product 三套
  独立枚举一致，且每世界 execute==denote。

### ROOT04 C/U 期望、事件概率、合法行动格 — DONE（CI 绿）

- 文件：`BusinessRoot/Analytics.lean`（`split_identity`、`weighted_sub/congr`、
  `CU_expectation_conservation`：E[C]−E[U]=P−q·p 用 C/U 而非 E[R]；
  超付样例 E[C]=60、E[U]=80、E[R]=−20；阈值 0 时 P(C≥0)=1 而 P(R≥0)=3/5；
  主样例 E[C]=880、阈值 800 事件 3/5、区间 [790,930]、格 {600,850,1100} 唯一 850、
  860 在区间不在格）。
- Python 侧：`root_witness.py::root04_checks` + 测试——同一组常数由锁定参考实现复算并逐项比对
  （`CROSS_CHECK_CONSTANTS` 与 Root.lean 的 `overpay_sample`/`main_sample` 一一对应）。

### ROOT05 两文件解析精化 — DONE（CI 绿）

- 文件：`BusinessRoot/ArtifactParser.lean`（闭合行文法 `DocLine`/`ofLines`、闭合类型化行文法
  `JsonRow`/`ofJson`——无 float/NaN/null 构造器；`doc_roundtrip`/`json_roundtrip`；
  `duplicate_key_rejected`、`demoted_row_not_parseable`；`readBoth`：两文件必须都解析、
  正文必须 EXACT 模式、两份受保护记录——含精确场景权重（`Protected.weights`，由
  `protectedOf` 从模型权重按键位 zip 生成）——都必须等于独立计算的期望记录）。
- CI 收敛期发现并修复一处镜像缺口：早期 `Protected` 不含权重字段，JSON 权重篡改
  （7/16 对 2/5）会被 `readBoth` 静默接受——`tampered_json_rejected` 当时是假命题。
  加入 `weights` 字段后 Lean 镜像与 Python 参考（其 bundle 检查本就拒绝权重篡改）一致。
- Python 侧（真实字节）：`root_witness.py::root05_checks`——写盘→`read_artifacts`→
  `check_business_bundle` 接受并记录 SHA256；五类篡改（JSON 概率错、丢条件、同版本 m 整体替换、
  pending 伪完整、两来源快照混用）全部拒绝。

### ROOT06 根定理实例化 — DONE（CI 绿）

- 文件：`BusinessRoot/Root.lean`：冻结 I0（P=1000、q=300、p=2/5、阈值 800、成本
  (100,60,10,10)、格 {600,850,1100}）；`root_worlds_match`/`root_joint_sem`/`root_task_sat`
  三义务定理；`business_root_two_files`：
  WF(I0) ∧ bundle 接受 ⇒ ∃W，Worlds(W)=Ω(I0) ∧ JointSem ∧ TaskSat ∧
  ReadBoth(d1,d2)=Protected_Q(W,m)；非空洞性：`root_bundle_accepts_real`（真实工件通过）
  与全部篡改/替换/混用反例被拒（`decide` 逐一核验）；ROOT02 绑定三定理。
- 表示约定（CI 收敛期确立，两处均有据）：冻结概率以分子/分母构造器形式存储
  （`qTwoFifths` 等 abbrev），因为 `2 / 5 : ℚ` 展开为 `Rat.div`、kernel 无法 whnf，闭合
  bundle/绑定/篡改比较会在 `decide` 下卡死；解析侧经 `Rat.num_div_den` 桥接引理
  （`qTwoFifths_eq` 等）转回 `n / d` 形式供 `norm_num` 计算（其有理数识别只接受 `n / d`
  范式）。两侧各取所需，不引入 kernel 之外的可信计算。
- 审计：`BusinessRoot/RootAudit.lean` 输出 `ROOT_COMPILED_ENV_JSON=`；
  `tools/ulm_consolidation/scripts/audit_root_compiled.py` 校验 24 条必需声明、
  公理 ⊆ {propext, Classical.choice, Quot.sound}。
- CI：`.github/workflows/unified-math-v2-reference.yml` 新增
  `run_root.py`（python job）与 `lake build JurisLean.BusinessRoot.All` +
  `audit_root_compiled.py`（lean job）。

### ROOT07 JC/Harness 接线 — LMM 侧完成，生产接线 NOT_INTEGRATED

- JC（基线 8dac071，jc-harness-local/1 在位）与 Harness（基线 61de5c53，已有真实 JC 联调）
  各自收到 `docs/ulm-consolidated/IMPLEMENTATION_HANDOFF.md`（`--role jc/--role harness` 安装）。
- LMM 侧宿主契约已实现并可运行：I0 由宿主确认时保存（`HostInputStore`）、两份实际字节交付
  与内容摘要（`root05_checks`）。生产环境中 JC 唯一 application/public entry 接线、Harness
  MatterStore/CAS 取源，**须在两仓按其各自流程另行施工，本包不假称已完成**。

### ROOT08 GitHub CI 与有限根接受 — DONE（CI 绿，已合入 main）

- 分支/PR/运行号：见文末“CI 证据”一节。
- 验收分轴保持：Lean 编译=以本次 run 为准；134 业务/法律审核/真实预测=未关闭。

## CI 证据（ROOT08，2026-09-10/11）

- 分支/PR/提交：`codex/ulm-business-root-20260910` → PR #3（MERGED，合并提交 `e1aefad`）；
  最终 Lean 提交 `88644bc`。
- 参考工作流 `unified-math-v2-reference.yml` run **34519378180**：existing-jc-transport、
  lean-seeds（`lake build JurisLean.BusinessRoot.All` + `RootAudit.lean` 产出
  `ROOT_COMPILED_ENV_JSON=`，`audit_root_compiled.py` → `{"status": "PASS"}`，
  receipt：theorem_count=383、required_count=24、公理 ⊆ {propext, Classical.choice,
  Quot.sound}）、python-reference（`run_root.py` PASS）、reference-gate 全部 success。
- Lean 权威管线 `lean-build.yml` run **34519379252**（attempt 2）：lean-full-clean-build
  （`lake clean` 后从零全量构建——含 BusinessRoot 全部 9 文件与 BusinessRelations 系——
  加 Axiom audit）、release-certificate、final-gate、python-gates、
  lean-module-build(BusinessRelationsAudit/BusinessRelations) 全部 success。
  lean-module-build(BusinessRelationsDelta) 两次在慢速 runner 上因 240 分钟作业超时被
  取消/悬置（冷缓存下从零构建 mathlib 超时）；该模块的从零编译证据由同 run 成功的
  lean-full-clean-build 覆盖，不构成任何 ROOT 义务的失败。
- 收敛轨迹（保留可查的失败 run）：34512426708（7af4e7e，11 错）、34514241309（9dcc498，
  11 错）、34516894406（17c1ea3，5 错）、34517689336（ef594d4，5 错）→ 88644bc 全绿。
  修复内容：冻结概率构造器形式化（kernel 可判定）、`Protected.weights` 补权镜像缺口、
  WF 绑定器命题化、`cases hr :` 泛化后终义务 `rfl`、`Rat.num_div_den` 桥接引理供
  `norm_num`、样例定理直接复用 Analytics 已证结论。
- 本地（Windows，仅 Python）：`pytest tools/business_relations/root/test_root_refinement.py`
  → 11 passed；`run_root.py --output work/root-local-check.json` → `{"status": "PASS"}`。
  符号链接拒绝用例在本机因特权缺失（WinError 1314）无法运行，以 GitHub ubuntu CI 为权威。

## 诚实边界（不得据此夸大）

1. `decide`/`simp` 关闭的是 Lean 镜像语义的命题；Python 实现与 Lean 的对应是交叉测试，
   不是 kernel 精化。保证级别如实标注为 CROSS_CHECK_MIRRORED_SEMANTICS。
2. 字节→token 词法在 Python TCB；Lean 闭合文法从结构化 token 开始。
3. 根完成仅限该冻结合成任务；不外推任何法律/真实/全领域结论。
