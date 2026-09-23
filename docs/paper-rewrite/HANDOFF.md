# 施工Agent启动说明：论文重写唯一执行包

你接手的是 `legal-math-modeling` 的论文全量重写。上一轮已经做过五问全仓排查，结论在本文件里。**不要重新审计**。你的任务是按本文件写稿，只在标"待复核"的条目上补验。

阅读顺序：本文件 → `docs/paper-rewrite/CLAIM_CEILING.md`（若存在）→ `docs/formal-release/theorem_inventory_v3.json` → `AGENTS.md` → 源码。

## 目标与已定路线

把 `paper/` 下的十五份文档推倒重写为**一份**中英双版母本。输入只有一个：`proofs/lean/juris_lean/JurisLean/` 里的 Lean 证明本体。旧稿（ChatGPT 生成的 `main.tex`+`sections/*.tex` 与 `main.md`、`main_cn.md`、12 篇专题稿）是**已知坏输入**，只用于抽数字和防传染，不得作为任何一句正文的来源。

已定的四条路线决定，不要重新讨论：

1. 全量推倒重写，不按"润色旧稿"处理。
2. 中英双版并行，同一结构。
3. 贯穿实例只用仓库自带的形式化实例，不虚构案情。可用：`TemporalKripke.lean` 的 `litigation_timeline`（三世界，事实日 1/5/15，程序日 10/20/30，转移 W1→W2→W3，证 `litigation_always_guard`）；`DDLDefinitions.lean` 的 `contract_breach_direct_violation_shape`、`license_permission_not_direct_violation`。
4. 补证不挡成稿。缺的定理写进局限与附录，不阻塞交付。

## 论文的主张上限

标题性主张已从"可组合保证架构"改为：**六类播报失真在类型层面无法表达**。其中四条在 ULM 主干内，两条在主干外的独立理论里，这个内外之别要明写，是结果不是缺陷。

允许写的数字（均已在源码层核实）：

- 145：`ULM*.lean` 19 个文件里的 `theorem` 声明条数，与 `ULMAllTheoremsAxiomAudit.lean` 的 145 个 `#print axioms` 目标名**双向零差集**。
- 27：`ULM16TheoryComposition.lean` 的定理条数，等于核心组合审计的 27 个目标名，且 27 条**全部**是把更早定理原样转发。
- 4：ULM 主干的全部外部依赖文件数（`ArgumentSemanticsRegistry`、`FactAdmissionSpec`、`FiniteMonotoneIteration`、`HornFixedPoint`）。
- 85/94：LaTeX 旧稿里编号公式中从未被 `\eqref` 引用的条数。

禁止打印，除非另行核实：

- "97 jobs succeeded"、"91-module matrix"、"2993 completed jobs"。两个 workflow 里 `matrix:` 命中数为 0；本地八份历史证书 JSON 里 `jobs`、`mutation`、`clean_build` 字段命中数为 0；这些数只存在于 `docs/formal-release/FINAL_FORMAL_RELEASE_REPORT.md` 那份手写报告和已过保留期的 run 工件。
- "46/46 mutations killed"、"mutation score 1.0"。`scripts/run_mutation_property_gate.py` 里 `KILLED` 的判据是"该 pytest 用例没有 failure/error/skipped"，`mutation_score = KILLED / len(cases)`，不生成变异体。可改写为"46 个受控畸形输入全部被拒绝"，不得称变异测试。
- "发布层 fail-closed / 内容级校验"。`assemble_release_certificate` 对五份证据文件只做 `_sha256_of`，判据是 `if not missing and identity_valid`；`tests/test_formal_release_inventory.py:73` 往这五个文件全写 `"bound evidence\n"`，并断言证书为 `RELEASE_PASS_PENDING_INDEPENDENT_VERIFICATION`、`error_codes == []`，该测试通过。
- "未发现项目自定义公理"限定于 ULM 名单。FullMath 整个子树 `#print axioms` 命中 0 条，其中 11 个文件使用 `noncomputable`/`Classical`/`choose`。
- 法发〔2020〕24号。生效日已核到原句"本意见自2020年7月31日起试行"，字号未核到官方文本，`references.bib` 的 note 里已记为禁印。
- 法答网"2023年7月上线"。目前只有《AI背景下类案检索方法新指引》自序一个二手来源。
- 任何把 94/476、91/452、200/1445 混用的表述。这些属不同 subject，须逐处绑定。

## 数学已经证明了什么（第一问）

三层强度，正文必须按层写，不得混数：

**类型不可表达类**（主干主体）。`PartialPayload` 把 `open_nonempty` 作为字段；`EvalResult.noExtension` 以 `extensionsForProfile profile af = ∅` 为参数；`adjudicate` 遇 incomplete 只产出 `solverIncomplete`；`solverIncomplete_ne_adjudicated`、`pending_ne_adjudicated`、`map_never_upgrades_failure`、`halted_has_no_step` 等由 `cases h` 或 `rfl` 闭合。这一类不是弱结果，它主张的是"写不出违反约定的代码"。

**真归纳与构造**（数量少、全篇承重）。`FiniteMonotoneIteration.lean:39,46,62,71,80,103` 是唯一内核：有限域单调膨胀算子在载体基数内稳定并给出最小不动点。`ULM10DungProfiles.lean:67-88` 是特征函数单调性（全仓最难的证明，约十五行）。`ULM10:99` grounded 最小性对 n 归纳，`ULM10:161` grounded 唯一性用反对称，`ULM10:199` preferred 存在性用幂集上 `Finset.exists_maximal`。另有 `ULM05:75` 对 `Run` 归纳、`ULM15:48` 归纳加传递、`ULM13:145` 对依赖类型族归纳。

**委托与改名**（零新数学）。`ULM07:21,25` 转发 `HornFixedPoint:43,60`；`ULM15:126,131,139,146` 四个 Banach 是 Mathlib `ContractingWith` 一行包装且要求 `[CompleteSpace β] [Nonempty β]`；`ULM16` 27 条全是别名，它的作用是给跨仓引用提供稳定名字。

**被旧稿漏报的正面结果**：`BanachComplete.lean:15` 用 `weightedSupDist` 手工构造出真实的 `MetricSpace (Fin n → ℝ)` 实例，四条公理全闭合。但 `CompleteSpace` 全仓无证明，所以仓库内的 Banach 结果接不到这个距离上。

## 结构（13+21 节 → 9 节）

1. 引言（制度事实开头，中文稿见本文件末附录）
2. 方法与声明强度：接口、六个不可表达性的精确定义、三种强度、计数口径
3. 有限单调迭代：唯一内核
4. 两次实例化：Horn 支持闭包与 Dung 语义
5. 主干编码层：请求身份、结果代数、类型图、义务、机器、前提来源
6. 分支查询与程序裁判：proof-carrying 构造子
7. 量纲算术、信任 meet 与保证包络
8. 主干之外的独立理论与缺口：时间、权限秩、污点、加权度量与收缩、DDL 四切片
9. 未证清单与推进顺序；结论与声明

旧稿的"Rosetta Stone"一节降级为第三节里的两三句；六处 countermodels 模板并入第九节；七个外围文件与 FullMath 全部归入第八节并明说与主干只有平行定义、无桥接定理。

## 文风契约

从计算法学正式出版物提炼。段落与句长统计出自上一轮读书报告，**标为报告值、可复核**：段落 150—250 字、3—6 句、一段只做一件事；句长中位 42—52 字，极少超 130 字；分号仅用于并列同类项，约每千字 1—3 次；破折号近乎为零；括号每千字 2—5 次，用途限于缩写首次交代、法条编号、英文原词、图表号。

以下特征是我自己读《计算法学方法初阶》第一章与《AI背景下类案检索方法新指引》自序确认的：开篇先摆既有研究再指出不足（"不过这些讨论也存在不足，一是……二是……"），随后"本章主要解决两个问题"接两个设问；靠制度事实立论（文件全称、生效日、上线日、案例数量、作者承担的课题）；主语是文件、法院、学者、本书，不是"类型""接口""保证"；限定集中放在段末或方法选择处，每章两到四次，**正文判定句是光着写的**；术语用"所谓X，是指……"配脚注权威，或先分叉再收束；逻辑靠"第一/第二/详言之/换言之/由此可见"显式串起。

硬禁止：机器码标识符出现在引言和摘要正文；`rfl`、`cases`、`decide` 等 tactic 名进正文；"本文不主张……"三连排比；Consider first/second/finally 模板复读；把一句话包装成编号展示公式；62 处独立成句的认识论播报（要搬进每节开头的 Scope 框和第九节的声明账本）。

## 已完成的改动

新增文件：`scripts/check_paper_claims.py`（论文声明清单护栏）、`scripts/ci/generate_theorem_manifest.py`（带作用域标签的清单生成器）、`docs/formal-release/theorem_inventory_v3.json`、`tests/test_paper_claims_guard.py`、`tests/test_theorem_inventory.py`、`work/verify_dois.py`（引文核验，未入库）。全量 pytest 144 项通过。

已改 Lean 与文档（**本地未编译，状态 CI_NOT_RUN**）：`weightedSupDist_complete`→`weightedSupDist_separates_points`（陈述是 `d ≥ 0 ∧ (d=0 ↔ x=y)`）；`horn_soundness`→`horn_result_subset_univ`；`horn_result_is_minimal_model`→`horn_result_unique_least_fixed_point`（缺"TH 不动点＝Herbrand 极小模型"这座桥，已写进文档注释）。落点：`WeightedSupNorm.lean`、`BanachComplete.lean:24`、`HornFixedPoint.lean`、`AxiomAudit.lean`、`_axiom_audit.lean`、`AGENTS.md:66`。`build-logs/` 与 `work/final-evidence/` 下绑定旧 subject 的证书**一行未动，也不要动**。

`AGENTS.md` 第 6 条定理计数规则与仓库自身审计互相矛盾：`rg "^theorem "` 在 ULM 范围数出 111 而实际 145，全仓 1409 而实际 1445，因为漏掉同一行带 `@[simp]` 的声明。建议改为引用生成器输出，**改前须征得用户同意**。

`references.bib` 现 46 条、无重复键。40 条英文已对 Crossref 逐条核验为真；Teitelbaum 与 Fenton–Neil–Lagnado 是线上年份与卷期年份之差，note 里已写明。新增 5 条中文，核验强度记在各条 note 里。

## 待办

第二问收尾：抽一份旧稿断言隔离清单（十五份文档里所有数字与强断言），新稿每出现一处须在源码或已核工件里有对应物。

第四问遗留与待复核（子代理报告、我未重验，写作引用前自己看一眼行号）：两套 `ContextKey`（`ULM01:95` 五字段 vs `UnifiedV21/Context.lean:6` 二十字段，`SevenAxis.lean:21` 用后者）；三套平行 Dung 语义且零桥接；两套 `AttackKind`、至少四套优先级；22 个跨文件重名，`isSelfAttack` 并包即冲突；七处把结论写进前提；`AuthorityLattice` 把谓词定义为 `False` 再证 `¬False` 且全文件无格；`CertificateChecker` 只读六个自报 Bool；`canonical_v2` 48 个名字里 11 个无实现；`program/PROGRAM_STATE.json` 写着 `FORMAL_CORE_RELEASED`；`work/full-math/*.json` 被 git 跟踪。

第三问缺口（按能救论文的程度）：ULM10 补 grounded 的 conflict-free/admissible/complete 并绑 `DefeatAF.WellFormed`；`weightedMetricSpace` 的 `CompleteSpace` 与到 `ContractingWith` 的桥；ULM07→ULM08 依赖桥；机器可达性或终止；非单调更新；`combineAssurance` 的代数律；五个零居民合同的至少一个闭合实例；FullMath 公理审计。

第五问必查两条：`build-logs/` 与两个历史 run 的原始工件复核；**juris-calculus 按名引用了哪些定理**（决定改名波及面和回执真伪，目前完全没查）。

## 铁律

本地永不执行 Lean/Elan/Lake。GitHub Actions 是唯一权威，推送或 dispatch 需用户逐轮授权，未授权前构建状态一律 `CI_NOT_RUN`。不得用 `sorry`/`admit`/`axiom` 闭合目标。UNKNOWN/TIMEOUT/SKIP/ERROR 一律 fail-closed。不得为行文流畅删除限定，只能搬家。计数必须绑定具名 subject。AGENTS.md 的 Prohibited Claims 清单逐条适用。中文对用户、英文与代码注释用英文。

## 附录：第 1 节中文草稿（未经复检，引用前按上限逐句校）

> 计算机辅助法律推理在我国司法实践中已经从研究议题变成工作要求。《最高人民法院关于统一法律适用加强类案检索的指导意见（试行）》自2020年7月31日起试行，对类案的概念、检索的前提、范围和方法作出规定〔1〕。2024年2月27日，人民法院案例库正式上线并向社会开放〔2〕。这些制度共同提出一项具体要求：系统给出的结论，必须能够说明它是怎样得出的。
>
> 现有研究大致沿两个方向回应这一要求。一个方向研究类案的识别与比对，讨论如何判断待决案件与已决案件属同类，以及检索结果如何与本案结合〔3〕。另一个方向研究推理的形式性质，包括可废止推理、抽象论证框架与优先级规则〔4〕。两条线索之间存在一个共同缺口：前者关心结论是否可靠，后者关心推理是否有效，而系统实际交付给人的是一次播报。求解器返回什么，评估器认定哪些论证可以被接受，最终把哪一种状态呈现给裁判者，这三步构成播报。播报环节的正确性，既不由类案检索规范保证，也不由论证理论保证。
>
> 本文关注播报失真中的一类特定情形：程序把"尚未查完"说成"主张不成立"。所谓无法表达，是指使用既定类型时写不出违反要求的代码，既不依赖运行期检查，也不依赖文档约定。
>
> 这一要求可以分解为六项。前四项位于本文的主干模型之内。失败不能被映射成正常载荷。声称结果不完备时，必须同时交出一个仍未关闭的义务。扩张族为空时必须交出空性证明，"不存在稳定扩展"因此无法被播报成"主张不成立"。求解不完备不能被改写成不利裁判。后两项位于主干之外的独立理论之中：聚合不能提高保证，其信任向量版本在主干内成立，权限秩版本在主干外；重复提交受污输入不能使之变干净，该理论同样在主干之外。这一内外之别是本文的一项结果，不是叙述上的不便。
>
> 主干模型由十六个 Lean 4 模块构成，含 145 条定理声明。本文对每一条标明它的实际强度，并把限定集中在每节开头交代。三种强度需要区分：类型层面的不可表达；真正的归纳与构造证明，包括对机器运行序列的请求保持归纳、Dung 特征函数的单调性、以及 grounded 扩张作为最小不动点的唯一性；对更早定理或 Mathlib 的转发，末模块的 27 条声明全部属于此类。145 这个数在源码层面可核，构建通过与公理审计另需持续集成绑定指定提交后才能主张，本文的写作状态下该项尚未取得。
>
> 本文不主张实体法律正确性，不主张运行时实现的完整精化，也不主张存在一个统一覆盖发布过程的定理。主干之外的时间与权限理论、以及规模更大的另一套论证语义，与主干之间目前只有平行定义，没有桥接定理。这一缺口在第八节单独列出。

注释对应：〔1〕`SPCSimilarCaseGuideline2020`；〔2〕`SPCCaseDatabase2024`；〔3〕`QiXiaodan2025SimilarCaseSearch`、`DengJinting2021CalcLawMethods`、`JiWeidong2024CalcLaw`；〔4〕`Dung1995`、`PrakkenSartor1997`、`BenchCapon2003`。
