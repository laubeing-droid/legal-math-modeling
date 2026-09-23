# 论文重写施工进度

本轮（2026-09-23，第二批次）：wave4 计算法学七册已由 8 个子代理全文通读（德国书拆两半），维度框架从用户提出的 5 维扩至 13 维，证据合成落点为网盘 `legal-math-evidence/wave4-evidence.md`（含维度×书证×仓库对应矩阵、六类不可表达性的法学背书表、五类形式化边界、八条结构性结论；因含商业书逐字引文不入库）。完整逐条引文报告在本轮会话记录中。下一轮：用该证据库重写"法律统一数学模型"方案与 GPT 提示词，并续写论文第 4 节。

本轮（2026-09-23，第一批次）：完成第 1、2、3 节中英双版，落点 `paper_cn.md`、`paper_en.md`（中文在前）；并完成对上一轮产出的翻车审查（见下节）。

## 上一轮产出翻车审查结论（2026-09-23 补验）

**坐实的翻车点（3 处）：**

1. **主张上限中 85/94 口径错配（实质性错误）**。85/94 可复现，但复现口径是"全部前缀的去重 `\label` 共 94 个，其中 85 个从未被 `\eqref` 引用"，85 里含 12 个 sec:/thm: 等非公式标签；按其标题"编号公式"的正确口径应为 **73/82**（去重 eq: 标签 82 个，从未被引用 73 个；12 处 `\eqref` 全部可解析）。**新稿禁用 85/94；若需引用改用 73/82 并注明口径。**另：两份 markdown 旧稿有 120 个 `\tag` 编号公式、零交叉引用，此事实可用但与 85/94 无关。
2. **HANDOFF"数学已经证明了什么"一处失实**：说内核"稳定并给出最小不动点"。源码核对：`FiniteMonotoneIteration.lean`（10 条定理）只证稳定性与停点，无最小性定理；最小性在 Horn 实例化（`HornFixedPoint.lean:60` 起）与 Dung 实例化（`ULM10DungProfiles.lean:99` 起）各证一次。第 3 节已按源码写。
3. **WeightedSupNorm.lean 模块头注释与重命名自相矛盾**：定理已改名为 `weightedSupDist_separates_points` 且定理级注释明说 CompleteSpace 未建立，但模块头注释仍写 "Proves this is a complete metric space"。属上一轮重命名漏改的文档残留（Lean 文件，本轮未动，待授权修正）。

**第 1 节草稿审查**：一处硬违反（末段"本文不主张"三连排比，属文风契约硬禁止项，已改写并搬入范围框）；其余逐句对上限复核通过，两处日期（2020-07-31、2024-02-27）在 references.bib 注记中有逐字核验记录。

**复核通过、未翻车的上一轮断言**：145/111/27/4 计数与双向零差集（清单工件+两审计驱动）；三处定理重命名落点与陈述（WeightedSupNorm/BanachComplete/HornFixedPoint，Herbrand 桥缺口的文档注释在）；`BanachComplete.lean:15` 手工构造 MetricSpace 实例、字段全闭合；FullMath 全子树 `#print axioms` 0 命中、11 个文件用 noncomputable/Classical/choose（64 文件，含子目录）；references.bib 46 条无重复键；AGENTS.md:66 落点正确（WeightedSupNorm 表行）；全量 pytest 144 项通过。

**待复核清单抽查（全部坐实，可供第 8/9 节引用）**：两套 ContextKey（ULM01 五字段 vs UnifiedV21/Context.lean 二十字段，SevenAxis 用后者）；AuthorityLattice 把 `autoMechanismReceiptValid` 定义为 False 再证其否定、全文件无格（AuthorityLattice.lean:20-27）；CertificateChecker 的 `checkCertificate` 恰好只读六个自报字段（wellFormed、status、evidence.kind、evidence.verified、requiredFactsPresent、proofObligationsPresent，其中四个 Bool；"六个自报 Bool"措辞略松）；`program/PROGRAM_STATE.json` 写 FORMAL_CORE_RELEASED 且 lean_full_build=COMPLETE（与 CI_NOT_RUN 纪律冲突，新稿禁引）；`work/full-math/*.json` 2 个被 git 跟踪；`isSelfAttack` 在 AttackDecision.lean 与 TypedAttack.lean 两处重名。

**我方稿件的自我修正（本轮已改）**：§1"这一要求可以分解为六类"改为"这类失真在本文中落实为六类"（指代修正）；§2"任何后续变换"收敛为"主干定义的结局映射"（过度表述）；§2 范围框第五/六类文件归属消歧。

## 本轮已核工件与读过的源码

- 工件：`theorem_inventory_v3.json`（2026-09-23 两次重生成，现行 subject 1e0875c；计数 145/111/27/4 始终一致）、`ULMAllTheoremsAxiomAudit.lean`（145 目标）、`ULMCoreCompAxiomAudit.lean`（27 目标）、`paper/references.bib`（草稿所引 8 条逐条查注记）。
- 源码：FiniteMonotoneIteration、HornDefinitions、HornFixedPoint、ULM01–ULM16 全部 16 个编号模块、ReceiptAuthority、TaintNoninterference、TemporalKripke、DDLDefinitions、ArgumentSemanticsRegistry、BusinessRoot/SevenAxis。
- 两本书指定部分原文已读：《计算法学方法初阶》第一章开头、《AI背景下类案检索方法新指引》自序（书目在用户私有蒸馏工作区，路径不入库）。
- wave4 计算法学七册已全文通读并合成维度证据库（十三维框架+行号锚点）。该证据文件含商业出版书籍逐字引文，按 `docs/disclosure/PUBLIC_PRIVATE_BOUNDARY.md`（第三方材料无再分发依据默认不入库）**不进仓库**，存用户同步网盘 `legal-math-evidence/`；论文引用其结论时须回查原书。

## 写作约定（沿用）

- 每节 = 范围框（blockquote）+ 正文 + 节末声明对应表；定理名/文件行号只进表，不进正文；tactic 名全文不出现。
- 计数口径固定在第 2 节末段：145/111/27/4，绑定清单工件；构建状态一律 CI_NOT_RUN。
- `scripts/check_paper_claims.py` 按旧语料布局写死（要求 paper/main.tex），对 `docs/paper-rewrite/` 不可直接运行；本轮以人工逐项扫描替代（禁印数字、字号、法答网日期、mutation 措辞、机器码，全部零命中）。
- 第 4 节起可用贯穿实例：`TemporalKripke.lean` 的 litigation_timeline、`DDLDefinitions.lean` 的 contract_breach_direct_violation_shape 与 license_permission_not_direct_violation。

## 测试

`python -m pytest tests/test_paper_claims_guard.py tests/test_theorem_inventory.py -q`：13 项通过。全量 pytest 见 HANDOFF"已完成的改动"（144 项）；本轮只新增 docs 下 markdown，未改任何代码与 Lean 文件。

## CI 修复记录（2026-09-23 第三批次，授权执行）

- run 35819869335（subject 2d06da6）结果：`lean-full-clean-build` **SUCCESS**（改名三条定理的 Lean 编译绿证首次取得）；`python-gates` **FAIL**，`test_theorem_inventory` 报 137 个 .lean 文件哈希失配；`seven-axis-acceptance`/`final-gate` 为 artifact 级联失败。上一绿 run 35124268367（subject 5084f25）时清单工件与该测试尚未入库。
- **机制（实测钉死，修正早前"blob 为 CRLF"的误判）**：仓库 blob 一直是 LF（`git ls-files --eol` 索引侧全 `i/lf`，`i/crlf` 计数 0）；故障在于 Windows 工作树有 67 个 .lean 为 CRLF 字节，生成器按磁盘字节记 sha256，清单固化了 CRLF 哈希；CI Linux 检出为 LF，字节不同即失配。本地 verify 通过与 CI 失败的矛盾由此解释。
- 修复动作：按 `.gitattributes`（`*.lean text eol=lf`）把 67 个工作树文件刷为 LF（blob 零变化、Lean 内容零改动），在 subject 2d06da6 重生成 `theorem_inventory_v3.json`（137 行哈希更新；计数 145/111/27/4 与审计目标数全部不变），`--verify` 通过；论文头部与本文档的 subject 绑定同步改为 2d06da6。
- 教训入规：生成哈希类工件前必须先 `git ls-files --eol` 确认工作树行尾与属性一致，否则工件会把平台脏字节固化。
- **第一轮修复后复跑仍红（run 35832550717，mismatch 从 137 降到 2）**：`_check.lean`（BOM+单处 CRLF）与 `DungDefinitions.lean`（48 处 CRLF 混合行尾）是 `w/mixed`，第一轮刷新名单只筛了全 CRLF 的 `w/crlf` 而漏掉混合型。第二轮按"非 `w/lf` 即刷"处理（共 2 文件，blob 零变化），在 subject 1e0875c 再次重生成清单；新增强校验：200 文件磁盘哈希 = HEAD blob 哈希 = JSON 记录值三方全等（0 失配），这是 CI Linux 检出的本地等价判据。论文绑定同步推进到 1e0875c。
