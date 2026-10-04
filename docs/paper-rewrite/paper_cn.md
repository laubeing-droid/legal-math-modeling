# 法律形式化的七层责任体系：一份可核验的分层主张账

**中文主稿**（英文同构稿 `docs/paper-rewrite/paper_en.md` 已落盘，两稿章节逐项对齐，中文稿领先）

**状态**：依据《法律概念总谱》（docs/master-plan/基线/法律概念总谱.md，冻结版）推倒重写；旧论文（播报失真/十六模块组织）已归档 docs/history/paper-v1-cn.md。
**证据纪律**：本文每一处数字与定理断言，均绑定生成工件 docs/formal-release/theorem_inventory_v3.json：计数必须带作用域名与 subject 提交号，且该工件的 `subject_binding.binding` 必须为 BOUND_TO_SUBJECT（标签所指的字节就是被数的字节）；凡本提交尚无授权 CI 运行，一律写 CI_NOT_RUN，不作 PASS，也不继承上一提交的绿。无锚主张不出场；锚缺失即 UNKNOWN。
**文风声明**：本文按作者 2026 年事务所文稿（代理词、再审申请书）文体写作——结论先行、引条引证、证据精确到页、判断句收段。

---

## 引言：法院要的答案，系统必须一句话说清

**结论：法律人工智能的可信问题不在零件，在分层装配与凭条；本文交付装配好的七层整机与它的主张账。**

《最高人民法院关于统一法律适用加强类案检索的指导意见（试行）》自二〇二〇年七月三十一日试行，要求对类案"进行检索并作出说明"〔SPCSimilarCaseGuideline2020〕。二〇二四年二月二十七日，人民法院案例库上线，类案检索从要求变成日常〔SPCCaseDatabase2024〕。法律人工智能研究随之兴盛〔JiWeidong2024CalcLaw；DengJinting2021CalcLawMethods；BuitenEtAl2021〕，论证框架、可废止推理、概率模型的文献汗牛充栋〔Dung1995；PrakkenSartor1997；ModgilPrakken2013；FentonNeilLagnado2013〕。

然而，现有工作有一个共同缺口：**系统给出的结论，凭什么可信到哪一级，说不清。**求解器返回什么、评估器接受哪些论证、最终把哪一种状态播报给裁判者——这三步构成播报，而播报环节的正确性，类案检索的规范不管，论证理论也不管〔BenchCapon2003；Horty2011〕。计算法学的中文文献已反复指出"法律与计算的真正对接点在于可验证性"〔DengJinting2021CalcLawMethods〕；计算逻辑一脉早已备好工具〔ClarkeEtAl1986；CousotCousot1977；Tarski1955〕；机器学习可解释性研究也承认其输出"仅供参考"〔RibeiroEtAl2016；GuidottiEtAl2018〕。缺的不是零件，是把零件按法律语义分层装好、每层挂上凭条的整机。

本文交付这样一台整机，并交付它的主张账。全部工作归纳为三件：

一、**一张七层两横切的总谱。**法律概念一百三十二项（P-001 至 P-132），每项一条定义、一个编号、一个形式化证明目标，分入概念层（L0）、法源层（L1）、要件层（L2）、证明层（L3）、裁量层（L4）、计算保证层（（L5））、交付层（L6），另有经验校准（横切A）与回执（横切B）两条贯穿规矩。总谱已冻结，改动须过三关。

二、**一份分作用域、分强度的定理承载账。**一百三十二项概念，五十七项挂既有定理，七十五项本轮新写。计数按清单工件 theorem_inventory_v3.json 的两个作用域分开报：作用域按文件位置划，`JurisLean/` 子树的 297 个文件（`juris_lean_package`）共 3240 条定理声明；把包外草稿工件一并数入是 3252 条（`all_tracked_lean`，312 文件），其中四个早先体内带 sorry 的目标已改列 UNPROVED、不再充作定理。文件数的跳升（225→296，其后逐针增至 297）主要来自两批外部移植：`JurisLean/External/` 下 40 件是 elazarg/GameTheory@107085bc4 与 elazarg/fixed-point-theorems-lean4@42d4b401f 的字节忠实拷贝（仅改 import 根、加来源头注，门测试逐件比对上游 sha256），承载一般混合策略纳什存在性（`mixed_nash_exists`）、一步偏离等价（`oneShotDeviation_iff_spe`）、Kuhn 双向与 Brouwer/Kakutani 不动点；另有 17 件是 davorrunje/neural-network-proofs@f909425 的**跨 pin 回移**（Leshno 通用逼近 iff 锥，漂移修复逐件记适配日志）；**57 件已由 run 36456965606（subject `c5830ed`）八作业全绿取得完整认定——构建、公理审计（1361 个具名目标、`sorryAx` 零命中、公理词汇仅 propext、Classical.choice 与 Quot.sound）与证书工件已连哈希落盘 `docs/formal-release/ci-evidence/36456965606/`，详见第十章「三缺口的载体对齐」；62 件（四件自家博弈载体、57 件外部移植、ReLUFamily）已分三批进入发布根，各自取得入根认定：批次一 run 36505244239（subject `86384e4`）、批次二 run 36507088206（subject `adaf87d`）、批次三 run 36509407756（subject `a85ba8a`）**。这 296 个文件是否全被 `lake build` 取到，另由根可达性账说话，现算命令是 `python scripts/ci/check_import_reachability.py`：该账现报 289 / 297 模块在根闭包内、10 件记账为独立驱动，未记账的不可达为 0。这 10 件**全部**是 AxiomAudit 等 CI 直跑入口；**待并隔离表已空**——十三件旁支针（含 S2、S3、S6、XU、C1、T2）各自拿到自己的 `changed-module` 构建后才入根，最后三件的 run 号是 `36770138720`（S3）、`36770475007`（T2）、`36772310980`（S6），subject 分别 `c03663cb`、`c03663cb`、`01ce4fff`。发布根的生成根块现 import 十四件旁支——`ClaimBasis`、`Representation`、`SourceNorms`、`InstitutionalEffects`、`PayoffEquilibrium`、`PrecedentFlow`、`Temporal`、`AdjudicationBridge`、`Uncertainty`、`BoundaryClosure`、`Probability`、`FullProcess`、`Unified`——每件都是先拿到自己的 `changed-module` CI 构建才入根；`JurisLean.Seams.ClaimBasis`（P-034 请求权基础链）是第一件，run 36749410410（subject `6a30194d`，`mode=changed-module` 目标）把它编绿后它才由该根块 import。其余六轮的 run 号与 subject 记在 `scripts/ci/check_import_reachability.py` 的隔离表注释里。那些轮次只认定**构建**：审计面后来新增的具名行里含 seam 1 的 32 条定理与⑤⑥的 8 条边界定理，而公理维度已于 run `36774916316`（subject `3106a071`，`event=push`，八作业全绿）补齐——该轮的 `lean-full-clean-build` 以 `lake env lean JurisLean/AxiomAudit.lean` 展开全部 1949 个具名目标，判定工件 `axiom-audit.json` 记 `status` 为 PASS、`audited_targets` 1949、`targets_with_sorryAx` 与 `targets_outside_standard_axioms` 皆为空集，公理词汇只有 `propext`(1418)、`Quot.sound`(1153)、`Classical.choice`(1010)，工件连同摘要已落盘 `docs/formal-release/ci-evidence/36774916316/`。该判定只属于 subject `3106a071`，其后的提交不继承；PASS 的含义限于"这些定理不依赖 `sorryAx` 与仓库自造公理"，不表示命题内容对真实法律成立。`SequentialGames` 曾因头注里的认定经复查从未成立而退回待并，见台账第七十二轮，后于批次一重新入根。289 + 10 大于 297，因为有两件既是独立驱动又被别处 import（BusinessRelationsDelta 与 FullMath.CompletionAudit），别当减法读。分支 ci/mandate-wave1 的 run 36351623739（subject 71d2177bc）已把该认定做成全绿，其后的提交不继承这一判定。强度另立账：132 项概念里 100 项有 Lean 锚、32 项只有 Python 与门测试锚；T 谱 127 个项目标的一般式的闭合数是 0（见第十章）。授权 CI 已于 run 36351623739（subject 71d2177bc）取得全绿，编译与公理判定绑定该 subject；此后写的提交不继承它。

三、**一套回执纪律。**每层输出必须带"可主张等级"：结论级（有证书）、参考级（仅供参考）、不可主张（没依据）。无回执的层，输出自动降为不可主张——这不是措辞约定，是机读账本与类型系统的结构后果。

对以上三件，本文按层分章陈述：每章先给结论，再列定理与证据锚，再交代该层办不到什么。质疑者可以直接翻到第九章未证清单——我们不留情面地列出了自己尚未证成的事项。

---

## 第一章 概念层（L0）：一百三十二项户籍，一项不留黑户

**结论：法律本体必须以第一层身份显式立户，禁止把概念体系吞进任何数据口袋。**

概念层是词汇表。请求权、时效、构成要件、权能、事件——后面每一层的陈述都要用这些词说话，所以词汇最先钉死。第一百三十二项中十项在本层干活（P-001 至 P-010）：概念定义〔LegalMathModeling2026〕、概念-数据同构、法律语言、主体、Hohfeld 八概念、关系状态、语境参数、定性算子、概念版本化、个人信息族。

**定理与证据锚。**Hohfeld 八概念代数：对立与相关两个映射均为对合且无不动点——四条定理（Hohfeld.lean，opposite_involutive 等，公理审计通过）。法律关系状态：Relation 类型携带共同约束（同一损失、竞合互斥、共同消减），非形成性裁判在类型上无法创造关系（LegalModelV2.lean，relation_shared_constraints_participate）。概念版本化：登记版本严格递增，违反即被拒（Genealogy/Part0.lean，P009 命名空间，strictly_increasing_version_enters）。

**边界。**本层只管"是什么、叫什么、怎么定义"。语义解释归第四层，工程户口本（类型注册表五十二类）以 manifest 为唯一权威，本层不复制清单。

---

## 第二章 法源层（L1）：位阶路由，新旧特别冲突不裁决

**结论：法源是地基的供货商；位阶冲突可路由，"新的一般对旧的特别"必须回答 UNKNOWN。**

十二项概念在本层（P-014 至 P-025）：法源类型、效力位阶、效力溯源、溯及力、版本衔接、判例拘束力、管辖、冲突规范与反致、公共秩序保留、准据法选择、案由路由、法域轴。

**定理与证据锚。**位阶路由三定理（Genealogy/Part1.lean，P015）：高阶胜（lex_superior_left）；同阶同日同性质返回 none；**旧特别对新一般返回 none**——机器在这里明确拒绝裁决，把问题留给有权解释者。这不是缺陷，是纪律：法源冲突中有一类依法不可由算法定〔Maher2001；AntoniouEtAl2001〕。反致一跳终止：外法回指即用法院地实体法，链条在函数里走不出第二跳（P021，renvoi_back_uses_forum_and_terminates）。溯及力：时际规则与从旧兼从轻落在 TemporalApplicability.lean 的定理群。

**边界。**位阶类型学本身仍是待立目标（三面皆空在案）——类型学问题，不是路由问题。

---

## 第三章 要件层（L2）：涵摄是算子，请求权要链条

**结论：定性在先、找法在后；涵摄有算子，请求权有基础链，链不完整就没有请求权。**

十三项概念（P-026 至 P-038），承办法官的第一个动作在这里发生：这是什么法律问题、争点是什么、要件怎么拆。

**定理与证据锚。**请求权（原四缺口之首）定理级收口：**主张可用当且仅当基础链要件全满足；未登记的基础返回 UNKNOWN**（Genealogy/Part2.lean，P034，claim_available_complete_iff 与 unregistered_basis_unknown）。涵摄算子：事实归入要件的完备性判定为合同级（ontology_v3，subsume），其 Lean 升级为一般归纳，属未证清单。代理三分：代理归本人、代表限范围、冒名未追认不约束（P035 三定理）。规则与原则二分：规则全有全无，原则只计权重（P063）。

**边界。**涵摄的"一般完备性"是数学问题不是法律断言；类比推理的迁移正当性归第四层裁量。

---

## 第四章 证明层（L3）：举证责任在谁，谁就受益于 UNKNOWN

**结论：证据只动候选集合，不动规范本体；败诉不等于事实为假；未决必须穷尽四类规则才准说。**

十四项概念（P-039 至 P-052）。这一层集中体现对象定义第 2 条的分层纪律：Truth 是规范本体语义，Judgment 是证据可支持判断，**判断不成立推不出真值为假**，除非规范另有构成效果。

**定理与证据锚。**该分层的 Lean 载体：KernelV3.lean 判断三值加真值判断分层见证（judgment_notEstablished_does_not_force_truth_false）。but-for 因果：双向反事实缺一即 UNKNOWN（P047，two_sided_but_for_true 与 one_side_missing_unknown）。证明力：三分量取弱者封顶（P042）。举证时限：逾期不可入，除非有理由的展期（P049）。非法证据排除：清单闭集，列名即排除（P050）。**自由心证边界（原四缺口之二）定理级收口**：内核只供应可采输入、评价行为在内核之外——输出类型上根本没有判断字段（P051，boundary_inputs_complete 与 boundary_records_input_only）。

**边界。**心证如何评价，本系统永不说。形式化边界的正面记录本身就是定理——这是诚实的极限，不是偷懒的借口。

---

## 第五章 裁量层（L4）：解释之争打的是攻防，量刑算的是双线

**结论：多读法并存、互相攻击、判例钉死；量刑规范线与经验线分离呈现，谁也不冒充谁。**

三十八项概念（P-053 至 P-090），全谱最大的一层：可废止论证〔Dung1995；PrakkenSartor1997；ModgilPrakken2013〕、例外与豁免、类比与区分〔RisslandAshley1987；VlekEtAl2015〕、解释五构造子、价值衡量的预序（拒绝全序）、归责原则、责任形态、行为主义全族（谈判、和解、诉讼策略、司法压力）。

**定理与证据锚。**解释构造子分支隔离（P060，isolated_branch_preserved）：五方法各自独立求值，比较只在其后——先隔离再求值，杜绝拉偏架。解释之争：钉死的读法对不高于其先例序的攻击免疫（P061）。漏洞信号（原四缺口之三）定理级收口：检测保持信号名录、输出无续造内容槽（P066）。价值预序：不可比较是合法输出（P064）——两位阶无法排序时系统输出 INCOMPARABLE，不硬排。量刑双线（P071/P072/P101）：规范线=确定性规则表执行，经验线=带证书区间，双线只在宣告步合并。谈判件：ZOPA 存在性判定（P076）、让步单调递减（P077）、调解区间（P078）、和解期望值（P079）。博弈均衡：显式标注"无冲突过滤"语义，永不冒称纳什〔OsborneRubinstein 类结果的引用见英文稿〕。

**边界。**量刑经验线永为参考级；解释的实质权衡归论文不归定理；话术资产只验"不冒充法律事实"（P107）。

---

## 第六章 计算保证层（（L5））：机器自动过的，才挂括号

**结论：金额算精确、期限算日历、概率只从检索母体来；加括号的层是机器自动履行的执行面，不是人工站。**

十三项概念（P-091 至 P-103）。这一层给全栈算的保证：ExactExpr 求值一致性（CPM 金额计算）、RoundingPolicy 进位策略、阶梯构造器、分段利息、抵充守恒、税档累进、迟延利息、智能合约同意锁。

**定理与证据锚。**抵充守恒（P097）：单债不足额全额给付、超额给付结转余款，两债见证 10=6+4+0。酌减（原四缺口之四）定理级收口：clamp 六定理——低于下界夹入下界、高于上界夹入上界、带内不动点、带内幂等（P098 全套）。税档三档切片：每档只税自己的切片（P099 两见证）。智能合约：无同意不转移、非边不转移（P103 三定理）。逻辑-概率单向桥（P114）：演绎蕴含概率一，概率一推不出演绎——反方向定理明写 false。

**边界。**一切数值以 Nat/精确有理承载，禁浮点；真实利率、汇率是外部参数，本层定理不背书其正确性。

---

## 第七章 交付层（L6）：交到人手里的，必须过人闸

**结论：程序流转按合法边走、效应日志幂等、列名动作必经人工闸——机器递刀，人签字。**

四项概念（P-104 至 P-107）。这一层最小，但它是唯一面向用户的层。

**定理与证据锚。**程序处置序：起诉→答辩→质证→驳回/中止/终结，合法边表闭集（P105，disposition_valid_path 与 disposition_invalid_jump）。诉讼标的同一性：案由同加当事人无序同（P106）。话术资产：含法律事实断言即拒（P107）。

**边界。**交付层的验证是"不冒充"，不是"正确"——文书法理质量由第四层供给，本层只管出仓纪律。

---

## 第八章 横切A（经验校准）：检索定母体，胜诉率才算数

**结论：没有母体就没有概率；母体必须由检索实算而来；合成数据永久硬标。**

十一项概念（P-108 至 P-118）。类案检索两层：向量召回只出候选，结构比对精确核对〔QiXiaodan2025SimilarCaseSearch 提供中文实务背景〕；胜诉率三步：检索定母体→母体实算→本案对比〔FentonNeilBerger2016 提供贝叶斯法律证据框架〕；偏离度三参照与倾向分层；**带证书逼近器（军令级）**。

**定理与证据锚。**召回永不充当同构（P108/P109）。方向与翻转见证（P110/P111）：反向无见证即无攻击证。胜诉率管线（P112/P113）：五要素事件定义+不可识别即 UNKNOWN 硬编码。带证书逼近器（P118）：proof-carrying 准入——q 小于一、误差界不超容差、适用域非空、迭代数为正，全部成为构造期证明义务；无证书即无准入（BanachCertificateV3 五定理）〔Banach1922 提供不动点原始文献〕。

**边界。**经验输出恒为参考级；胜诉率是模型相对的后验质量，不是案件胜败的保证；文本相似工具输出封顶候选级（P117）。

---

## 第九章 横切B（回执）：没有回执的层，无权说话

**结论：七层×七回执域授权表机读化；无回执层输出自动降为不可主张；主张清单逐条机读并配漂移门。**

十四项概念（P-119 至 P-132）。回执是贯穿全谱的凭条纪律：谁签发、依据什么、能主张到哪级。

**定理与证据锚。**UNKNOWN 保持与三层准入闸门（P119/P120，既有定理群）。防幻觉：列名模式即阻断（P125）。防概念偷渡：跨法域未适配即阻断（P126）。引文核验：逐字前缀比对（P127，降级注：前缀而非任意子串，诚实记录）。正当程序三元素映射（P128）。生命周期边表（P130）。幂等效应日志（P131，空日志重放幂等+既有命令不覆盖见证）。人闸表（P132）：列表动作必经其闸。

**边界。**回执证明绑定，不证明真理；四十九格授权表起步时四十一格 NO_RECEIPT_PENDING——保守起步是纪律，不是缺陷。还有一桩范围事实必须讲在前头：裁决 6 定下的授权表只有 L0–L6 七层乘七回执域，两条横切不是层、在表里没有行；它们的通道上限因此记在同一份账本的 `crosscut_grades` 里（横切A：经验输出与检索母体率 REFERENCE，合成数据与不可识别目标 NOT_CLAIMABLE；横切B：无回执、引文未核、幻觉模式、未适配法域、人闸未过一律 UNCLAIMABLE），由 `theory/spec/receipt_ledger.py` 逐通道声明并校验上限，未知轴或未知通道直接抛 LedgerDefect；口径必须说全：**“取最弱引用域封顶”只在层侧实现，横切侧目前只有声明与校验，还没有消费方**，门测试因此禁止本段把封顶写给横切。所以“每层每句输出带可主张等级”这句话现在是两段机器可读事实的合取：七层看 49 格授权表，两条横切看 `crosscut_grades`；两者都由门测试对齐论文用词，改一处不改另一处就红。

---

## 第十章 未证清单与声明账本：我们还没证成什么

**结论：一台可核验的机器，必须同时交付它办不到什么的清单；不出这份清单的，才叫不可信。**

**未证事项（压实后重排，2026-09-25 深夜九轮问后）**：
一、T01–T127 目标谱定理级展开——**载体已落地，一般式未闭合**：四批 131 条定理给满 127 个 T 位；覆盖账 theory/spec/lh_alignment/t_p_coverage.jsonl 已改由 scripts/ci/generate_t_coverage_ledger.py 从 Lean 源机械生成，逐条填上锚定定理名与强度档（GENERAL 13 / DEF_PROJECTION 36 / WITNESS 82，只数 EXACT 锚），并如实记 127 条全部带降级注、40 条明写“完整陈述仍缺”。**达到一般式的 T 目标数：0/127**。**另一栏同页可读**：卷覆盖账现记 `general_form_carriers = 12`，即 12 个 T 位已带至少一条 EXACT 的一般式证明；闭合栏仍为 0，因为覆盖口径还要求该块把降级注清空。两个数各说一件事，不得互相顶替。上一版覆盖账曾把 127 行全标 FULL 而其中 124 行未填任何定理名，该口径作废；T112（量刑双线）曾误锚在解释构造子定理上，已撤。
二、~~P-083 排序全局降序正确性~~——**已于本轮压实**：插入排序一般式四定理全链落地（GENERAL-A 单步插入增一/GENERAL-B 长度守恒/GENERAL-C 插入保持降序/GENERAL-D 排序输出恒降序，General.lean，CI 运行 36258901155 于 commit bd364c5 全绿）；此前授权的见证级退半步随之关闭；
三、军令四件都已有 Lean 载体，但**各自的剩余缺口没有一并抹平**：胜诉率三步管线闭合第二步（母体计率）与区间对象；第三步原先记为"要有带逐案裁判日期的真实语料才谈得上实证区间"，该前提本轮被本地交付件 WAVE-ALL-001 证伪——它 159,507,974 行里每行都带 `judge_date`。据此新写 `theory/spec/wave_cohort_probe.py`，把一条有日期的队列（`case_class` 为民事案件且 `trial_prog` 为民事二审，事件为 `case_result` 含"驳回上诉"）流式喂进仓库既有的 `unified.win_model` Beta 后端：2756 行有日期的队列里 2303 行填了结果，其中 1439 行命中，实现频率 1439/2303 = 0.624837，后验区间 [10146599/16777216, 10811301/16777216]（约 0.6048–0.6444），全部聚合量见 docs/formal-release/wave_cohort_probe.json。等级仍封顶 EVIDENCE_WITH_PROVENANCE_CAVEAT，四条边界写在工件自己身上：切片是分片文件序前缀不是随机样本、453/2756 行未填结果且从不补值、"驳回上诉"是文本匹配不等于胜诉度量、交付件未声明使用条款（R-08）；类案已有结构不变量与"合并不掉、换名不掉"的分离定理；本轮另立 `CaseIsomorphism`，把同构定义为保关联的双射并证其为等价关系、给出"全自环与全不自环不同构"这条负例，并附一个可执行的三槽候选判定（`triedRenames` 列举 `Equiv.Perm (Fin 3)` 的六个元素逐一试验，`isoRel3_allLoops_self` 与 `isoRel3_allLoops_noRelation` 两条 `decide` 一真一假，`noRelation_ne_allLoops` 在关系级证不同构），**枚举这一步本轮已由计算证下**：`triedRenames_complete` 说 `Equiv.Perm (Fin 3)` 的每个元素都在所列六条里，`rel3Iso_iff_by_list` 说把关系定义换成「所列六条之一保关联」既不加强也不削弱（`Equiv.ofBijective` 把任意双射送回列表）。**最后一寸本轮也补上了**：`bool_beq_true`（四条封闭 case，不赌 simp 集）加 `pairs3_all_mem` 得到 `preservesR_iff`，于是 `isoRel3_iff` 成立——可执行测试与"保关联双射"的定义**双向一致**，`not_Rel3Iso_allLoops_noRelation` 更把一条 `decide` 出的 `false` 读成不同构定理。**范围限定在三槽**：六值枚举与四 case 分片都不对 `Fin n` 成立，不得写成"一般可判定"（R-09 于三槽闭，认定绑 run 36333310003 / subject 4a1d109）；证书逼近器那条有理比线性压缩的误差界仍在原地；本轮另立 `Mandate/ReLUApprox.lean`，为**一个两层 ReLU 网络**给出由模块自己从权重行算出的稳定性界：`h1 = relu (x1 - x2 + 1)`、`h2 = relu (-x1 + 3*x2 + 2)`、`out = relu (2*h1 + h2)`，常数 `lip = 2*(1+1) + 1*(1+3) = 8`，且对任意输入，坐标扰动不超过 `E` 时输出差不超过 `lip·E`，并由 `out_not_constant` 说明它不是常函数（认定见 run 36344882459 / subject 1b6a8d6a9）。**不主张**最小常数、其他范数或任意宽深——那是一例可算界的边界；**族结论**已由外部载体闭合：Leshno 通用逼近 iff（`leshno_dense_iff`，run 36456965606 / subject `c5830ed`）加 ReLU 实例化（`relu_dense`、`relu_dense_iff` 等 13 条，run 36468808532 / subject `3f44b8e`）给出「有限和 ReLU 脊单元在紧集上一致逼近连续函数」——实例化引用载体、未自建论证（R-07 从"已立一例，族结论仍缺"改写为"一例可算界自持、族结论由外部载体认定"）；博弈论有有限扩展式树与两人零和纯策略值，本轮又添一个被完全证明的**混合策略**纳什均衡：`Mandate/MixedPennies.lean` 由四格导出猜正反的期望收益并展开为 `1 - 2p - 2q + 4pq`，对**全体**有理混合证 `(1/2, 1/2)` 互相最优、值为 0，并证同一博弈无纯策略均衡（认定 run 36351623739 / subject 71d2177bc）。零和一支本轮落成一般式：`Mandate/ZeroSumSion.lean` 以 `stdSimplex ℝ (Fin (m+1))` 与 `stdSimplex ℝ (Fin (n+1))` 取两侧混合策略集、以双线性期望取收益，逐项 discharge 非空、紧、凸、两侧半连续与拟凸凹共十项假设，证得**任意有限两人零和博弈在混合策略下有鞍点**（认定 run 36372895460 / subject fea48d9；入根另由其后一轮构建认定）。这条只覆盖零和，不越到非零和或多人——但那两格的缺口自此不再由本仓自建论证填补：一般混合策略纳什存在性与序贯解概念（一步偏离等价、Kuhn 双向）已改由外部文献载体承载并取得 CI 认定（`mixed_nash_exists`、`oneShotDeviation_iff_spe` 等，run 36456965606 / subject `c5830ed`，字节忠实移植、逐件 sha256 来源门，见第十章「三缺口的载体对齐」），不是从零和鞍点外推——零和支与 Sion 路线自此只是本仓自立的工程先例，不再充当一般存在性的替代物（R-02b/R-03 的缺口由"无载体"经"载体已认定"至终态：载体认定 run 36456965606、入根 run 36505244239 与 36507088206，全链闭合）。旧的 `BanachCertificate.lean` 仍自陈 certificate schema only、`verifyCertificate` 恒真，本轮不改写它，只是把主张的位置交给新模块并留此说明。博弈树取**二元选点**模型（编译器逼出来的选择，不是模型的自然形状）；n 元"任选其一"由 `ofList` 编码回到表层，空选、首选项与"多加选项不降值"三条事实以定理形式归还，并注明这是关于编码的定理而非 `Tree` 原生的多路节点（R-11 已闭）。概率是例外：真数学在 FullMath/Probability（Brier 恒等式、污染界、有限后验归一），〔本轮更新：分支 ci/mandate-wave1 已由 scripts/ci/check_import_reachability.py 把它并入库根（FullMath/All.lean + 根可达性块），并随发布根由 run 36322009701（subject fc43a92）建绿：该轮证书源清单含 FullMath/Probability 13 件与 BusinessRoot/Analytics 1 件〕；公理审计面当前在源上是 2652 行 `#print axioms`、去重后 2598 个具名目标（按该总数所绑的 subject 计；发布根 `AxiomAudit.lean` 在现源上独占 2014 行，那个 subject 上是 1414 行，差额是此后生成的旁支面；其中军令层具名 280 条（`grep -c '^#print axioms JurisLean.Mandate.'` 现算，24 件各至少 5 条，ReLUFamily 的 13 条随隔离首编译机制入面）；行数的跳升（927→1637）来自外部移植件——审计面为 `JurisLean/External/` 新增了第三块生成面（697 个具名目标，含神经回移 17 件），块内四条头条定理随外部件一起已由 run 36456965606（subject `c5830ed`）八作业全绿取得完整认定，公理审计原文随该轮工件落盘、可重读，见下文「三缺口的载体对齐」——认定属该 subject 的字节，入根另论；这 280 条里有 76 条属四件博弈载体（`SequentialGames` 9、`ZeroSumValue` 15、`PureNash` 27、`OneShotDeviation` 25），它们经 run 36409348921（subject 649d0fd）全绿构建编过，并由该轮落盘的公理审计原文逐条具名（664 个具名目标，`sorryAx` 零命中，见 docs/formal-release/ci-evidence/36409348921/axiom-audit/axiom-audit.raw.txt）；这四件已随入根批次一进根并取得认定（run 36505244239 / subject `86384e4`）；计数只数 git 跟踪的 `.lean`，`.lake/packages` 里第三方源的同名行不算），整条统计线（FullMath/Probability 13 文件与 BusinessRoot/Analytics 共 70 条）与军令 24 件都在面内；其公理结论已由 run 36351623739 落盘的审计原文给出（该 subject 上落盘原文 570 个具名目标 = 源侧 `grep -c` 的 570 行，公理词汇仅 propext、Quot.sound、Classical.choice，sorryAx 零命中；此后的提交另计）——此前 CI 只把该输出上传而不读，读它的门是 scripts/ci/check_axiom_audit_log.py。另：量刑规则表槽位（DATA_SLOT_READY）结构就绪、真实表属外部数据。**〔本轮更新，分支 ci/mandate-wave1；军令层现由 280 条 `#print axioms` 具名，这是当前源侧计数、不绑定任何 run；run 36344882459（subject 1b6a8d6a9）认下的是该轮 ReLUApprox 那 9 条，彼时军令层具名 162 条〕**四件已在该分支补写 Lean 定理：胜诉率第二步（率在有母体时存在、无母体时不存在、加胜诉不降、加败诉不升，Mandate/CohortRate.lean）；类案结构对比（争点码与要素码完全相同而关联边 3≠1 的具例，签名对其分离且该分离在任意合并与任意换名下保持，Mandate/StructureInvariants.lean）；带证书逼近器（n 步迭代闭式、界由模块算出而非由调用方作为字段带入、准入判据与实跑误差等价，Mandate/DerivedCertificate.lean）；博弈论（有限扩展式博弈树与后向归纳值的最优性，Mandate/GameTree.lean；但仍是单人序贯最大化，纳什均衡存在性未动）。另新增对已发布载体的判定式定理：法源准入三档外延（Mandate/SourceRank.lean，取代一条 f k = f k 的自等）、人闸表单值注入（Mandate/GateTable.lean）、引文包含关系与前缀关系的关系面（Mandate/SubstrAdmission.lean，补上 Python 用子串、Lean 证前缀的双侧缺口）。四件与三件升格初落时未入根、未入公理审计面、未挂 p_registry 锚点（CI 编过之前不进正文主张）；后已随发布根多轮晋升全部入根并经各自构建认定（R-01b 一轮 15 件起，`python scripts/ci/check_import_reachability.py` 现算可达性）。
四、涵摄完备性、八处降级、六类边界界定定理——**部分已于九轮问压实**：25 条新定理（General.lean+Boundary.lean，CI 验证）；P127 左插命题被最小反例关闭并登记，右扩张修正版已证；第 5/6 类边界经指针压实（consensus_does_not_escalate / repetition_does_not_clean / majority_cannot_clean）；
五、检索第一层向量引擎——**已于九轮问压实**：确定性 TF-IDF 余弦引擎落仓（vector_engine.py，8 条门测试：归一化不变/自相似/对称/确定性排序/候选级封顶），零依赖纯 Python。

**声明账本**：作用域 `juris_lean_package` 3240 条定理声明、作用域 `all_tracked_lean` 3252 条，均绑定清单工件 theorem_inventory_v3.json（subject 及其 subject_binding 记在工件里）。公理审计的实际覆盖面是 2223 个具名目标（`#print axioms` 共 2277 行），不是全部声明；本轮由 scripts/ci/generate_probability_audit_surface.py 把原先进不了审计面的统计定理、军令层定理与外部移植件生成式纳入（该 subject 源上军令具名 173 条（本轮为 280 条））。编译与公理判定绑定 run 36351623739 及其 subject 71d2177bc：`lean-full-clean-build`、发布证书（220 文件 / 1932 条声明）与独立校验均为 success；该判定只属于那一个 subject。计数成分也要交代：按 declaration_shape_report.json 声明的两条句法规则实测，`JurisLean/` 树内 3240 条定理声明里，一行式契约搬运 431 条（形如 `theorem 别名 : 契约名 := 证明名`，计数诚实、但不含数学内容），结句中不绑定变量的 1244 条；两条规则可交叠，故不可相加。此处此前写作 433 与 791，而仓库里没有任何脚本能复现其判据，本轮起改用有工件、有门测的实测值。本文未主张：整部中国法已完备形式化；神经逼近器输出可当结论；T 谱已闭合。系统使用者看到的每一个结论，都能沿回执追到其证据等级；对后续施工，T 谱覆盖账就是推进顺序本身。闭合形态另立一账（只说证完用了什么项，不评判命题价值）：全仓 3240 条定理声明里，287 条由单一反射项闭合、102 条由纯 decide 闭合、其余 3228 条含 tactic 过程；逐文件名单在 trivial_proof_census.json，三类相加恰等于总数由门测试核。

### 三缺口的载体对齐

**结论：三条证明级缺口（R-02b/R-03 的一般混合策略纳什与序贯解概念、R-07 的通用逼近一族）不再自建论证——owner 于 2026-09-28 定案改道外部文献载体；载体与实例化均已取得完整 CI 认定：57 件外部载体由 run 36456965606（subject `c5830ed`）八作业全绿认下，ReLU 实例化 13 条由 run 36468808532（subject `3f44b8e`）认下，两轮证据字节均已落盘可重读；62 件随后分三批进入发布根（批次一 run 36505244239、批次二 run 36507088206、批次三 run 36509407756，各轮全绿），该波隔离表清空——三缺口从载体到根全链闭合，全程无自建论证。**

改道依据是 owner 2026-09-28 指令：数学证明统一由文献载体承担，本仓不自建证明孤岛（literature-first）。缺口①②由同 pin 字节忠实移植承载：`elazarg/GameTheory@107085bc4`（MIT）33 件，头条为一般混合策略纳什存在性 `mixed_nash_exists`、一步偏离等价 `oneShotDeviation_iff_spe`、Kuhn 双向与 Minimax；`elazarg/fixed-point-theorems-lean4@42d4b401f`（MIT）整库 7 件，含 `brouwer_fixed_point` 与 `kakutani_fixed_point`。两笔修订的 `lean-toolchain` 与 `lake-manifest.json` 都钉 `leanprover/lean4:v4.30.0` 与 mathlib `c5ea0035`，与本仓逐字节同 pin；每件只加可剥离的来源头注、把 import 根改写为 `JurisLean.External.*`，门测试 tests/spec/test_external_port_provenance.py 从仓内文件反推上游字节、逐件比对 PROVENANCE.json 记录的 sha256——「除头注与 import 外零改动」是被检查的性质，不是口头承诺。

缺口③的载体是跨 pin 回移：`davorrunje/neural-network-proofs@f909425`（Apache-2.0）的 Leshno 依赖锥 17 件，头条 `leshno_dense_iff`，即 Leshno–Lin–Pinkus–Schocken 1993 的 iff 刻画（M 类激活稠密逼近，当且仅当其几乎处处不是多项式）。同 pin 对它不可行：该库生于 mathlib v4.32.0-rc1，不存在本仓 pin 期的修订，这一点已逐件核过；锥内 29 个 Mathlib import 在本仓 pin 的 mathlib 里路径全部存在，import 面零改动。字节忠实不是它的不变量：PROVENANCE.json（neural-backport-provenance-v1）逐件记上游 sha256 与适配日志，门测试核「adapted 标志等于重构比对的现实、漂移件必有非空日志」。至今恰好一条适配——SmoothEngine.lean 在一行 `rwa` 之前补一行 `beta_reduce`，原因是 v4.30 不把 `congrArg` 的 λ 做 β-归约而 v4.32.0-rc1 会；语句与其余证明行零改动。ReLU 实例化有意不在回移里，而是另立引用 `leshno_dense_iff` 的仓内模块 `Mandate/ReLUFamily.lean`：relu 连续故入 Leshno 类 M、非几乎处处多项式，经载体自带的桥接引理得 `relu_dense` / `relu_dense_iff` / `relu_not_isAEPolynomial`，共 13 条定理，已由 run 36468808532（subject `3f44b8e`）构建并过公理审计（零 `sorryAx`、公理仅标准三元组）——实例化引用载体、未自建论证。

诚实状态：run 36451514398（subject `c556f04`）先给出编译面事实——57 件外部载体首次整体编过、同轮公理审计通过（1361 个具名目标、`sorryAx` 零命中、公理词汇只有 propext、Classical.choice 与 Quot.sound），但该轮 `python-gates` 因定理清单时序红、run 整体判 failure。其后 run 36456965606（subject `c5830ed`）八作业全绿取得完整认定：证书、公理审计原文与全部工件已连哈希落盘 `docs/formal-release/ci-evidence/36456965606/`（18 个文件、461487 字节、`digests.json` 记逐件哈希）。ReLU 实例化的认定随后由 run 36468808532（subject `3f44b8e`）给出（八作业全绿，工件同样落盘），三缺口载体链就此闭合。两轮认定都只覆盖各自 subject 的字节，此后的散文与头注改动不属判定内容；57 件外部载体加 ReLUFamily 已分三批进入发布根并取得各批的入根认定（run 36505244239 / 36507088206 / 36509407756），那些批次清空的隔离表（PENDING_CI_MODULES）此后又记下五件自身尚无构建认定的旁支（`AdjudicationBridge` S2、`Probability` S3、`FullProcess` S6、`BoundaryClosure` C1、`Uncertainty` XU），**这五件已在 2026-10-01 各自取得单模块构建绿后全部出账**；同一天表里又记入一件（`Seams/BoundaryBridge5`，⑤ 桥针：本地 2964 作业绿后，由 run `36805877201`（subject `1eef93d7`）单模块构建绿，随即入根并撤销审计面 holdout，**故它现已出账**），记账不可达因此只剩 10 件 CI 直跑入口件（后者住在独立驱动表，`python scripts/ci/check_import_reachability.py` 现算为准）。文献谱系与逐条核验记录在 docs/master-plan/04_文献谱系_法律与数学.md 与 docs/master-plan/05_文献谱系_形式化与复验.md（含对两库 pin 与许可的逐字节复核附录），本文照单引用、不在此重复。

此致
每一位按行核过的人。


---


---


---


---


---


---


---


---


---


---


---


---

## 派生记账段（3751 口径，生成器直读工件重算，勿手改）

本节由生成器从工件直读重写，**取代上文一切旧的计数与形状读数**。落笔前核实两件事：
三类闭合形态之和恰等于总数；清单、闭包账与形状账三方对声明总数的读数一致。任一不成立即拒绝写。

**作用域读数**（均取自 `theorem_inventory_v3.json`）：`juris_lean_package` 3617 条定理声明、306 个文件（`theorem_inventory_v3.json`）；
`all_tracked_lean` 3629 条、321 文件（`theorem_inventory_v3.json`）。两作用域的包内审计面在源上是 2652 行 `#print axioms`（`theorem_inventory_v3.json`），
去重后 2598 个具名目标（`theorem_inventory_v3.json`）；全仓侧与包内同读数：2652 行、2598 个具名目标（`theorem_inventory_v3.json`）。
审计驱动文件 `AxiomAudit.lean` 独占 2389 行（`theorem_inventory_v3.json`），军令层现由 280 条具名目标构成。
2652 条命令去重得 2598 个具名目标（同一目标可在多处被点名），其中 2389 条来自 `AxiomAudit.lean`，余下 263 条在别的驱动里（`theorem_inventory_v3.json`）。

**闭合形态**：全仓 3617 条定理声明中（`theorem_inventory_v3.json`），287 条由单一反射项闭合、102 条由纯 decide 闭合、其余 3228 条含 tactic 过程（`theorem_inventory_v3.json` 与 `trivial_proof_census.json`）；其中一行式契约搬运 431 条（`theorem_inventory_v3.json`），结句中不绑定变量的 1244 条（`theorem_inventory_v3.json`）。
交叉核对：包内 3617 条定理加 134 条 lemma，恰等于计入声明总数 3751（`theorem_inventory_v3.json`）。

**本节不改变任何主张的强度**，只说明"数了多少、用什么项证的"。根扩大是因为七件模块各自拿到
changed-module 认定后入根；构建面由 `lean-full-clean-build` 判绿认定，公理维度仍是 `CI_NOT_RUN`。
