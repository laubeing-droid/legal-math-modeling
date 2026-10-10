# W2-B 24 项三态分类 ＋ W2-A 打包侦察（分包 J · 分析交付，非施工）

> 分支 ci/unified-construction-20261008；本文件只读分析产物，供主控审阅后自行入仓。
> 仓库根：`D:\Codex\1.法律工作区\legal-math-modeling工作区\legal-math-modeling`（下文引用一律仓库相对路径）。
> 依据：施工方案 W2-B 段 `docs/master-plan/20261010_统一法律数学模型_连续与语义全量施工方案.md:78-82`；
> 评审第 8/12/13 条 `docs/master-plan/20261010_接续方案评审_Codex_R1.md:60-64,98-108`；
> 红线 `docs/spec/20261007-统一法律数学模型_附录I_Lean施工明细.md:504`（改错配合同及别名绑定，不改原需求）与
> `:723-724`（禁换弱目标、禁删必需输入）。
> 本分类是**分析判定，不是证明**：①类仍需施工包逐项交付六件套后才算闭合。

---

## 一、口径与来源

1. **24 项清单来源**：`docs/full-math/BINDING_217_and_60.md:320` PARTIAL-B 明列
   `F03, F05, F06, F07, F08, F09, F10, F11, F12, F13, P03, P06, P07, N01, N02, N03, N10, B01, B07, G01, G05, C01, EXT03, EXT06`＝**24 项**，
   构成＝20 个 F/P/N/B/G/C 目标行（PARTIAL 且评注为"仅组件"或"错位"）＋2 个 EXT 弱映射行（EXT03/EXT06）。
   本分包按绑定表逐行重数（第 2 节行 26/28–36/40/43/44/52–54/61/62/68/69/73/74/83/86），**合计恰为 24，与 §4.1 口径一致**。
   其余 PARTIAL 行中 134 项属 PARTIAL-A（需求别名，归 W2-A，不属本表）；60 针侧 PARTIAL 已由针补强波收官（`BINDING:327-330`）。
2. **原目标文本出处**：F/P/N/B/G/C 项取 `tools/full_math/spec/TARGETS_57.json` 的 `original_statement`
   （抽核 22 项，`statement` 与 `original_statement` 逐字一致，即登记表未区分原始/当前合同）；EXT03/EXT06 无独立
   statement 字段（`tools/full_math/spec/EXT_9.json` 只有泛句 acceptance"产生具体算法、独立语义、证明、反例与实际证据"），
   原目标回 `docs/full-math/MATHEMATICS_SPEC.md` §3（:63-80）/§9（:182-195）取权威文本——口径差异如实记录。
3. **旧映射定理语句**：全部从工作树 Lean 源逐条提取（路径 `proofs/lean/juris_lean/JurisLean/FullMath/…`，行号见各项）。
4. **裁定搜索记录**：在 `docs/master-plan/施工台账_20261008_统一法律数学模型全量施工.md`（"裁定"仅出现于模板同源定制、
   工件计数门两处，均与 24 项无关）、两份 master-plan（"范围裁定"仅为流程概念，`20261010_接续方案评审_Codex_R1.md:64`、
   `20261010_统一法律数学模型_连续与语义全量施工方案.md:80`）、`TARGETS_57.json`（22 项 `current_state` 全部
   `NEEDS_SPECIFIC_FULL_PLAN_EVIDENCE`，无一项带已授权域处置）中搜索——**未发现 24 项中任何一项存在已授权范围裁定**。
   同时，24 项全部位于已授权 217 登记内（`TARGETS_57.json`＋`EXT_9.json`），按红线"域外必须相对已授权合同判定"，
   **不存在"超出原施工域"的判定需求**，故本表无 ③ 类候选、无"待 Owner 裁定"项。
5. **三态定义**（方案 `:78-82`）：①可补强到全量（有明确数学路线→施工）；②原目标含反例或表述不清（修订合同后证修订版，
   保反例）；③已授权范围裁定（记"已裁定范围处置"，不得计入原命题已证明）。

---

## 二、24 项逐项分类

记 `FullMath/` ＝ `proofs/lean/juris_lean/JurisLean/FullMath/`。每项五字段＋判定依据。

### J-01｜F03 严格前提准入
1. **原目标**："Prediction/Hypothesis 不可成为无条件 VerifiedPremise。"（`tools/full_math/spec/TARGETS_57.json` F03.original_statement；绑定行 `BINDING_217_and_60.md:26`）
2. **旧映射缺陷**：现绑 `composable_projections`@`FullMath/Core/IdentityCodec.lean:57`——组合恒等式下七字段相等定理（组合投影语义），与准入语义无任何蕴含关系（`BINDING:26` 评注"映射为组合投影定理，与严格准入语义错位"）。
3. **反例/范围依据**：取任意 composable 的 `CompId a b`，旧定理成立；同一登记链另构造一条把 `Admission.prediction c` 注册为已验证前提的调用（主链以非空串充权限——`附录I:510` 已点名此主链用法），原目标假而旧定理仍真。
4. **三态判定**：**①可补强到全量**。素材已在仓：`verified_requires_source_authority`@`FullMath/Evidence/Admission.lean:46-52` 的 `cases` 消解已证 status=verified 只能来自 `verifiedPremise` 构造子（hypothesis/prediction 分支 absurd）——该定理现错挂在 F12 名下（见 J-09），对 F03 恰是核心组件。
5. **剩余义务**：施工包 F03——换绑别名；补主链准入门（拒绝非空串/后缀充权限，类型化 source/authority）＋可用材料/可信内容/法院认定三型区分（`附录I:510`）。不得动 TARGETS_57.json 原句。

### J-02｜F05 有限 Horn 最小不动点与终止
1. **原目标**："TH^|A|(∅) 是有限正 Horn 的最小闭包。"（TARGETS_57 F05；`BINDING:28`）
2. **旧映射缺陷**：现绑 `cl_mono`@`FullMath/Logic/HornFixpoint.lean:65`——仅 `∀ n m, m ≤ n → cl R F m ⊆ cl R F n`（迭代单调性组件），非最小闭包＋高度 |A| 终止全量（`BINDING:28` 评注）。
3. **反例/范围依据**：旧定理对任意 `R F n m` 成立（如 R=∅, F={a}, n=5, m=2）；但"在高度 |A| 恰给出最小闭包且不早停"未被表述——取两步规则链 p0→p1→p2（|A|=3），最小闭包高度 2 已稳定，"|A| 步内到最小闭包"的终止界是独立结论，cl_mono 对其无内容。
4. **三态判定**：**①可补强到全量**。`cl_least_iterate`@`FullMath/Logic/HornFixpoint.lean:130`（最小性）已在仓（现错挂 D077 名下，`BINDING:143`）；补 |A| 高度归纳终止定理即达全量。
5. **剩余义务**：施工包 F05——换绑 {cl_mono, cl_least_iterate, 高度界} 合成定理；`附录I:512`（独立语义桥＋两个既有表示受保护观察相同）。

### J-03｜F06 有限高度论证生成健全
1. **原目标**："a∈Generate_d ⇒ WellFormed(a) ∧ height(a)≤d。"（TARGETS_57 F06；`BINDING:29`）
2. **旧映射缺陷**：现绑 `generate_complete`@`FullMath/Logic/ArgumentConstruction.lean:221`——**反方向**（WellFormed∧height≤d ⇒ ∈Generate）。`附录I:504` 已点名"F06 接生成完备……与原登记 F06 健全……不对应"。
3. **反例/范围依据**：满足旧定理的输入：任意良构论证 a（如 facts=[0]、rules=空）；但若 Generate 实现混入带悬空前提叶的非良构树，原目标假而旧定理（完备方向）对成员资格不含约束，仍真——方向颠倒使 Generate 的健全性完全失控。
4. **三态判定**：**①可补强到全量**。`generate_sound`@`FullMath/Logic/ArgumentConstruction.lean:181` 恰为原方向且已证（现错挂 D029 名下，`BINDING:95`）；换绑＋补 height 界即达。
5. **剩余义务**：施工包 F06——重绑 generate_sound＋输出树高度界；保留 generate_complete 给 F07（`附录I:504`：保留原定理本身，只改绑定）。

### J-04｜F07 有限高度论证生成完备
1. **原目标**："WellFormed(a) ∧ height(a)≤d ⇒ a∈Generate_d。"（TARGETS_57 F07；`BINDING:30`）
2. **旧映射缺陷**：现绑 `rooted_same_conclusion_different_identity`@`FullMath/Logic/ArgumentIdentity.lean:106`——循环/身份存在性见证（同结论不同高度），与生成完备完全错位（`附录I:504` 点名"F07 接身份反例"）。
3. **反例/范围依据**：该见证只给出两个循环论证 a、b 的存在性；对具体良构有界论证 a（facts=[0]、单规则两子树、height=2），旧映射不产生任何 `a∈Generate` 的成员资格——完备性未被触及。
4. **三态判定**：**①可补强到全量**。`generate_complete`@`ArgumentConstruction.lean:221` 就是原目标语句且已证（其现名下合同正是 F06 的错挂）；换绑即达，几乎零证明成本。
5. **剩余义务**：施工包 F07——换绑 generate_complete；若原范围需无界观察另证有限商化保义（`附录I:514`）。

### J-05｜F08 循环与身份的边界
1. **原目标**："无根循环不能产生支持；有根循环的原子稳定不意味着论证树稳定。"（TARGETS_57 F08；`BINDING:31`）
2. **旧映射缺陷**：现绑 `edgeFuel_iff`@`FullMath/Logic/AttackCompilation.lean:68`——边燃料 k 层反射（edgeFuel=Defeat 的逐层展开），覆盖攻击编译的燃料方面，非循环-支持边界（`BINDING:31` 评注"edgeFuel 仅边预算方面，非无根/有根循环反例全量"）。
3. **反例/范围依据**：edgeFuel_iff 对任意 k 与 height≤k 的 b 成立；但原目标的两个方向都是**构造性见证**：(a) 无根 a↔b 互攻环（两节点、无事实根）中没有任何原子进入 grounded 支持；(b) 有根循环上原子闭包早已稳定而论证树高度无限交替——`rooted_cycle_alternates`@`FullMath/Logic/ArgumentIdentity.lean:43` 已给 (b) 的素材。旧映射对两类见证均无表述。
4. **三态判定**：**①可补强到全量**。注意原目标本身是"要求给出反例"的负命题，这不属②（原目标含反例），而是目标自身即反例构造义务；素材（rooted_cycle_alternates）已在仓。
5. **剩余义务**：施工包 F08——补无根循环不产生支持的否定见证＋有根循环树不稳定见证两条定理（`附录I:515`：不能只保一个孤立例子）。

### J-06｜F09 攻击/击败编译双向对应
1. **原目标**："D_impl(a,b) ↔ DefeatSpec(v,c,a,b)。"（TARGETS_57 F09；`BINDING:32`）
2. **旧映射缺陷**：现绑 `pending_edges_bound`@`FullMath/Logic/AttackCompilation.lean:141`——`(pendingEdges edges policy).length ≤ edges.length`（List.length_filter_le 的长度界），与双向反射错位（`BINDING:32` 评注"仅未决边界，非攻击编译双向反射"）。
3. **反例/范围依据**：任意 edges/policy 输入满足长度界；但 policy 返回 `some false` 的被拒边、优先政策介入的边、端点与来源保持等情形，"实现↔规格"互推均无定理——例如被过滤边的"实现拒绝 ⇔ 规格非击败"方向未被证明。
4. **三态判定**：**①可补强到全量**。`edgeFuel_iff`@`AttackCompilation.lean:68` 已给燃料化双向反射骨架；按 `附录I:516` 扩展到每种攻击、优先及 pending 情形＋端点/来源保持。
5. **剩余义务**：施工包 F09——全攻击类型双向反射定理；未知优先政策产生未决模型、不静默删边（`MATHEMATICS_SPEC.md:74`）。

### J-07｜F10 扩展成员判定反射
1. **原目标**："member_b(profile,e)=true ↔ SatisfiesProfile(AF,profile,e)。"（TARGETS_57 F10；`BINDING:33`）
2. **旧映射缺陷**：现绑 `grounded_least`@`FullMath/Logic/ExtensionProfiles.lean:203`——仅 grounded 族对任意 charF 闭集 P 的包含方向（grounded af ⊆ P），非四 profile 布尔反射（`BINDING:33` 评注"仅 grounded profile，非四 profile 成员反射"）。
3. **反例/范围依据**：取 AF 与任意不动点闭集 P：grounded_least 成立；但 Complete/Stable/Preferred 三族的 `member_b` 布尔输出与语义集合（CF/Defends/Admissible/Complete/Preferred/Stable，`MATHEMATICS_SPEC.md:76`）之间无反射定理——e∉grounded 时的完整判定与三族判定均失控。
4. **三态判定**：**①可补强到全量**。`grounded_fixpoint`/`grounded_admissible`@`ExtensionProfiles.lean:186-190` 已有 grounded 不动点与 admissible 底座；按 `附录I:517` 与规格 §3 定义逐族证布尔反射（512 图回归只作测试不替普遍证明，`MATHEMATICS_SPEC.md:78`）。
5. **剩余义务**：施工包 F10——四族反射定理（重，建议与 EXT03 同一施工线，见 J-23）。

### J-08｜F11 扫描部分健全
1. **原目标**："S_found ⊆ Solutions。"（TARGETS_57 F11；`BINDING:34`）
2. **旧映射缺陷**：现绑 `incomplete_not_universal`@`FullMath/Logic/QueryAggregation.lean:64`——`evalUniversal .incomplete = .unknown`（rfl 定义性事实），与扫描健全错位（`附录I:504` 点名"F11 接查询未完成"）。
3. **反例/范围依据**：该 rfl 对任意类型 A 成立；但扫描器 `S_found` 每个元素属于独立 Solutions 集的健全性未被表述——扫描器哪怕输出垃圾元素，旧定理仍真。原目标是集合包含（健全性），规格 §3 明确"不把生成列表自己定义成语义全集"（`MATHEMATICS_SPEC.md:65`）。
4. **三态判定**：**①可补强到全量**。`附录I:518` 指定路线：`Representation/FiniteCertificates.lean` 的 `partial_scan_sound`——证明每次追加候选合法＋未处理集合及依赖保留。
5. **剩余义务**：施工包 F11——扫描健全定理＋未处理集保留；不能以"输出都合法"作唯一证明。

### J-09｜F12 扫描完整性
1. **原目标**："CompleteCheck ⇒ S_out = Solutions。"（TARGETS_57 F12；`BINDING:35`）
2. **旧映射缺陷**：现绑 `verified_requires_source_authority`@`FullMath/Evidence/Admission.lean:46`——Admission 构造子分类定理，与扫描等式完全错位（`附录I:504` 点名"F12 接来源权限"；`BINDING:35` 评注"映射为准入权威定理，与完整扫描等式错位"）。
3. **反例/范围依据**：任意 Admission 输入满足旧定理；扫描完整性要求"覆盖全域＋每元素精确核验 ⇒ 输出=解集全等"（原目标是完整性等式，非健全性），旧映射零覆盖。
4. **三态判定**：**①可补强到全量**。`附录I:519` 三件套：`enumeration_member`/`enumeration_certified`/`exact_check_reflects`，三个前提由构造推出（法律判词反射＋完整域覆盖＋实际枚举终止）。
5. **剩余义务**：施工包 F12——完整性等式定理；注：其旧映射定理（Admission 分类）移交给 F03 作组件（见 J-01），不删。

### J-10｜F13 空值与查询聚合安全
1. **原目标**："未找到解≠无解≠{∅}；不完整扩展族不能证明全称查询。"（TARGETS_57 F13；`BINDING:36`）
2. **旧映射缺陷**：现绑 `add_only_reuse`@`FullMath/Evidence/Withdrawal.lean:67`——增量闭包复用等式 `closure R' (F∪Δ) = closure R' (closure R F ∪ Δ)`，与空值/聚合安全错位（`附录I:504` 点名"F13 接增量复用"）。
3. **反例/范围依据**：add_only_reuse 对任意 R⊆R'、F、Δ 成立；但原目标要求三态分立见证（找不到扩展的空族≠无解≠恰含空扩展）与"incomplete 族不走全称真分支"——`threeRing`@`FullMath/Logic/QueryAggregation.lean:70`（三环无稳定扩展）素材已在仓而旧映射无表述。
4. **三态判定**：**①可补强到全量**。`incomplete_not_universal`@`:64` 已给 incomplete→unknown 分支；按 `附录I:520` 接 Result/evalUniversal/no_extensions_ne_empty_family。
5. **剩余义务**：施工包 F13——三态分立构造见证＋全称分支守卫；`MATHEMATICS_SPEC.md:80`（不能先删不满足合理性的扩展后继续声称原语义完整）。

### J-11｜P03 变量消去精确性
1. **原目标**："VE(query,e)=Enumerate(query,e)。"（TARGETS_57 P03；`BINDING:40`）
2. **旧映射缺陷**：现绑 `sum_out_distrib`@`FullMath/Probability/VariableElimination.lean:51`——**单变量** sum-out 分配律，且带 `∀ f ∈ fs, IndepAt f i` 独立性前提（`BINDING:40` 评注"仅 sum-out 分配律组件，非 VE=枚举全等"）。
3. **反例/范围依据**：旧定理只覆盖满足 IndepAt 的单步消去；对三变量任意联合表（变量相关，如 p(a,b,c) 全表），VE 实现 `elimVars` 全序列输出与全枚举的相等关系无定理覆盖。注意：独立性前提是**旧定理多出的前提**（原目标无此假设），正确路线是消去该前提并扩到全序列——不得把"带前提的单步"当原目标过门（红线 `附录I:723`）。
4. **三态判定**：**①可补强到全量**。`附录I:524`：完整消元序列对原联合分布边缘的等价——对 elimVars 序列归纳＋变量集覆盖/无重名；sum_out_distrib 作一步引理复用。
5. **剩余义务**：施工包 P03——VE=Enumerate 全等定理（精确 ℚ 算术，无浮点）。

### J-12｜P06 层级胜率学习实际使用数据
1. **原目标**："有限超先验权重 ∝ π_h∏g B(α_h+w_g,β_h+l_g)/B(α_h,β_h)。"（TARGETS_57 P06；`BINDING:43`）
2. **旧映射缺陷**：现绑 `hyper_data_changes_posterior`@`FullMath/Probability/DirichletPosterior.lean:115`——数值反例"数据改变后验"（∃ 两配置使 1/3 ≠ 6/11），非层级权重闭式公式（`BINDING:43` 评注"仅'数据改变后验'性质，非层级权重公式"）。
3. **反例/范围依据**：该定理只代入两组具体数；层级权重公式的归一化常数（∝ 右侧全式）、B 函数比值结构、超参数→同案预测的数据敏感性全称式均未证——存在性反例不蕴含闭式。
4. **三态判定**：**①可补强到全量**。`附录I:527`：hyperWeights/hyperWeights_normalizes＋具体函数与数据敏感性（两个值见证仅作非退化）。B(α,β) 以**正常数**消费（比例式不需求 B 的显值），整型/半整型/正有理分段的常数链由第一波 `Seams/UnifiedBetaDomain.lean`（bernCdf/betaTwoConst 等，`.local/agent_A_beta_report.md`，已绿）供给；**不需一般 Gamma**（方案 `:58`）。
5. **剩余义务**：施工包 P06——闭式比例定理＋归一化＋数据敏感性（依赖已绿 BetaDomain）。

### J-13｜P07 模型平均与竞争模型界
1. **原目标**："模型平均更新用证据边际；稳健界覆盖每个保留模型。"（TARGETS_57 P07；`BINDING:44`）
2. **旧映射缺陷**：现绑 `mixture_within_retained`@`FullMath/Probability/ModelAveraging.lean:22`——凸组合保持在 [lo,hi]（界半句组件），缺"证据边际更新"半句（`BINDING:44` 评注"仅保留模型内界，缺证据边际平均全量"）。
3. **反例/范围依据**：任意 ws∈单纯形、ps∈[lo,hi] 满足旧定理；但后验权重 ∝ 先验×边际似然的更新式、以及"未处理模型的界单独保留，不能只在保留模型内平均后宣称全域"（`附录I:528`）均未证。
4. **三态判定**：**①可补强到全量**。mix/mixture_update_normalizes 已在 `ModelAveraging.lean`（附录 I 同行指名）；补边际更新定理＋保留域声明即达。
5. **剩余义务**：施工包 P07——证据边际平均定理＋每保留模型稳健界＋未保留域边界声明。

### J-14｜N01 单位、来源、舍入解释器
1. **原目标**："每个算术表达式的结果具有声明单位/计算口径与精确指称。"（TARGETS_57 N01；`BINDING:52`）
2. **旧映射缺陷**：现绑 `conservation`@`FullMath/Numeric/Quantities.lean:30`——`covered r - uncovered r = r`（ℚ 一元守恒恒等式），缺单位/口径/舍入解释器（`BINDING:52` 评注）。
3. **反例/范围依据**：任意 `r : ℚ` 满足旧定理；但"100 元 + 3 米"这类量纲不相容相加、舍入位置/方向/误差界、跨月跨年历法（规格 §5：`MATHEMATICS_SPEC.md:110,118`——月不换 30 天、六类时间分型）在旧定理下不被拒绝也不被解释。
4. **三态判定**：**①可补强到全量**。`附录I:536`：类型化单位运算、来源、舍入＋完整跨月跨年历法（"当前同月 succDay 不是完整日历"为仓内自认开放）。路线明确：Quantity AST 携带币种/量纲/债项/主体/期间/口径（规格 §5:110），逐构造子证指称。重工程但无数学障碍。
5. **剩余义务**：施工包 N01——数量 AST 类型层＋舍入/历法解释器健全定理；该件是 56 项 PY-NUM 需求（见 W2-A 节）的数量底座，建议最优先排程。

### J-15｜N02 区间解释健全
1. **原目标**："Eval(e,x)∈IntervalEval(e,X) 对所有 x∈X 成立。"（TARGETS_57 N02；`BINDING:53`）
2. **旧映射缺陷**：现绑 `mul_sound`@`FullMath/Numeric/Intervals.lean:92`——仅乘法单节点健全（其证明内部还消费 `fixed_y_bounds`/`fixed_x_bounds`，`:94-96`），非全表达式归纳（`BINDING:53` 评注）。
3. **反例/范围依据**：mul_sound 对任意区间 i j 与 x∈i, y∈j 成立；但含加法/倒数/嵌套的表达式 e（如 `(x1+x2)·recip(x3)`）的区间健全性无定理——规格 §6 明确"对表达式结构归纳证明区间包含……除法需 0 不在分母区间，否则返回相应分裂/无界表示或明确不支持"（`MATHEMATICS_SPEC.md:124`）。
4. **三态判定**：**①可补强到全量**。`附录I:537`：对本案数量表达式递归给区间解释器，逐节点健全；除法跨零分支明确。
5. **剩余义务**：施工包 N02——结构归纳健全定理＋除法分支合同（与 N01 数量 AST 同源）。

### J-16｜N03 法律可行域
1. **原目标**："被称为 legal-feasible 的候选逐一满足已准入 C(v,c,f,y)。"（TARGETS_57 N03；`BINDING:54`）
2. **旧映射缺陷**：现绑 `weak_duality`@`FullMath/Numeric/LinearPrograms.lean:34`——方阵 LP 弱对偶 `dualObj ≤ primalObj`，与法律可行域标签健全性错位（`BINDING:54` 评注"映射为弱对偶，与法律可行域错位"）。
3. **反例/范围依据**：任意方阵 A 与可行 x,λ 满足弱对偶；但"legal-feasible 标签 ⇒ 逐条满足准入约束 C(v,c,f,y)"的标签反射未被触及——法律可行域须由构成关系生成约束（`附录I:538`："从同案裁量/共同约束生成约束，而非外填矩阵"）。
4. **三态判定**：**①可补强到全量**。定义 legalFeasible＝对准入 C 逐条检查并证健全反射；LP 机器留给 N05（N05 已 BOUND）。输入编码走 F03 准入产物（N03 depends_on F03/F09/N01，TARGETS_57.json）。
5. **剩余义务**：施工包 N03——可行标签健全定理；弱对偶定理保留原位不删。

### J-17｜N10 固定点与优化目标一致
1. **原目标**："x*=clip(-b/a) 满足变分不等式，因此最小化指定二次目标。"（TARGETS_57 N10；`BINDING:61`）
2. **旧映射缺陷**：现绑 `T_fixed_interior`@`FullMath/Numeric/Banach.lean:90`——仅内部情形（前提 `l ≤ -(b/a) ≤ u` 下不动点等式），缺左/右边界两情形与"⇒最小化"半句（`BINDING:61` 评注"仅内部情形不动点，缺三情形变分不等式"）。
3. **反例/范围依据**：取 a=1, b=3, l=0, u=1：-b/a=-3 ∉ [0,1]，clip 后 x*=0；旧定理前提不满足（对其无内容），而原目标恰需此边界情形的变分不等式 ⟨Tx*-x*, x*-x⟩≥0 论证——三情形缺二。
4. **三态判定**：**①可补强到全量**。`附录I:545`：T_fixed_point/T_fixed_interior＋Convexity——补边界 KKT 情形，把同一目标/可行域与 N08/N09 算子串接；二次目标凸性给出"变分不等式⇒最小"半句。
5. **剩余义务**：施工包 N10——三情形变分不等式＋最小化推论（N08/N09 已 BOUND 作底座）。

### J-18｜B01 领域无关的争点型证明责任
1. **原目标**："证明对象、提出责任、说服责任、标准、阶段、主体和后果均有明确来源。"（TARGETS_57 B01；`BINDING:62`）
2. **旧映射缺陷**：现绑 `conflict_without_rule_is_pending`@`FullMath/Burden/DomainAgnostic.lean:42`——双政策冲突→pending（rfl 单组件），`BINDING:62` 评注"仅无政策则 pending 组件"。
3. **反例/范围依据**：`resolveList [p,q] s = pending` 对任意 p≠q 成立；但七槽（证明对象/提出/说服/标准/阶段/主体/后果）逐一从具名法源分配的全称性质未证——`附录I:546`："列表单项存在不等于正确分配"。
4. **三态判定**：**①可补强到全量**。BurdenSlot/resolveList 语法扩全七槽＋来源绑定逐槽证明；规格 §10 的 `BurdenPolicy=(issue,party,production,persuasion,standard,stage,triggers,rebuttal,consequence,sourceVersion)`（`MATHEMATICS_SPEC.md:200`）给出字段级合同。
5. **剩余义务**：施工包 B01——七槽来源绑定全称定理；单组件定理保留。

### J-19｜B07 法源时间与语义覆盖
1. **原目标**："法律覆盖 complete 相对于独立 requiredSlots、例外和时间政策成立。"（TARGETS_57 B07；`BINDING:68`）
2. **旧映射缺陷**：现绑 `version_change_invalidates`@`FullMath/Burden/SourceTime.lean:89`——cacheKey 不同⇒cacheHit=false（版本失效单方向），`BINDING:68` 评注"仅版本失效方向，缺 requiredSlots 覆盖完备"。
3. **反例/范围依据**：任意不同版本 v v' 满足旧定理；但"对独立 requiredSlots 逐一覆盖、例外与时间政策单独处理、缺政策=不适用而非跳过"（`附录I:552`）未证——版本失效不蕴含覆盖完备，两方向独立。
4. **三态判定**：**①可补强到全量**。SourceVersion/decideSlot/cacheKey 上补 requiredSlots 覆盖定理＋缺政策未决分支（同文件 `cache_hit_only_same_version`@`:94` 已有反向引理）。
5. **剩余义务**：施工包 B07——覆盖完备定理（原目标是"complete"完整性陈述，不得降为健全性单方向过门，`附录K:10`）。

### J-20｜G01 效用与合法行动集
1. **原目标**："策略优化只在 LegalAction 集合内，成本/概率/目标含明确来源。"（TARGETS_57 G01；`BINDING:69`）
2. **旧映射缺陷**：现绑 `vf_dominates`@`FullMath/Numeric/Bellman.lean:100`——合法行动内 `qval ≤ vf`（`Finset.le_max'` 单组件），`BINDING:69` 评注"仅值函数占优，缺合法行动集/来源全量"。
3. **反例/范围依据**：任意 legal/r/p/β/t 输入满足旧定理；但"奖励/概率来自 L08 后果"的来源绑定与"违法动作永不进入最大化（禁止高收益抵消硬违法约束）"（规格 §12：`MATHEMATICS_SPEC.md:222`）未证——占优是对给定 legal 集的，legal 集本身是否来自法律状态无定理。
4. **三态判定**：**①可补强到全量**。`附录I:553`：行动可行域来自法律状态，奖励来自 L08 后果；真实信息约束下有限时域求值及最优策略构造。
5. **剩余义务**：施工包 G01——legal 集来源定理＋成本/概率/目标来源绑定（合法成员见证）。

### J-21｜G05 均衡/策略近似误差
1. **原目标**："maximum regret≤ε ⇒ 在声明有限游戏上的 ε 均衡。"（TARGETS_57 G05；`BINDING:73`）
2. **旧映射缺陷**：现绑 `rectangle_lower_bound`@`FullMath/Action/RobustDecisions.lean:19`——非矩形共享参数下界 `m₁+m₂ ≤ r₁θ+r₂θ`（**EXT08 的内容**），`BINDING:73` 评注点名"映射为矩形下界（EXT08 内容），与 ε 均衡错位"。
3. **反例/范围依据**：取 Θ={θ₀}、r₁=r₂=常值、m₁=m₂=0：旧定理成立；同一参数下构造 2×2 博弈某 profile 最大偏离收益=1，则原目标（ε=1/2 的 ε 均衡）假而旧定理真——完全错位。
4. **三态判定**：**①可补强到全量**。规格 §12："ε 均衡证明各玩家最大偏离收益≤ε；遍历策略集有限完备或由独立最优响应证书保证"（`MATHEMATICS_SPEC.md:226`）——即"各玩家最大偏离收益≤ε"就是 ε 均衡的定义展开；桥接素材 `dev_gain_two_eta`@`proofs/lean/juris_lean/JurisLean/Seams/PayoffEquilibrium.lean:303`（针 31 锚）已在仓。
5. **剩余义务**：施工包 G05——换绑 regret≤ε→ε 均衡定理（有限策略集完备遍历）；矩形下界定理保留给 EXT08。

### J-22｜C01 关系组合健全/完备
1. **原目标**："局部关系包含/相等通过共同见证关联后在总关系中保持。"（TARGETS_57 C01；`BINDING:74`）
2. **旧映射缺陷**：现绑 `relComp_assoc`@`FullMath/Composition/RelationalComposition.lean:26`——结合律组件；`附录I:558` 明示"结合律只负责组合骨架"，包含/相等保持是另一件事。
3. **反例/范围依据**：任意 r s t 满足结合律；但 `r ⊆ r' ⇒ relComp r s ⊆ relComp r' s`（ witness 结构下的包含保持）与等式传递未证——结合律对单调性零蕴含。
4. **三态判定**：**①可补强到全量**。补 relComp 对两参数的单调性＋等式保持，再逐条真实法律关系实例化 sound/complete、串接同一中间对象（`附录I:558`）。
5. **剩余义务**：施工包 C01——保持定理＋实例化；结合律引理复用。

### J-23｜EXT03 profile 化结构论证合理性与新旧映射
1. **原目标**："按明确严格/可废止规则、子论证、contrary、偏好前提证明；不能静默删扩展改原语义"（`BINDING:83` 行内容列）；权威文本 `MATHEMATICS_SPEC.md:66-80`（§3）：子论证闭合、严格规则闭包（不加入可废止规则）、直接/间接一致性、不并置两个扩展的结论判矛盾、profile 不满足强性质时给具体反例＋**版本化替代合同**、不把全部 profile 统一降级。
2. **旧映射缺陷**：现绑 `grounded_fixpoint`@`FullMath/Logic/ExtensionProfiles.lean:186`——仅 grounded 不动点等式（`BINDING:83` 评注"仅 grounded 不动点，非 profile 化合理性映射"）。
3. **反例/范围依据**：任意 AF 满足 grounded_fixpoint；但严格闭包不混可废止规则、按 profile 的结构合理性（子论证闭合/一致性）逐条实例化、扩展删除须留版本化合同——均无定理。EXT_9.json 状态 `PLANNED_PROOFS_NOT_CLOSED`、proof_targets=["F06","F07","F08","F09","F10","B01"]（`tools/full_math/spec/EXT_9.json` EXT03 行）——即 EXT03 的完成以 F06-F10/B01 补强为前提。
4. **三态判定**：**①可补强到全量**。`附录I:578`：`ArgumentProfile`、`profile_semantics_correspondence`、`legacy_profile_embedding`——复用树生成/Defeat/AF profiles，证明选定 profile 的支持、攻击与评价含义。**24 项中最重**。
5. **剩余义务**：施工包 EXT03——依赖 J-03/04/05/06/07/18 先行；版本化替代合同机制入 Contracts。

### J-24｜EXT06 保形秩、数据用途和统计组合
1. **原目标**："边际/条件/筛选后覆盖分开；PAV 与保形校准数据不擅自复用；支持时变条件风险扩展"（`BINDING:86` 行内容列）；权威文本 `MATHEMATICS_SPEC.md:186-192`（§9）：保形秩 `k=ceil((n+1)(1-α))`、k=n+1 取 +∞ 不截成最大值、并列分数保守 ≤、交换性给秩覆盖、筛选集需另证 `P(Y∉S)≤β` 才得 `max(0,1-α-β)` 合并覆盖、序贯超鞅 `M_t=∏(1+λ_t(L_t-r))` 经 Ville 控制任意停止误报。
2. **旧映射缺陷**：现绑 `parts_cover`@`FullMath/Probability/SplitNoLeak.lean:57`——`r∈legalRows ⇒ r∈partRows (tagOf r)`（用途分部覆盖单组件），`BINDING:86` 评注"仅 parts 覆盖组件，缺保形秩/数据用途"。
3. **反例/范围依据**：parts_cover 对任意 legalRow 成立；但保形秩覆盖、边际/条件/筛选三覆盖不可互推（反例：仅边际覆盖 1-α 时筛选后条件覆盖可低于 max(0,1-α-β)——规格 §9:188 明文）、多轮复用校准集不自动保留原保证、时变条件风险的置信序列前提均无定理。
4. **三态判定**：**①可补强到全量**。`附录I:581`：`splitByDeclaredUse`、`conformalRank`、`coverage_under_declared_sampling`——复用 SplitNoLeak/Brier/PAV 局部引理；交换性/用途独立/自适应条件真实建模。EXT_9.json proof_targets=["P10","P11","P12","P13","E01"]（P10-P13/E01 均 BOUND，底座齐）。
5. **剩余义务**：施工包 EXT06——保形秩覆盖＋三覆盖分立＋序贯置信序列（标准保形预测＋Ville 路线，数学无开放点）。

---

## 三、三态计数汇总

| 三态 | 项数 | 编号 |
|---|---|---|
| ① 可补强到全量（有明确数学路线） | **24** | J-01…J-24 全部 |
| ② 原目标含反例或表述不清（修订合同后证修订版） | **0** | — |
| ③ 已授权范围裁定（已裁定范围处置，不计入已证明） | **0** | — |
| 待 Owner 裁定 | **0** | — |

判定依据（逐项已给反例/范围依据）：
- **无 ②**：24 项原目标全部是"对自仓构造的健全性/完备性/反射/存在性"陈述，逐项检查未见目标自身为假或不可表述（F08 的负命题是"目标要求给出反例"，不是"目标含反例"；B07/G05 的关键名词 requiredSlots/maximum regret 在 `MATHEMATICS_SPEC.md:200,226` 与规格文本中有字段级定义，不属表述不清）。
- **无 ③**：裁定搜索记录见第一节第 4 条——未发现任何已授权范围裁定；且 24 项全部在 217 授权登记内，按红线不产生"超出原施工域"判定。"超出某模块实现域"的情形存在（如 succDay 非完整日历、UnifiedCAD 仅二次有理根），但它们都**不落在 24 项上**，且属于"模块待补"而非"域外"。
- **口径提示**：本表 ①×24 不改变各项目前"未闭合"状态——`TARGETS_57.json` 22 项 current_state 全部 `NEEDS_SPECIFIC_FULL_PLAN_EVIDENCE`、EXT_9.json 2 项 `PLANNED_PROOFS_NOT_CLOSED`；①是"路线判定"，完成以施工包六件套＋CI 为准（方案 `:118`）。

## 四、红线自查

1. 未以"删原需求"消除任何错配：所有处置均为换绑/补强，原定理保留（J-01/03/04/09/21/22 明示"保留"义务），符合 `附录I:504`。
2. 未以弱命题替原目标过门：每项剩余义务都指回原目标语句的完整形态（完整性项 F12/B07 不得降为健全性过门，`附录K:10`）。
3. 表述不清未直接换弱命题：②计数为 0，无需此出口。
4. 域外判定相对已授权合同：24 项均在授权登记内，无域外判定；未把"模块实现域不足"混充"域外"。
5. 引用均带文件:行号；反例均构造性（给出具体输入/参数）。

---

## 五、W2-A 打包侦察（134 项）

### 5.1 分组统计（`tools/full_math/spec/DEMANDS_134.json`，逐项 group 字段实核）

| 组 | 项数 | D 范围 | 现挂别名（15 通用定理之一，`BINDING:319`） |
|---|---|---|---|
| 01 接案、问题与主体识别 | 8 | D001-D008 | locator_not_identity |
| 02 法源、解释与类案研究 | 10 | D009-D018 | unknown_is_pending |
| 03 证据内容、事件与冲突 | 10 | D019-D028 | dedup_conflict_not_overwrite |
| 04 请求权、抗辩及争点处理 | 8 | D029-D036 | generate_sound |
| 05 刑事定罪、量刑与多被告 | 10 | D037-D046 | perPerson_slots_distinct |
| 06 借贷、担保与共同债务 | 10 | D047-D056 | parts_nonneg |
| 07 侵权责任与损害 | 8 | D057-D064 | fixed_y_bounds |
| 08 合同条款与权利义务审核 | 12 | D065-D076 | docPut_docPut |
| 09 并购与交割条件 | 10 | D077-D086 | cl_least_iterate |
| 10 企业调查、诉讼与执行数据 | 8 | D087-D094 | exists_extension_witnessed |
| 11 金额、时间和经济敞口 | 9 | D095-D103 | succDay_ordinal_mono |
| 12 起草、修订与交付 | 12 | D104-D115 | parse_render_roundtrip |
| 13 办案、交易工作流与策略 | 8 | D116-D123 | bellman_onesided |
| 14 伦理、隐私与表达可靠性 | 7 | D124-D130 | step_rules_mono |
| 15 美国法特定问题与法律语言任务 | 4 | D131-D134 | condition_incompatible_iff |
| **合计** | **134** | D001-D134 | 15 个通用定理服务 134 需求（`BINDING:319`） |

正式化类别分布（DEMANDS_134.json formalization_class）：法律条件计算优先 54、语义/经验混合 40、机械精化优先 40（各组明细已实核）。

### 5.2 依赖分类

**A 类：不依赖新基础，现有载体即可全量施工（87 项）**——组01-04、08-10、12 的合同构造只消费既有 FullMath 族级定理
（Core/IdentityCodec、Logic/*、Evidence/*、Burden/*、Numeric/Quantities、Composition/ByteSyntax 等）与
Python `tools/full_math/implementation/` 六个参考模块（horn_logic/argumentation_ref/numeric_ref/probability_ref/burden_ref/action_ref）
＋`tools/unified_math_v2/unified/` 16 模块。别名错配的修复=按 `ALL_134_MATH_CONTRACTS.md` 每项"要证明的具体性质"重写
`FullMath/Contracts.lean` 的 def（现为通用别名语句，如 `demand_D001 : Prop := ∃ a b : List String, locator a = locator b ∧ a ≠ b`，
`Contracts.lean:253`）＋重证 Acceptance。

**B 类：依赖第一波已绿基础件（28 项）**：
- **UnifiedFourteenFamilies（W1-3，已绿）**：组05/06/07（D037-D064，28 项）——族级规则网络（29 条规则原子＋法源效力窗口）
  正是这三组的族级定理消费面；W2-A 规则"证明可调用族级定理，但须证输入编码、参数、观察与范围映射"（方案 `:70-71`）。
- **UnifiedBetaDomain（W1-4，已绿）**：PY-PROB/PY-CAUSE 9 项（D013/D040/D058/D101/D118/D120/D125/D128/D134，附录K Python 行实核）
  中的概率/统计组件（胜率、先验、统计 vs 直接证据分类）。
- **UnifiedTrajectory（W1-2，已绿）**：组13（D116-D123）工作流排序/策略求解的可选轨迹表达（延续偏离）。
- **UnifiedCADCore（C0/C1，已绿）**：PY-ACT 11 项（D080/D081/D083/D100/D117-D121/D128/D134）中策略枚举的实式编码面。

**C 类：依赖尚开放基础（挂起子句，非整项挂起）**：
- **CAD C2-C5（完整投影/格覆盖/证书生成器/QEPCAD 证书线）**：若上述 PY-ACT/PY-PROB 项的独立合同要求量词消去级保证
  （混合策略均衡存在、序贯信念、共同后果优化——`附录J:24` 类比），其全量判定在 C2-C5 闭合前记"组件已施工、全量判定挂起"。
  精确到项的 CAD 依赖需各施工包开工时按合同句逐项确认（本侦察按 PY-tag 初判，**不确定处如实标注**）。
- **一般 Gamma**：无 134 项直接依赖（W1-4 三段路线已绕开，方案 `:58`）。

### 5.3 分批施工方案（14 批 × 8-12 项，依赖放行）

| 批 | 项数 | 内容 | Lean 载体落点 | 依赖 |
|---|---|---|---|---|
| B01 | 8 | 组01 D001-D008 主体/定位 | FullMath/Contracts+Acceptance（现 217 def/218 theorem 结构，`BINDING:323`） | 无新依赖，可立即开工 |
| B02 | 10 | 组02 D009-D018 法源/解释/类案 | 同上＋Burden/SourceTime | 无 |
| B03 | 10 | 组03 D019-D028 证据/事件/冲突 | 同上＋Probability/EvidenceIdentity | 无 |
| B04 | 8 | 组04 D029-D036 请求权/争点 | 同上＋Logic/ArgumentConstruction | 无 |
| B05 | 10 | 组05 D037-D046 刑事 | 同上＋Burden/Families | FourteenFamilies（绿） |
| B06 | 10 | 组06 D047-D056 借贷/担保 | 同上＋Numeric/Quantities | FourteenFamilies＋数量账本构造（与 W2-B N01 同源，先做共享 AST） |
| B07 | 8 | 组07 D057-D064 侵权 | 同上＋Numeric/Intervals | 数量/区间构造（与 N01/N02 同源） |
| B08 | 12 | 组08 D065-D076 合同条款 | 同上＋Core/ByteSyntax | 无 |
| B09 | 10 | 组09 D077-D086 并购交割 | 同上＋Logic/HornFixpoint | 无 |
| B10 | 8 | 组10 D087-D094 企业数据 | 同上＋Logic/QueryAggregation | 无 |
| B11 | 9 | 组11 D095-D103 金额时间 | 同上＋Numeric/Quantities 日历 | 日历构造（建议在此批落地完整历法，回灌 W2-B N01） |
| B12 | 12 | 组12 D104-D115 起草交付 | 同上＋Core/ByteSyntax | 无 |
| B13 | 8 | 组13 D116-D123 工作流策略 | 同上＋Numeric/Bellman、Action/* | Trajectory（绿，可选）；CAD 类子项按 C2-C5 挂起标注 |
| B14 | 11 | 组14+15 D124-D134 伦理/美国法 | 同上＋Evidence/Withdrawal、Probability/Conditioning | BetaDomain（绿）；D128 优化子句按 C2-C5 挂起标注 |

合计 134；B01-B04/B08-B12 共 87 项可立即并行；批内聚=同组同别名载体，一次重绑一批，测试参数化共用而期望逐项独立（`附录K:14`）。

### 5.4 六件套落点（每项，`附录J:30-34`＋`附录K:15` 行为合同）

1. **Lean 独立结论定理**：`FullMath/Contracts.lean` def 换为本项独立语义语句（来源=`ALL_134_MATH_CONTRACTS.md` 每项
   "要证明的具体性质"加粗句）＋`FullMath/Acceptance.lean` 重证；禁止参数化别名（方案 `:70`、评审第 12 条）。
2. **Python 入口**：按附录K 每项 Python 行的 PY-tag 落位（附录 `附录J:45-58` 已定义 PY-ID/PY-IR/PY-RUN/PY-CHECK/PY-EVID
   载体；PY-NUM→v2 quantities/precision、PY-SRC→norm_selection/source、PY-BUR→burdens/standards、PY-ARG→arguments/
   argument_grammar、PY-DOC→contract、PY-PROB→win_model/model_basis/beta、PY-ACT→pipeline/action、PY-CAUSE→taint/process）。
3. **独立 checker**：`v21/checker.py` 模式——独立参考核验合同，不接见证回调、不用主实现生成预期（`附录J:33`）。
4. **下游消费**：`pipeline.py` 的 run_case/step_event/run_trace 实际消费本项中间结果（`附录J:55`）。
5. **本项正反例**：`ALL_134_MATH_CONTRACTS.md` 每项"反例"字段（如 D001"同一咨询含欠款与名誉请求，不能因主主题只报一个"）
   落 `tools/full_math/implementation_tests/test_*.py` 参数化用例，期望逐项独立（`附录K:14`）。
6. **合成结果**：`tools/full_math/completion.py` validate_binding＋运行回执（PY-EVID，`附录J:58`）。

### 5.5 附录 K ↔ DEMANDS_134.json 对应性（核对结论：**全量 1:1，无缺行**）

- 全量核对（非仅抽查）：附录K `#### D001`…`#### D134` 标题行 **134/134**；`demand_D###` 引用 **134/134**；
  与 `DEMANDS_134.json` 的 134 个 requirement_id 双向差集均为空（脚本核验，`.local/j_kcheck.py`）。
- 逐项抽查 11 项（D001/D014/D027/D040/D053/D066/D079/D092/D105/D118/D134）：标题、组别、实践问句三方一致；
  每项 K 行含 Lean 重绑指令（`FullMath.Contracts.demand_DXXX → FullMath.Acceptance.demand_DXXX`）＋M 族落点＋
  PY-tag 行为合同，与 json 的 required_lean_name/required_contract_name/proof_family_ids 对应。
- 结论：**未发现"K 有行无 json 项"或"json 有项无 K 行"**；W2-A 依赖材料可直接以"附录K 逐行＋DEMANDS_134.json"双源执行
  （方案 `:72-73`），`BINDINGS_AND_EVIDENCE.md` 第 1 节确无逐项需求描述（`:3-28` 仅绑定方法论，评审第 12 条认定维持）。

## 六、发现的口径问题（供主控裁定/修订）

1. **60 针侧小计内部不一致**：`BINDING_217_and_60.md:313` 表尾"小计：BOUND 2，PARTIAL 42，UNBOUND 16"是补强波前旧读数，
   `:328` 已更新为"BOUND 60 / UNBOUND 0"，但 `:329` 明细"BOUND=48"（47 新闭合＋针 47 复认）与 `:330`"60 针全部……落定理"并列——
   48 与 60 的差额（针 53 finite_positive_support_truth_bridge 行 `:304` 状态列自标 UNBOUND/Python 列 UNBOUND）未在 §4.2 内闭合解释。
   **属于 60 针侧，不影响本表 24 项口径**；建议主控在 Z1 审计表（方案 `:27-31`）中一并清算。
2. **EXT03/EXT06 原目标文本层级**：EXT_9.json 无逐项 statement（仅泛句 acceptance），权威文本在 MATHEMATICS_SPEC §3/§9——
   与 F/P/N/B/G/C 项（TARGETS_57.json 有 original_statement）层级不同；施工时"修订句提案"落点不同（EXT 项以规格节为原合同）。
3. **TARGETS_57.json 的 statement≡original_statement**（22 项抽核一致）：登记表未区分原始/当前合同；按 `附录I:504`，
   别名修复只动 Contracts/Acceptance 绑定，**不得改 spec JSON 原句**——施工包需有此纪律。
4. **PY-tag 是附录K 的 Python 行为合同线索，非 DEMANDS_134.json 字段**：json 侧只有 reuse_targets/proof_family_ids；
   批次 Python 落点以附录K 逐行为准（本侦察已按 K 行实核 PY-tag 分布：PY-NUM 56 项、PY-SRC 53 项、PY-LOG 28 项、
   PY-ACT 11 项、PY-PROB/PY-CAUSE 各 9 项）。
