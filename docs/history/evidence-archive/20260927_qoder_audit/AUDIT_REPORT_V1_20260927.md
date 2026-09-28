# Qoder 审计报告 v1（2026-09-27，HEAD b57d4aa）

## 0. 总判定

不是"统一的法律数学证明"，目前是**统一的法律数学台账 + 一份薄而真的数学内核**。"统一"落在账本层（P 谱、T 谱、p_registry、回执表四套账互相咬合，机械核验基本无断链）和交付层（回执纪律真在 Python 里强制），没有落在数学结构层——新的 300 条 Genealogy 定理自建 295 个载体、只引一处 Mathlib、import 是一条线性链而非共享内核，所以 132 概念各写各的小模型。更扎人的是：真正有数学含量的是历史线 FullMath/BusinessRoot（ℚ、`ring`、Brier 恒等式、污染界），而它们既没进新账本的锚，也没进公理审计。任务书里说的"CI 全绿"我核过是真的（push 即跑全量 clean build + 公理审计 + 发证），但绿只说明能编译、门测试过；它救不了一条结论是 `f k = f k`。想让这套东西变成你要的整机，缺的不是证明数量，是**一次真正的合流**：把 Mathlib 接进来、把散落的小模型归到一组序结构/代数结构上、把军令四件从 Python 抬进 Lean。

---

## 1. 四问直接回答

### Q1 方案执行度：**PARTIAL**（已执行 6 项 / 部分 4 项 / 未执行实质 2 项）

| 方案条款 | 判定 | 证据 |
|---|---|---|
| 132 概念逐项有锚 | 部分 | `theory/spec/p_registry.json` 132 条、288 锚，文件与符号实存率 100%（我逐条 `Path.exists()` + 词界 grep，0 缺）；**但 32 条无任何 Lean 锚**，含军令件 P-112/118/090 |
| 七层两横切无矛盾 | 部分 | 实数 132 行、P-001..P-132 连续；但 L3 桶头 `docs/master-plan/基线/法律概念总谱.md:129` 声明"13 项"实际 14 行；同文档 `:247` 与 `:279` 档位自相矛盾 |
| 四 ❓ 定理级收口 | 已执行（名）/部分（实） | 四条定理名全部实存（`claim_available_complete_iff`、`boundary_inputs_complete`、`gap_detection_preserves_signal_roster`、clamp 六定理）；P-051 两条是投影 rfl，见下 P2-13 |
| T01–T127 定理级展开 | **未执行实质** | `theory/spec/lh_alignment/t_p_coverage.jsonl` 127 行全 `COVERED/FULL`，其中 **124 行 `"theorem": null`**；被指向的源码自陈 `Batch1.lean:81` "T01 完整陈述仍缺：" 共 40 处，全 TSpectrum `降级注` 129 处 |
| 复用总账 X57/Y41/Z34 | 已执行（算术）/部分（锚） | `02_复用总账.md:14-27` 三档逐桶求和 = 57/41/34/132 全对；但 `:30` 战役后改口"现全谱 直接挂 132/132"，与实测 32 条无 Lean 锚不符。锚点抽样我只做了 p_registry 侧（288 锚 0 断链），**逐条 X/Y/Z 抽样未完成＝UNKNOWN** |
| 军令五件 | **FAIL 4/5** | 见 Q2 判据 4 |
| 两层纪律 | 部分 | 抽 3 个 CI run 号（36258901155/36117165469/36095609565/36094524508）全部真实且 `success`；但论文 5 处数字主张只有 1 处（`:145`）附了 run 号，`:144/:147/:150` 只写"CI 全绿/具名 CI 运行"而未具名 |
| 11 卷分卷计划进度 | UNKNOWN | 本轮未逐卷核对（见第 5 节） |

### Q2 目的达成度：**PARTIAL，且重心偏向"播报统一"**

用户的两个担忧，第一个成立，第二个反向成立（比工程更糟的是记账）。

**判据 1｜同构统一：不成立。** `JurisLean/Genealogy/` 的 import 图是一条线：`Part0→Part1→…→Part6→Batch1→Batch2→Batch3→Batch4`（14 个文件各一行 import，我逐行读过）。TSpectrum 的 `Batch1.lean` 除了第 1 行 `import JurisLean.Genealogy.Part6` 外，正文对 Part6 零引用（全文件 `JurisLean` 只出现在第 1、3、1742 行的 namespace 上）。300 条定理配 295 个自建载体（def/structure/inductive）。实锤的重复建设：`Part4.lean:543 structure EvidenceItemEVPI` + `:548 def insertEvpi` 与 `General.lean:147 structure P083EvpiItem` + `:153 def insertEvpi` 是同一概念的两套模型。全仓唯一的共享内核 `JurisLean.FullMath.Core.Foundations`（45 个模块 import 它）**不被 Genealogy 任何一个文件 import**；Genealogy 引 Mathlib 只有一处：`Part3.lean:2 import Mathlib.Data.Finset.Basic`。

**判据 2｜数学密度 vs 工程密度（方法：comment-stripped 后按语句是否含变量绑定 + 关键词，指标是我自建的，口径见第 4 节）。** 语料 1799 条 theorem+lemma：**791 条（44%）语句里一个变量都没绑**，即按定义就是见证级闭语句；**433 条（24%）是一行式契约搬运** `theorem root_CIVIL : Contracts.root_CIVIL := Roots.root_CIVIL`（`FullMath/Acceptance.lean:23-33`，215 条；`CompletionAudit.lean` 217 条）；用 `induction` 的 **72 条（4.0%）**，用算术 tactic（omega/linarith/norm_num）的 130 条（7.2%）。含工程压制词的 208 条（12%），含数学词的 409 条（23%）。分线看：Genealogy 见证级 51%、FullMath 63%、BusinessRoot 61%、ULM 线 0%。**结论：工程不是重心，"记账式见证"才是重心**；真正的法律数学在 BusinessRoot/Analytics 与 FullMath/Probability 这两条老线上（例：`BusinessRoot/Analytics.lean:99 CU_expectation_conservation (P q p : ℚ) : weighted … = P - p * q` 由 `ring` 闭合，是真的一般式）。

**判据 3｜四层覆盖。** 本体层最厚（P014-P052 群，含 Dung/Horn/DDL 老定理群）；计算层次之（clamp 六定理、`P097_allocate_conservation`、`P099_progressiveTax3_*`，多为 Nat 上的真不等式）；压制层密度最高但数学最薄（Part6 的 23 条几乎全是 `= true` 闸门）；**行为主义层最空**：T112 量刑双线在 `Batch4.lean` 处是 `theorem T112_dual_track_separated : (DualTrackSentencing.mk 24 20 30 "NORMATIVE").track = "NORMATIVE" := by rfl`（构造子自己读的字段）；T81 纳什讨价还价在 `Batch4.lean:241` 是 `(NashBargaining.mk 0 100).agreement = 100 := by rfl`；谈判侧 Python 也只做区间交：`theory/spec/negotiation_contracts.py:73-76` `lo = max(...); hi = min(...); return (lo, hi) if lo <= hi else None` —— 没有纳什积、没有最大化。

**判据 4｜军令四件 Lean 落点。**
1. **概率**：老线有真数学（`FullMath/Probability/Brier.lean:20 brier_excess_identity (p q : ℝ) : … = (q - p)^2`；`Misspecification.lean:15 contamination_bounds … nlinarith`；`Conditioning.lean:62 posterior_normalizes … ∑ s, posterior p e hZ s = 1`），**但 FullMath 全域 `#print axioms` 为 0 条**，且新线只留了 `Batch3.lean:121 def brierScore (probability : Int) (outcome : Int) : Int` 的 Int 玩具。
2. **胜诉率三步管线**：Lean **无任何承载**。三步只在 Python：`theory/spec/probability_pipeline.py:68/129/189/263`，真正的数学 `:186` 委托给 `tools/unified_math_v2/unified/win_model.py:158-199` 的精确有理 Beta-binomial 尾概率。违背"已实现必接入"。**FAIL**。
3. **类案数学结构对比**：Python 侧是元组集合相等（`retrieval_v4.py:110-115 same_bucket = left.bucket_key() == right.bucket_key()`）；Lean 侧 `Batch3.lean:219 signature_deterministic : bucketKey {…} = bucketKey {…} := rfl`（同一字面量两边自等）。全仓无 `Equiv`/同构/双射定理。**FAIL**。
4. **NN 带证书逼近器**：`BanachCertificate.lean:14` 文件自陈 "Status: certificate schema only; no Banach theorem is claimed here."，`:37-39 def verifyCertificate (_T : …) (_cert : …) : Bool := true`；V3 五定理是字段投影——`CertifiedApproximation` 结构第 71 行已含字段 `errorWithinTolerance : errorBound ≤ tolerance`，`:103 certificate_error_within_tolerance … := certificate.errorWithinTolerance`。误差界是**输入假设**，不是被证出的界；`weights : List Nat`，没有被逼近的函数、没有网络。真 Banach 数学在别处（`ULM15IncrementalEmpiricalBanach.lean:146 banach_apriori_error_bound`）但与该证书零连接。**FAIL（军令级）**。
5. **博弈论**：Python 自己声明不是纳什（`theory/spec/action_decision.py:147-149 "it is NOT a Nash equilibrium solver"`）；Lean 侧只有 `Batch4.lean:238-242` 的 Int 玩具与老线 `FullMath/Action/Mechanisms.lean:42 secondPriceReserve_DSIC`（真 DSIC 占优）。全仓无博弈树/扩展型（`gameTree|game_tree` 在 proofs/ 零命中）。**FAIL**。

**判据 5｜删减实验。** 把工程压制类（闸门、幂等、版本三元组、名录保持、边表）全部拿掉后，剩下的能自圆其说的"法律数学"是：`General.lean` 22 条（其中 P083 四定理链、P042 min 三元上界、P097 守恒、P052 归纳 iff 都是真一般式）+ 老线 FullMath/Probability 与 BusinessRoot/Analytics 的 ℚ/ℝ 部分 + Dung/Horn 不动点老根。一句话：**能撑起一个"有数学的骨架"，撑不起"132 项概念的数学统一体"——因为骨架上的肉大多数是 record-field 自等。**

**总答**：部分是。账本统一了，数学没统一；而且真正被"统一"进来的那部分，恰恰是数学最薄的那部分。

### Q3 复杂度：**新线偏复杂，老线偏简单粗暴（计数灌水）**

不是"证明太难"，是**自己给自己造了约束又不执行约束**：

- **P083 四定理链 = Mathlib 现成件的手搓重证。** 你们钉的 Mathlib 里（`.lake/packages/mathlib/Mathlib/Data/List/Sort.lean`）：`:65 def insertionSort`、`:125 theorem length_insertionSort (l : List α) : (insertionSort r l).length = l.length`（就是 GENERAL-B，且同族 `mem_insertionSort:121`、`perm_insertionSort:117` 都是 @[simp]）、`:207 theorem Pairwise.orderedInsert (a : α) : ∀ l, Pairwise r l → Pairwise r (orderedInsert r a l)`（就是 GENERAL-C，一般式，现成）。GENERAL-D 由 `:222 pairwise_insertionSort` 直接给。**代价**：`General.lean:147-264` 约 95 行、20+ 轮 CI。**但**：走这条路要 `rcases/obtain/exact/by_cases` 与 Mathlib import，而 `Batch1.lean:1663-1691` 那份自制白名单把这些全列为"未使用"。→ 白名单必须显式扩容才能简化，我不默认扩。
- **自制白名单没有任何实现。** 任务书说 `scripts/scan_lean_guards.py` 是"tactic 白名单守卫"——不成立：该脚本只有 4 条禁词 `sorry/admit/^axiom/: True :=`（`scripts/scan_lean_guards.py:8-13`），**没有 tactic 白名单，也没有禁 `native_decide`**（而 `Batch1.lean:14` 写着"禁止 sorry / admit / axiom / native_decide"）。全仓 `scripts/ tools/ tests/` 搜 `WHITELIST|TACTIC` 零命中；`git log --follow` 显示该脚本只有 `23c5a31 Initial repository snapshot` 一次提交，从未扩过（没有"临时扩未收回"问题，因为从来没建过）。
- **同型重复**：`cases Nat.lt_or_ge … + if_pos/if_neg` 只 4 处（都在 General.lean），提炼不值；真正重复的是模式 `cases X <;> rfl`（Genealogy 9 处）、`:= by` + 单行 `rfl`（Batch4 61 处）、以及"结构体字段自读"这一整族（见 P2-13）。这类不值得抽象，**值得删**。
- **Bool/Prop 阻抗没清**：P083 学到的教训没铺开——`General.lean:21、343、426、495、514` 仍是 `if decide (…)`（P-052 subsumeComplete、P-097 allocate、P-127 isPrefixChars、P-131 hasCommand 两处）。现在能编，但同型地雷还埋着 5 颗。
- **结构冗余**：`FullMath/Acceptance.lean` 整文件 215 条 + `CompletionAudit.lean` 217 条 = 433 条纯搬运定理，占了 1775 的四分之一；这是"计数复杂度"，直接决定论文数字能不能信。
- **整体回答**：数学本体不复杂，也**不够**复杂；复杂的是包装层。可简化清单共 4 条，全部要么需扩白名单（已标注）、要么纯删（不碰白名单）。

### Q4 错误与遗漏：**发现 19 处**（P0×3 / P1×7 / P2×7 / P3×2）

历史病案复发检查结果：**空真/前提不可满足——未复发**（`: False`、`∈ []`、字面量互斥合取在 Genealogy 全域零命中，两位独立扫描一致）；**`sorry/admit/axiom` 在新线零命中（我按注释剥离后重扫 216 个 tracked .lean，命中仅 4 处且全在 CI 守卫根之外）**；**`#print axioms` 目标 536 个，断链 0**；**越界断言：未发现**（`正当防卫成立|量刑正确|依法成立|substantively correct` 等模式在 Lean 包内零命中，且 `Part6.lean:4-5` 自我声明 "No theorem asserts substantive legal correctness" 与实况相符）。新病主要长在**覆盖账与被指源码的语义错位**上，见下表 P0-1/P0-2。

---

## 2. 扩展维度矩阵

| 维度 | 判定 | 严重度 | 一句话证据（file:line） |
|---|---|---|---|
| D5 深度分布 | 见证级 44%、induction 仅 4.0%、纯搬运 24% | P1 | `FullMath/Acceptance.lean:23` `theorem root_GENERIC_FINITE : Contracts.root_GENERIC_FINITE := …` |
| D6 降级对账 | 正向 8/8 通过；反向失败——TSpectrum 129 处降级注未入台账 | P1 | `TSpectrum/Batch4.lean:541` `/- 降级注：结构纪律层。 -/`（该文件 67/67 条自带） |
| D7 白名单执行面 | 白名单不存在；禁词漏 `native_decide`；扫描根漏 15 文件 | P1 | `scripts/scan_lean_guards.py:8-13` 仅 4 条 pattern；`.github/workflows/lean-build.yml:89` 只扫 `proofs/lean/juris_lean/JurisLean` |
| D8 总谱档位对账 | 实测 27/62/39/4＝`:247` 相符、与 `:279`（61/40）矛盾；32/132 概念无 Lean 锚 | P2 | `法律概念总谱.md:279` "✅27＋📦61＋📋40＋❓4" vs `:247` "📦 62｜📋 39" |
| D9 回执纪律落地 | Python 侧真强制（49 格 / 41 pending / 8 AUTHORIZED，与论文一致）；Lean 侧无 UNCLAIMABLE 类型 | P3 | `tests/spec/test_receipt_ledger.py:71` `assert ledger.effective_claim_level(layer, ("LeanProof","HumanLegalReview")) == UNCLAIMABLE`；全包 `UNCLAIMABLE` 0 命中 |
| D10 交付包边界 | 论文自身口径超出证据面（"全部经 CI 验证""无一条 sorry"） | P0 | `docs/paper-rewrite/paper_cn.md:23` |
| D11 复现成本 | 本地可复跑：`pytest tests/ -q -ra` → 336 passed / 3.28s（临时口径，非 Lean PASS）；清单生成器需 `git rev-parse HEAD` 在干净提交上跑 | P3 | 实测输出；`scripts/ci/generate_theorem_manifest.py:147-149` |
| D12 分卷计划进度 | **UNKNOWN**——本轮未逐卷核对 | — | `docs/master-plan/基线/T谱/R20附件_分卷计划PLAN.md` 未展开 |
| 附加：计数工件绑定 | subject 标签滞后一个 commit | P2 | 见 Q4-6 明细 |

---

## 3. 问题清单（按严重度）

**P0-1｜T 谱覆盖账与它指向的源码互相打脸。**
位置：`theory/spec/lh_alignment/t_p_coverage.jsonl`（T01 行）↔ `proofs/lean/juris_lean/JurisLean/Genealogy/TSpectrum/Batch1.lean:81`
覆盖账：`{"t_id": "T01", … "theorem": null, "relation": "EXACT", "coverage": "FULL", "status": "COVERED"}`；源码：`T01 完整陈述仍缺：`。全量：127 行全 `COVERED/FULL`，124 行 `theorem: null`，源码侧 `降级注` 129 处、`完整陈述仍缺` 40 处；`Batch4.lean` 67 条里 61 条闭 `rfl`、6 条 `decide`，61 条形状是 `(T.mk …).field = 字面量`。论文 `:144` 采信该账："覆盖账 127/127 全 COVERED"，`:150` 更把它升为"唯一口径"。
修复：覆盖账字段改三值（`GENERAL`/`WITNESS`/`SCHEMA_ONLY`），逐条填 theorem 名（Batch4 的命名规范已能机械推出），并把 `降级注` 计数做进门测试——账与注不一致即 fail-closed。
反证路径：打开 `t_p_coverage.jsonl` 任一行看 `"theorem": null`；打开 `Batch4.lean:539-543` 看 `T107_coverage_declared : (AssetCoverage.mk true true).covered = true := by rfl`。

**P0-2｜假锚：T112 量刑双线被锚到解释构造子定理上，且同锚复用。**
位置：`theory/spec/lh_alignment/t_p_coverage.jsonl`（T112、T122 行）↔ `Genealogy/Part4.lean:102`
覆盖账 T112 `"t_title": "量刑双线（规范线+经验线）"` → `{"module": "JurisLean.Genealogy.Part4", "theorem": "isolated_branch_preserved", "relation": "SPECIALIZATION", "coverage": "FULL"}`；而 `Part4.lean:101-104` 是 `/-- Isolated evaluation preserves the constructor family before any comparison. -/ theorem isolated_branch_preserved (i : Interpretation) : (evaluateIsolated i).method = methodOf i`（法律解释五构造子）。同一条定理同时是 T122"解释构造子（五方法具名）"的锚。
修复：T112 改 `OPEN` 并写明 open_reason（真实落点只有 `Batch4.lean` 的 `DualTrackSentencing` rfl 占位）；门测试禁止一锚对多 T。
反证路径：`grep -n '"T112"' theory/spec/lh_alignment/t_p_coverage.jsonl` 与 `sed -n '101,105p' proofs/lean/juris_lean/JurisLean/Genealogy/Part4.lean` 对读。

**P0-3｜论文声明"全部经持续集成权威验证，无一条 sorry"不成立（口径错位）。**
位置：`docs/paper-rewrite/paper_cn.md:23`；实体在 `proofs/engineering_proof_artifacts/banach/BanachEffectiveNodes.lean:153`
论文：`全仓定理声明一千七百七十五条（绑定清单工件），全部经持续集成权威验证，无一条 sorry`。实测：清单作用域 `all_tracked_lean` = `Every git-tracked .lean file under proofs/.`（`theorem_inventory_v3.json` scope_definitions），该 216 文件里 4 条 `theorem` 的证明体就是 `sorry`——`BanachEffectiveNodes.lean:153 sorry  -- Needs Mathlib iterate lemmas`（属 `:145 theorem convergence_rate`）、`strict_proof_baseline/lean/BanachEffectiveNodes.lean:96`（属 `:71 pricingFunction_has_unique_fixed_point`）、`.../FiniteGaloisAdjunction.lean:118`、`.../FiniteRosetta.lean:111`。这 4 个文件都在守卫扫描根之外（`lean-build.yml:89`），所以既不报警也照样计数。
修复：三选一——把 1775 缩到守卫根内口径并在论文写"作用域=JurisLean 包"；或把这 4 条声明改成 `UNPROVED` 载体（`def … : Prop`）；或把守卫根扩到全部 tracked .lean。我倾向后者+前者同时做。
反证路径：`grep -n sorry proofs/engineering_proof_artifacts/banach/BanachEffectiveNodes.lean`；再用 `python -c` 对 `theorem_inventory_v3.json` 的 `declarations` 查该文件 `theorem_count=9` 且含 `convergence_rate`。

**P1-4｜军令四件（胜率管线 / 结构同构 / NN 证书 / 博弈）在 Lean 无实承载。** 证据见 Q2 判据 4 各行。修复：按军令序 PR-01..03 先做"把 `win_model.py` 的 Beta-binomial 尾概率抬成 Lean 定理（ℚ/ℝ 有限和即可，Mathlib `Finset` 够用）"，NN 军令改成可证伪目标——现结构体里 `errorBound ≤ tolerance` 是字段，必须改成"由可计算的 Lipschitz/次模界**导出** errorBound"才叫证书。反证路径：`sed -n '53,80p;98,110p' proofs/lean/juris_lean/JurisLean/BanachCertificate.lean`。

**P1-5｜"同构统一"缺共享内核，且新线几乎不接 Mathlib。** 证据：`rg '^import' Genealogy/` 14 文件 25 行全是线性链；`Genealogy` 仅 `Part3.lean:2` 引 Mathlib；`Part4.lean:543` vs `General.lean:147` 双份 EVPI 模型。修复方向（最小动作）：定一个 `Genealogy/Prelude.lean` 放序结构+有限载体+金额代数，Part/Batch 只准 import 它，禁自造 carrier。反证路径：`rg -n '^import' proofs/lean/juris_lean/JurisLean/Genealogy/`。

**P1-6｜公理审计按全仓口径主张，实覆盖 536/1799（30%）。** 证据：`theorem_inventory_v3.json` `print_axioms_distinct_targets: 536`；`FullMath/**`、`Genealogy/TSpectrum/*` 自身 audit 行数为 0（审计集中在 `AxiomAudit.lean` 327 条 + 4 个驱动文件）；Genealogy 300 条里 298 条被审（缺 `Part4.lean:560/568` 两条 P083 旧见证，已被 `General.lean` 一般式取代——这部分台账 `:40` "142 定理全入 AxiomAudit" 我实测 140/142）。论文 `:150` "公理审计全绿"紧跟 1775 出现。修复：把"全绿"限定为"536 个已登记目标全绿"，并补 FullMath/Probability 的 `#print axioms`。反证路径：`grep -c '^#print axioms' proofs/lean/juris_lean/JurisLean/AxiomAudit.lean`。

**P1-7｜tactic 白名单只存在于注释里。** 证据：`scripts/scan_lean_guards.py:8-13`（4 条禁词、无白名单、无 native_decide）↔ `Batch1.lean:15` "tactic 仅使用白名单中的 rfl / decide / cases / simp / induction"、`General.lean:8` 同调。修复：要么实现白名单扫描（列禁词之外再加正向白名单），要么删注释改用"未使用清单"措辞。注意：白名单一旦成真，Q3 的 Mathlib 简化就必须先扩白名单——两件事必须一起决定。

**P1-8｜守卫根漏 15 个 tracked .lean（含全部 4 个 sorry 文件）。** 证据：`lean-build.yml:89`；`git ls-files '*.lean' | grep -v ^proofs/lean/juris_lean/JurisLean` = 15 行。修复：根改 `proofs/`，并把 CI 里"生成 Lean 文件的 `git diff --exit-code`"两类（`SevenAxisCases.lean`、`CompletionAudit.lean`）保留。

**P1-9｜未登记降级远多于登记的八处。** 证据：`03_证明战役台账.md:43` 登记 8 处（P-042/073/083/084/097/099/127/131，正向核：`General.lean` 对应 8 组 `-GENERAL` 定理名全实存且 4 条真用 induction/omega）；反向：TSpectrum 129 处 `降级注`、40 处"完整陈述仍缺"、Batch4 67/67 无一条一般式，均未入台账。修复：把降级登记从"人写八条"改成"脚本抽注释"。

**P1-10｜1775 里 24% 是契约搬运定理，不是数学。** 证据：`Acceptance.lean:23-33` 起 215 条 + `CompletionAudit.lean` 217 条，一行式 `theorem X : Contract := Proof`；`rg -c '^theorem \S+ : [\w.]+ := [\w.]+$'` 全仓 433。修复：这类改名 `example`/`def`-carrier 或单列"绑定计数"，与"定理计数"分开报，别让论文正文用它撑场面。

**P1-11｜概率真数学在编但不在审。** `FullMath/Probability/` 13 文件有 ℝ/ℚ 级结果（`Brier.lean:20`、`Misspecification.lean:15`、`Conditioning.lean:62`、`BetaInterval.lean:15,63,71`），但 AxiomAudit 的 9 条 import（`:1-9`）不含 FullMath，故其公理面未登记。修复：AxiomAudit 增引 Probability 簇。

**P1-12｜`JurisLean.lean` 根不含 FullMath/Genealogy 之外的老线全量；FullMath 仅由 CI `--all` 计划编译。** 证据：`rg -ln 'import JurisLean.FullMath' proofs/lean/juris_lean --glob '!**/FullMath/**'` 零命中；`scripts/ci/changed_lean_modules.py:60-62` 的 `--all` 走 `rglob` 才纳入。风险：任何只跑 `lake build`（默认 target `lean_lib «JurisLean»`，`lakefile.lean:6-7`）的环境都不会编 FullMath——本地/第三方复现者尤甚。修复：把 FullMath 与 Genealogy 显式并入根，或在 README 写明"必须用 all-module plan"。

**P2-13｜见证冒充一般式（8 例，全部我逐条读过）。**
① `Part1.lean:32` `theorem source_grade_total (k : SourceKind) : admissionGrade k = admissionGrade k := by cases k <;> rfl`——结论是 `f k = f k`，`rfl` 即可，名称承诺"全序/total"。
② `Part6.lean:375` `listed_action_requires_its_gate (action) : actionRequiresGate action (requiredGate action) = true`，而 `:371` 定义是 `decide (requiredGate action = gate)`——对任意函数都成立，与人闸表无关。
③ `Batch1.lean:1068` `check_af_sound (accepted : checkAF summary = true) : AlternationFree summary`，而 `:1065 AlternationFree := checkAF summary = true`——P⊢P。
④ `Batch1.lean:1257` `progressive_and_multiplier_correct … := ⟨rfl, rfl⟩`——两个合取支就是 `:1247/:1252` 的定义体。
⑤ `Batch1.lean:1331` `route_and_exclusion_sound` 的每个合取支都是假设记录的字段投影。
⑥ `Batch2.lean:307` `priority_waterfall_monotone` 结论 = `:301` 结构体字段类型；`Batch2.lean:189` 同型（`conservationLaw` 字段）。
⑦ `Part3.lean:137/142` P-051"定理级收口"两条：`supplied` 定义为 `fun _b => inputs`（`:126`），`record` 常量返回唯一构造子（`:133`），故均 `:= rfl`。设计意图（输出类型没有 Judgment 字段）是真的、也是好的，但它是类型设计，不是定理内容。
⑧ `General.lean:402` `P099_progressiveTax3_nonnegative … ≥ 0 := by omega`——由余域是 `Nat` 即真，与税模型无关。
修复：①②③⑤⑥改 `def`/`example` 或补真前提；⑦保留但在 docstring 明写"类型层边界，非定理内容"；⑧并入 `-BRACKET` 族即可。反证路径：逐个 `sed -n` 打印，每条 3 行内可见。

**P2-14｜退化定义 4 例。** `Batch3.lean:186` `def deterministic (s : LogisticSpec) : Bool := true`（丢弃参数，唯一依赖定理是 `true = true`，名带 Logistic 却无回归）；`Part6.lean:167 compliant (r) := r.disclosed` 使 `:170/:175` 成字段读取；`Part6.lean:189 blockHallucination | [] => false | _::_ => true` 通配吞掉内容，使 `:194 detected_pattern_blocks` 只证"非空表非空"（同型复制于 `Part4.lean:108`、`Part4.lean:289`）；`Batch3.lean:91` `decide (d.alpha ≥ 0 && d.beta ≥ 0)` 对 `Nat` 恒真。修复：让这些函数真消费参数（按模式匹配枚举内容、按系数判确定性），否则删除。

**P2-15｜32 个概念无 Lean 锚，3 个 ✅ 概念锚指 Python。** 证据：p_registry 实测 100/132 含 `.lean` 锚；`P-013`、`P-044` 的 `anchors` 只有 `.py`（`theory/spec/temporal_applicability.py`、`theory/burden_of_proof_tracker.py`）却在总谱 `:94/:137` 标 ✅（图例 `:73` "✅已证（Lean 定理）"）。注：P-044 的 Lean 定理确实存在（`FullMath/Burden/DomainAgnostic.lean:37,46,53,65`）只是没挂锚 → 属锚缺失而非虚报。修复：给 3 个 ✅ 补 Lean 锚，给 32 条明确标 `CONTRACT_ONLY`。

**P2-16｜计数工件 subject 滞后一个 commit。** 证据：HEAD 里的 `theorem_inventory_v3.json` 记 `subject.commit = 1488685…`，但对 stated subject 逐文件 `git show` 重算 sha256，**216 个里 1 个不匹配**（`Genealogy/General.lean`），而对 `bd364c5` 重算是 0 不匹配。根因在 `generate_theorem_manifest.py:147` 取 `rev-parse HEAD`——生成于改动提交之前。定理数（1775）两处相同，故只是绑定错标不是数字错。修复：生成后 `git commit --amend` 之外，加一步 `--subject-from-tree` 校验，或生成物落笔后立即在下一 commit 重跑并让论文只引 CI run。反证路径：一条 for 循环对 `d['files']` 比 `git show <subject>:path | sha256`。

**P2-17｜总谱自审数字与自身表格矛盾。** `:247` "✅ 27｜📦 62｜📋 39｜❓ 4" 与实数一致（我按行解析 132 行，27/62/39/4）；`:279` 却写 "✅27＋📦61＋📋40＋❓4"，且同条自称"已重算定稿"。修复：改 `:279` 一处。

**P2-18｜`if decide` 同型风险残留 5 处。** `General.lean:21,343,426,495,514`。修复：按 P083 已验证的路子改 Prop 级 `if`；或是有意保留（simp 形状更稳）则在注释里写明并加一条门测试。

**P2-19｜论文 5 处数字主张只 1 处具名 CI run。** `:144/:147/:150` 说"CI 全绿/CI 验证/具名 CI 运行"却不给号；仅 `:145` 给了 36258901155（我核：真实、`success`、`headSha=bd364c5…`、push 事件）。修复：三处补 run 号 + 作业名。

**P3-20｜L3 桶头计数错。** `:129` 声明 "（P-039..P-051，13 项）" 实际 14 行（P-052 在桶内）；`02_复用总账.md:206` 注②已知此事，故属总谱未同步。

**P3-21｜论文稿面瑕疵。** `paper_cn.md:141` markdown 断裂（`**结论：…才叫不可信。}` 粗体未闭合且多一个 `}`）；`:153` 结尾 " readers。" 是占位（带前导空格的中英混排）；`:3` 仍写"英文同构稿随后"而 `paper_en.md` 已在库。

---

## 4. 统计附录

**口径先说清**：以下全部是静态文本测量（注释剥离后正则），不是 Lean  elaboration 证据；Lean 权威仍是 CI。深度分类的"见证级"判据＝**语句在去掉 `theorem 名字` 之后不含任何 `(`/`{`/`∀` 绑定**，即按定义只能是闭语句见证——这条不依赖我的品味。工程/数学词分类是我自建的关键词表，只用于给量级，不作为单条判定。

**表 A｜D5 收尾与深度（1799 条 theorem+lemma，全 tracked 216 文件）**

| 轴 | 数 | 占比 |
|---|---|---|
| 收尾为 term-mode（`:= 项`，含别名与投影） | 790 | 42.5% |
| `exact` / `simp` / `decide` / `rfl` / `cases` / `rw` | 297 / 263 / 101 / 80 / 70 / 60 | 16.0 / 14.1 / 5.4 / 4.3 / 3.8 / 3.2% |
| `norm_num` / `linarith` / `omega` / `induction` | 26 / 25 / 14 / 7 | 1.4 / 1.3 / 0.8 / 0.4% |
| **语句无绑定（见证级）** | **791** | **44.0%** |
| 使用 `induction` | 72 | 4.0% |
| 使用算术族（omega/linarith/norm_num） | 130 | 7.2% |
| 一行式契约搬运定理 | 433 | 24.1% |

**表 B｜数学 vs 工程 vs 见证（分线）**

| 线 | 条数 | 见证级 | 含工程词 | 含数学词 |
|---|---|---|---|---|
| FullMath | 744 | 473 (63%) | 15 (2%) | 102 (13%) |
| Genealogy（新统一线） | 300 | 153 (51%) | 46 (15%) | 95 (31%) |
| 其他根级 | 437 | 91 (20%) | 82 (18%) | 129 (29%) |
| ULM* | 145 | 1 (0%) | 7 (4%) | 49 (33%) |
| BusinessRoot | 113 | 70 (61%) | 53 (46%) | 13 (11%) |
| UnifiedV2/V21 | 60 | 3 (5%) | 8 (13%) | 21 (35%) |

Genealogy 内部分布：`General.lean` 22 条 / induction 8 / 见证 0；`Boundary.lean` 5 条 / 见证 0；`TSpectrum/Batch4` 67 条全部 `rfl|decide` 且 61 条为字段自读；`Part4` 40 条（见证 19+15）。

**表 C｜四层覆盖**

| 层 | 定理级承载 | 实质 |
|---|---|---|
| 本体 | Hohfeld 4（`Hohfeld.lean`）、DDL 3（`DDLDefinitions.lean`）、Dung/Horn 不动点群、Part0-3 群、KernelV3 14 | 厚，但 Part 侧多为小模型见证 |
| 计算 | `ExactNumericContract.lean`、`clamp` 六定理、`P097_allocate_conservation`、`P099_*`、`FullMath/Numeric`、`BusinessRoot/Analytics.lean:99` ℚ 期望守恒 | 中，老线比新线更硬 |
| 压制 | Part6 23 条、`SafetyTheorems`、`UnifiedV2/FiniteContract` | 密但数学薄，且 4 条字段投影 |
| 行为主义 | Batch4 占位（T81/T112 rfl）+ Python（`action_decision.py:147` 自称非纳什） | **最薄，四问之痛的正面** |

**表 D｜P 号缺位清单**：总谱 132 行 ↔ Lean 里以 `Pxxx` 形式出现的 75 个 namespace 全实存；57 个 P 号在 Lean 文本中不以任何形式出现（`P-001,004,005,006,007,008,011,013,016,017,025,026,027,028,030,031,032,033,037,039,040,041,043,044,045,046,053,054,055,056,059,067,069,071,072,075,076,077,088,090,091,092,093,101,104,108,109,110,111,112,113,115,116,118,119,120,123`）——其中 32 个在 p_registry 里连 `.lean` 锚都没有（名单见 P2-15）；其余靠老线文件锚（ULM*/Dung*/ExactNumeric*），**但 P 号本身不出现在 Lean 源码里，所以"按 P 号回溯定理"在编辑器层做不到**，只能靠 p_registry 这一跳。

**本地实测（临时，不是 Lean PASS）**：`python -m pytest tests/ -q -ra -p no:cacheprovider` → **336 passed in 3.28s**；清单摘要 1775/24/216 与 HEAD 一致；216 文件 sha256 复算 0 失配（相对工作树）。

---

## 5. UNKNOWN 清单

1. **D12 十一卷分卷进度**：未逐卷读 `docs/master-plan/基线/T谱/R20附件_分卷计划PLAN.md`，不对"哪卷空着"下任何结论。
2. **复用总账逐条锚点抽样**：只核了三档算术（57/41/34=132 全对）与 p_registry 侧 288 锚零断链；**未**按任务书要求对 X/Y/Z 各抽 ≥5 条核"档位名实相符"。（该项有一个后台核查在跑，尚未回报。）
3. **CI 工件内容**：我只用 `gh run view` 核了 run 的存在/结论/headSha/作业清单（4 个 run 全 `success`，push 事件跑 python-gates + lean-full-clean-build + axiom-audit + release-certificate + final-gate），**没有下载 artifact 逐字读** `axiom-audit.raw.txt` / `lake-clean-build.log`。故"输出仅含 propext/Classical.choice/Quot.sound 三标准公理"我**无法证实**（源码里 `#print axioms` 的 536 个目标名实存 0 断链已证，但其打印结果不在仓内）。
4. **双侧一致抽 5 对**：只做了形状比对，未逐对做数学等价性论证。已发现的口径差异（供你判断，不作 FAIL 定级）：P-099 Python `progressive_tax(taxable, brackets)` 任意档表 vs Lean `progressiveTax3` 固定三档；P-127 Python `delivery_contracts.py:127 return self.cited_text in self.snapshot_text`（**子串**）vs Lean `isPrefixChars`（**前缀**），而论文 `:133` 只登记了"前缀而非任意子串"这一侧；P-083 Python `negotiation_contracts.py:156` 用 `sorted(enumerate(items), key=(-evpi, idx))`（Timsort）vs Lean 手搓 insertion sort——**同名概念，两侧不是同一个算法对象**。
5. **历史病案②（Iff 结论误用 rfl）**：未做定向全仓扫（`Iff.rfl` 用法本身合法，需逐条看结论式）；我只在 Genealogy 内看到 `mapping_complete_iff_all_required_traced := Iff.rfl`（`Part3.lean:172`，定义即结论，见 P2-13⑦），未见错误用法，但不等于全仓无。
6. **`docs/formal-release/ALLOWED_CLAIMS.md` / `FORBIDDEN_CLAIMS.md` 全文逐条比对**未做（D10 我只从论文侧取证）；AGENTS.md《Prohibited Claims》12 条我抽查未见违反（"Banach complete"、"38 constants calibrated"、"privacy established"等禁语在论文/台账中零命中，另 `BanachCertificate.lean:14` 主动声明未claim Banach 定理）。
7. **README 复现演练**只做到"我自己在本地跑通 pytest 与清单核对"，未演练"新工程师从零"路径，故 D11 判 P3 而非 PASS。
