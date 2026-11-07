# 剩余分支收束：2026-11-07

基线：main `9d62642851592b0aac751c9c0735abeb4f905a18`。本轮保留 main 的现有树与原有关债结果，显式迁入尚未承接的数学内容；合并父提交同时保全原分支历史。

## 来源与落点

| 来源分支及提交 | 收束方式 |
|---|---|
| formal/grouped-split-20261027 — a115a58c1e16cb39d901fb596f49a542c7cea240 | 迁入 LearningSplit20261027 及其独立驱动，复用当前 EventSplitObservation；保留六个测量分组命题，增加来源测量到事件的解析条件下与 eventSplit 输出一致的证明，以及同事件可被任意测量分组拆开的反例。 |
| formal/original06-finite-examples-20261031 — d04e2c5e02f2cc446157bbf3b57a9a79ec264ad4 | 迁入 U06_OriginalFiniteExamples20261031 及其独立驱动，保留七个原有命题；证明旧有限表等于主线轨迹期望效用、旧最小值等于主线最坏分支值、唯一稳健最优结论转入主线，以及二次效用使用当前 Bernoulli 测度和 cashOutcome。 |
| paper/cn-walls-20261031 — 8a3671353c7af0cf89ece854c304a32ad5a1a6d5 | 旧 Twelve.lean 的有效内容由下表所列主线定义、一般定理和实际消费者承接；保留来源提交，不把旧重复类型、True 占位和错误证明引回当前源码树。 |
| paper/codex-cn-ops-v4-20261101 — 3f82db702098d0e4bc5816f09e938a67cb947f2e | 已是基线 main 的祖先，5a0eb465 已合流，后续主线修复保留；无需再移入源码。 |
| cursor/formal-tail-cand8-1dc1 — 95aa2666 | PR #25 在 ba9f6b78 完整承接，FormalTail20261024.lean 与基线相同。 |
| formal/close-u01-debt-20261027 — cdae3ee9 | PR #60 在 7d438f89 完整承接，后续主线继续关债。 |
| tip-pin-expand-cand5bis-20261025 — 4d632106 | PR #16 在 db2a46dc 完整承接，原具名验证材料仍在主线。 |
| candidates/final20261021-825792b、ci/unified-construction-20261008 及各旧本地 main | 提交 5db4e045、825792b8、60a809ba、3e8d2e5f、3f1b4d16 均为基线 main 的祖先。未提交内容独立保全，不由提交祖先关系推定已承接。 |

前两组 Lean 文件位于 `proofs/lean/juris_lean/JurisLean/Candidates/`。新增桥接依赖主线现有模型，原冻结模块与其成功回执字节保持不变。测量分组仍不替代原题 01.3 的事件分组。

## 旧 CN 十二制度逐项承接

以下路径前缀均为 `proofs/lean/juris_lean/JurisLean/CN/`。

| 旧 Twelve 范围 | 当前主线承接 |
|---|---|
| 民事行为成立、有效、无效与撤销权 | Revision20261101/Rights.lean 的 CivilActLife、revocableLife、revokeLife、revocation_keeps_establishment；Completion20261105/Institutions.lean 的 revoke_effective_and_power 与 revocation_removes_tracked_relations。无效不能与有效并存由同一 CivilActLife 的 effective_not_invalid 约束。 |
| 代理与本人能力 | 同一 Rights.lean 的 Agency、delegate、delegation_keeps_principal_capacity；Institutions.lean 的 delegation_actual_capacity、delegation_norms_unchanged。 |
| 管辖分支优先次序 | Rights.lean 的 jurisdiction、ordinary_needs_no_agreement、appearance_cannot_override_exclusive；InstitutionRules.lean 的 jurisdictionCheck 和 Institutions.lean 的 jurisdictionQuery。 |
| 证据能力与证明力 | Revision20261101/World.lean 的 admittedView、admitted_implies_raw；Institutions.lean 的 burdenQuery。 |
| 善意取得 | Rights.lean 的 AcquisitionParties、ordinaryAcquisition、proven_bad_faith_fails，增加 undetermined 保持；InstitutionRules.lean 的取得路径与实际 acquisitionQuery 消费。 |
| 共同犯罪个别投影 | 旧 membership_not_copy_extra 只有存在量词和 True，未表达不复制行为；InstitutionRules.lean 的 liableFor、twelve_yi_e2_not_copied，以及 Institutions.lean 的 excess_not_copied 才表达并证明该内容。 |
| 破产受理截止 | InstitutionRules.lean 的 cutDay、onAcceptance、staySelected；Institutions.lean 的 cut_at_acceptance、cut_after_acceptance、interestFromCase、other_interest_unchanged。旧证明把 acceptedAt ≤ t 错推为 ¬t ≤ acceptedAt；主线已覆盖相等边界。 |
| 国家赔偿第四轨 | Rights.lean 的 LiabilityTracks；Institutions.lean 的 compensation_other_tracks 保持其他三个实际账本；替代旧 four_track_no_sum : True。 |
| 基本权利 rank 与权限分离 | Institutions.lean 的 normRank、constitution_top、rights_conflict_preserves_L。 |
| 意思表示解释作用域 | Institutions.lean 的 interpretLocal、interpretation_other_contract、interpretation_preserves_N；实际比较另一个合同的后态，而不止返回目标合同 ID。 |
| 既判力人、物、时 | Rights.lean 的 BindingIndex、withinBinding；InstitutionRules.lean 的 twelve_res_miss_person/time/subject 与 twelve_outsider_not_auto_remedy；Institutions.lean 的 resJudicataQuery。 |
| 八类引擎输出与候选 | Completion20261105 的 EngineTypes、EngineConsumers、InstitutionRules 中的 consumeEngine、twelve_no_permit_no_bridge，以及 Institutions.lean 的 engine_proposal_only。 |

本次收束的目标是把各来源的有效成果与提交历史集中到 main。CN 中九算子与十二制度/八引擎的完整生成语义及保义覆盖，继续以 main 的具名命题为准；分支合并不新增该定理。

## 验证方式

新独立驱动分别检查八个测量分组目标和十一个有限例子/连接目标。GitHub Actions [changed-module 42378218776](https://github.com/laubeing-droid/legal-math-modeling/actions/runs/42378218776) 在源码提交 `96480727c4e31f54dd1f0c9e126b7e0323590a4d` 编译四个新增模块及其依赖成功；job `128420130485` 的原始输出逐个列出十九个目标的类型和标准公理依赖。通过后接入根入口，再对合并结果运行完整主线流程，当前完整验证状态以该提交的 Actions 为准。

工作目录收束前，逐工作区保全未提交、未跟踪和忽略文件，并为五个原 Git 数据库保全提交历史。归档在项目工作区的独立收束备份目录，原件在归档校验完成之前不删除。

旧证据仍比对原始 subject 的源码。压缩合并后删除来源分支会使普通全历史 checkout 缺失这些对象；完整 CI 从既有 verification.json 读取原始提交，按精确 SHA 取回缺失对象到 `refs/verification/subjects/*`，不恢复开发分支，不改写旧回执。全新克隆已验证 PR 历史及改写前提交均可取回，90 个原始验证 subject 都有对应对象。

## 未提交材料的实质承接（2026-11-07 至 11-08）

本阶段基线是 main `23e6dcbb6242f790d1740244c84473c32d880688`。原九个工作目录归档共 4,712 个文件；逐文件记录原路径、Git blob、主线匹配、承接或去留理由。审查覆盖候选源码、测试、五份待应用 diff、未提交 CI 索引、嵌入脚本的证明片段，以及历史回执。完整逐项清单留在工作区的收束核查目录。

| 原未提交成果 | 当前实际承接与修正 |
|---|---|
| appropriation_grounded / P-097 测试 | `theory/spec/computation_contracts.py` 的 `allocate_grounded` 接收有主体和义务身份的债项，在确定约定、指定或法定次序后消费既有 `allocate_payment`。560 的同序债项按精确有理比例分配，修复旧整数余数法对小额分数付款的失真；561 限于同一义务。未知担保、比较依据缺失、重复顺序不能形成分配。对应现有 batch3 测试。 |
| observation_ledger / S3S7_Bridge / S7_WellFormed_Carrier | `theory/spec/probability_pipeline.py` 在实际频率统计和既有 `win_model.fit` 入口统一按事件身份去重；同身份不同观测字段直接拒绝。`LearningSplit20261027.lean` 复用现有事件行，证明有效计数加法、后验桥、重放不变与冲突拒绝，并把事件后验连到既有 `Seams.Probability.BetaGenModel` 的读数。 |
| law_source_v2 的确定部分 | `theory/spec/source_contracts.py` 的 `select_indexed_source` 按层级、全名、可选版本和显式适用时点选源，实际调用已有 `temporal_applicability.effective_at`；拒绝缺失/倒置区间及重叠版本。外部抽取、案件链不随纯选择逻辑一起推定完成。 |

有效计数载体不是另起一套后验模型：`accepted_event_posterior_is_existing_beta_readout` 明确比较同一批事件的计数后验与既有 Beta 模型读数。新增十项目标均纳入原有 `LearningSplitAudit20261027`，与原八项分组目标一起检查。云端 [changed-module 42388046568](https://github.com/laubeing-droid/legal-math-modeling/actions/runs/42388046568) 在源码提交 `c177f29dd6f53dd186beef823534da23af209083` 编译及十八个公理目标检查通过。三个相关 Python 测试文件共 107 项合成测试通过；完整流程结果由本次 PR 及合并提交的 CI 绑定。

以下内容没有回灌：S0 候选的 w4 同时要求终止位为真和为假，w7 改变的 eventTag 又未被终止函数读取；逐槽可观察不等于联合表示覆盖。旧 GapStatements 的后验命题直接返回其同一前提。旧 S2 “条文实例待登记”仍能通过非空检查。有效泛型回缩、E01 区间消费则已由当前 `Final20261021/Representation.lean`、`SourceRepresentation20261027.lean` 和 `FullMath/Probability/E01Contract.lean` 承接。

五份 release-scope-proposal diff 所涉及的全部旧 inventory 路径都在当前清单中；预览的 238 个 import 均在当前根入口的传递闭包内；旧 401 个 CI run 已全部进入当前索引，概念账 C14 原文仍保留。旧未提交索引的 399 个 run 也已全部承接。派生数字由现有生成器重算，不应用旧数字补丁。

保留未闭合的外部法条/案件探针原件：旧脚本将判决日、失效日和适用时点混用，外部 r33 与法条库虽在本机存在，完整案件语义尚未接入本项目。旧 DOI 工具会漏掉首个 BibTeX 条目，且短词表相似度不足以确定文献身份，留作待修原件。旧 RSI 人工流程锁仅作历史参考，不作为新的数学债务或发布门槛。主线原有关债流程的用户决定保持不变。

历史证据按内容去重后保留，提取副本与原 artifact 内成员逐字节相同者只留原 artifact。七个 Git 历史包合成一个后在空仓库实际恢复，174 个引用一致，120 个不同旧头全部覆盖，并通过完整性检查。旧包和旧目录仅在本次主线承接及完整验证通过后清理。

## 七份待核材料的续核与承接（2026-11-08）

本阶段基线为 `31828be6e0028b5838afe980fd69255571308218`。下表逐项处置上一阶段的七份 `RETAIN_PENDING` 原件；原路径均相对于归档的 `worktree-05/`。原件保留历史用途，主线不加载归档里的程序。

| 原文件 | 实质核查与本轮承接 |
|---|---|
| `theory/spec/candidates/law_source_v2.py` | 精确层级、全名、版本、已知适用区间继续复用既有 `select_indexed_source`。新增同文件的 `bind_indexed_rule` 把选定快照、版本和非空条文定位绑定到既有 `LegalRuleRecord`，与规则原有范围取交集；实际案件入口消费所得规则。旧版从文件名猜生效日、从一部法的废止条款推整个法库、动态导入本机 r33 的实现淘汰。 |
| `tests/spec/test_r33b_law_source_v2.py` | 精确身份和拒绝文件名代替生效日的断言已有主线测试；本轮补充条文缺失、快照缺失不能生成可执行规则的反例。旧测试依赖私人绝对路径并在缺语料时 skip，不作为验收测试搬入。 |
| `tests/spec/test_repealed_at_date_seam.py` | 保留明确区间边界、无有效版本即拒绝；纠正“判决日晚于废止日就不能适用旧法”的断言。既有时间合同使用包含两端的日区间：第 6 日切换版本时，旧版本末日为第 5 日。合成测试同时覆盖旧末日、新首日及显式选错版本。 |
| `theory/spec/candidates/case_chain_end_to_end.py` | 金额分配已由上一阶段 `allocate_grounded` 承接。本轮修复现有 `run_case` 和独立检查器把知识截止日当适用时点的问题，法源绑定输出现在直接进入实际规范选择、许可模板和裁断。旧四阶段脚本的占位程序规则、借真实案号配合成金额、没有语义连接的阈值门不承接。 |
| `tests/spec/test_case_chain_end_to_end.py` | 由既有 `test_run_case.py` 中的 `IndexedSourceCaseTests` 替代：合成案实际走到裁断，历史规则有效、新规则不能倒灌、篡改选择被独立验证器拒绝；同时验证绑定不能扩大规则范围。使用 unittest 类，确保现有云端 reference runner 能发现这些测试。 |
| `theory/spec/candidates/case_source_end_to_end.py` | 淘汰。该脚本只按真实语料的判决日选择法律，并用同一个判决日检查自己选择的结果，不能验证适用性；未用 `law_basis` 建立其声称的独立依据，还固定对每部法取第 560 条。通用读取 gzip/CSV 没有需要另建组件承接的独有成果。 |
| `work/verify_dois.py` | 重写到既有 `scripts/check_paper_claims.py`。明确统计全部 BibTeX 条目及有/无 DOI 数，支持首项、嵌套花括号和引号字面值；不支持的宏或拼接显式报错。核对返回 DOI、完整规范化标题、作者、年份和期刊/会议名；不再用短词表交集判通过。提供 `--check-dois` 与 `--doi-metadata` 两种互斥入口；请求编码完整 DOI，异常或字段不一致返回非零。 |

适用时间绑定依据是[最高人民法院民法典时间效力规定第一条及其例外条款](https://www.court.gov.cn/shenpan/xiangqing/282051.html)：裁判日期不能直接替代所判断法律事实及相应过渡规则确定的时点。这里的 `target_day` 是已明确绑定的适用问题时点；`as_of_day` 仍只控制可见知识。不同法律事实、程序规范或过渡例外需要分别给出对应绑定，不由这个区间选择器自动推断。

DOI 请求与元数据字段按 [Crossref REST API 文档](https://github.com/CrossRef/rest-api-doc) 接入；Crossref 未收录或网络不可用记为未核实，不宣称 DOI 无效。DOI 名称按 [DOI Handbook](https://www.doi.org/doi-handbook/html/) 仅折叠 ASCII 大小写；普通文献字段的比较保留 Unicode 内容，不能因中文被清空而误报一致。作者缩写、标题变体或期刊缩写存在差异时明确要求复核。

测试全部使用合成文献、合成法源和合成案件。完整 Python、reference、Lean 与证书结果绑定本次 PR 和合并提交的 Actions；本轮未新增或修改 Lean 命题。旧探针淘汰的理由是已核实的实现错误或已被当前入口替代，不是把外部语料未运行写成通过。

基线代码反例已实跑：`target_day=5, as_of_day=10`，有效期 1–5 的许可规则在旧入口被漏选，结果从应成立变成不成立；有效期从 6 开始的规则则被错选，反向导致成立。本轮两种结果均纠正，独立检查器确认新结果并拒绝篡改选择。`RETAINED_SOURCE_LOCK.json` 仅更新 `pipeline.py` 的当前 Git blob 指纹，沿用既有有意修正后的重锁规则；原源码和原指纹保留在上述基线提交，没有改写历史证明回执。
