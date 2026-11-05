# Actual finite round spending and fixed-root learner changes

Scope: original E15 and 15.2–15.6. Candidate generation calls the existing actual event-update/fitter before validation blocks enter the completion call. It reads the current loaded model and the current learner's proposal tables, saves the visible append-only round-prefix length and retains the actual training poststate. A later completion must match that state and the fixed protected-domain list.

Every evaluated round pays the sum of its actual protected-block deltas, including protected-bound or authorization refusals. The checked cap is preserved by arbitrary finite sequences of generation, evaluation and learner changes. The monotone round number is the business key: an exact request replay returns the original receipt while preserving the current state, and another payload for that key conflicts. Completed attempts retain their block event IDs even if sampling/evaluation was unqualified; renaming a snapshot cannot reuse those events as fresh. Pre-admission key/round failures compute no evaluation. The boundary is this retained service history, not an omniscient claim that external users never saw data.

The fixed checker rejects a different claimed checker, an unbounded-improvement claim, a removed protected domain, stale generation state, reused events, missing predeclared sampling support and an exhausted budget. Unknown generation/evaluation returns no risk guarantee; zero charged budget in that case means no qualified evaluation was issued, not zero failure probability. Computation, interval comparisons, external sampling support, external authorization and actual loading retain distinct evidence in the record and LoadOutcome.

An independent current-context permit may change the finite proposal generator after checking table shape, values and a new version. The next actual fitting call consumes those changed tables. The loaded service, Gamma, fixed mechanism/rules, checker, protected domains and budget history remain unchanged by this learner change. A self-issued or new-checker permit cannot pass the old trusted-root/catalogue contract. This is relative to an externally supplied trusted catalogue and fixed executable checker, not a proof of real legal authority or absolute safety.

Independent [run 40446553400](https://github.com/laubeing-droid/legal-math-modeling/actions/runs/40446553400), [job 121999119450](https://github.com/laubeing-droid/legal-math-modeling/actions/runs/40446553400/job/121999119450), SUCCESS on `5da99fc8cee319bdfb55d46cdcda2cd48df3a293`: 15 exact type/axiom targets and 20 guarded executions, standard axioms only. Both source files match that subject after LF normalization. The actual two rounds load a risk-0 model from a risk-1/2 parent, then reject a changed target while retaining the loaded model and first-round spending. Other executions cover exact replay after a later round, key conflict, reused events, missing/forged sampling support, late candidate timing, changed checker, unbounded claim, budget exhaustion, protected harm, authority refusal, prior unqualified exposure, actual learner consumption, self-issued/new-checker permits, pending generation and malformed tables.

Earlier subjects are retained: `5fcce8f50eeff1e252b5dd03147e0b6a6afea81f` / [40445170629](https://github.com/laubeing-droid/legal-math-modeling/actions/runs/40445170629) failed record syntax and proof case handling; `d3c301d94ce82dcf6c10918b11759330040b8832` / [40445643984](https://github.com/laubeing-droid/legal-math-modeling/actions/runs/40445643984) built the core but failed two audit record layouts; `2cce859d0188638e055ef5a56b997edfe655c469` / [40446024645](https://github.com/laubeing-droid/legal-math-modeling/actions/runs/40446024645) added fixed protected-domain retention and reached the default heartbeat limit in two proofs. The final proof prunes refusal branches before case analysis; it does not increase limits, weaken statements or remove guards.

Construction-card G-PROPOSED correspondence (baseline 825792b83476a767152396d7f5e2ba3017048841): this source/namespace is absent there; later proved dependencies are reused explicitly.

| Symbol | Original obligation | Reuse / new | Actual consumer | Acceptance |
|---|---|---|---|---|
| beginAdaptiveRound | E15 frozen candidate, current learner/history | NEW; reuses prepareNext and actual event fitter | finishAdaptiveRound | actual loaded parent, current proposal tables, real journal post |
| assessAdaptiveRound | E15 qualified evidence, protected tasks, budget | NEW; reuses evaluate/activate | appendRoundRecord | actual block-delta sum, refusal spending, fixed scope, event freshness |
| finishAdaptiveRound | E15 round identity and actual continuation | NEW; exact-request replay and conflict | next generate/assess | original receipt, current state retained, actual loaded post consumed |
| arbitrary_finite_round_actions_keep_budget | 15.3 finite deterministic ledger invariant | NEW; uses proved one-step transitions | any finite list of actual calls | upper cap invariant for arbitrary well-bounded initial state |
| changeRoundLearner | 15.5 theta/phi versus fixed E/N/A | NEW; reuses current Authorization.checkGrant | next beginAdaptiveRound | old checker/catalogue required, actual new proposal consumption |
| learner_change_keeps_service_budget_and_trusted_root | 15.4/15.5 preserved boundary | NEW | subsequent generation and evaluation | service/rules/mechanism/checker/protected set and spent history framed |

The earlier AdaptiveValidation probability theorem and this deterministic runtime ledger are different obligations. Genuine history-conditional iid sampling, fixed targets, source interpretation and the final U00 joint statistical witness still require their exact premises and wiring. This module does not automatically certify every external data source or every future U00 trace. The whole business/measurement/policy/RSI consumer chain remains unfinished. The archive rollback package is separately proved and merged; this batch does not claim rollback automatically bypasses round accounting.

Root integration follows independent success; the audit stays standalone. Full PR ULM/Authority is a separate acceptance. OPEN=20, closes_debt=false, CAND8=8 outside PROVE_CANDIDATES; no discharges/frozen-pin/workflow/toolchain changes or local Lean/Lake/Elan.



## 原题 15.4–15.6 的有限数学归引（2026-11-06 准备附记）

本节登记冻结原题 15.4–15.6 的有限数学证据。复用已验 S131 `94cf001912dbcd215ade40c3ce556f26f68f8ff5`，tree `7d8d6c043039779e8f6f4c4519073e60fcfb7304`。当前为候选登记，完整 PR 验收待该树的门禁和证书。实际消费边及 U00 按各自记录验收。

### 15.4 L107/L109：旧行为、旧风险与法律上下文分别保持

冻结 L107：“设旧任务集合T_old、新任务集合T_new，旧安全观察O_old和新观察O_new。给出升级θ或机制φ后保持旧行为的模拟／非干扰条件，并构造平均性能提高却在一个旧关键任务上失败的例子。有限验证只能覆盖声明分布或测试域，不能证明所有新任务通用可靠。”

冻结 L109：“要求判断：同一更新能否既保留所有旧输入逐点行为，又在相同输入上严格改进错误？明确行为相等、目标风险不劣、法律约束不变三种不同保持概念。必要时否定过强要求，不通过重命名‘兼容’绕开矛盾。”

取 `T_old = Fin m` 和 `T_new = Fin m ⊕ Unit`，用 `q ↦ Sum.inl q` 嵌入旧任务。定义 `O_old(s,q) = predictLoaded s.service q`，并令 `O_new` 的值域为 `ℚ ⊕ RoundLearner`。对 `Sum.inl q`，返回 `Sum.inl (O_old(s,q))`。对新增检查任务 `Sum.inr ()`，返回 `Sum.inr s.learner`。`AdaptiveRoundLedger20261027.learner_change_keeps_service_budget_and_trusted_root` 给出变更前后整个 service 相等，因而每个嵌入旧任务在变更后的观察等于变更前旧观察的 `Sum.inl` 包装。新 learner 的检查结果不受该等式约束。`changed_learner_is_actual_next_generator` 证明许可变更后的 proposal 进入下一次实际生成。此有限实例要求旧查询的嵌入、解释和所读 service 字段保持，覆盖声明中的这些查询和一个新增检查任务。

这一当前状态 frame 不延伸为“未来所有候选加载后旧行为永远相同”。若之后实际更新 θ，须重新区分三种合同：

- 行为保持要求每个旧输入的同一观察相等。`ValidatedFeedbackLoad20261027.refusal_keeps_actual_prediction` 给出拒绝加载时整个实际 loaded 包及所有查询预测保持；成功加载没有无条件的逐点行为 frame。
- 风险保持由 `ProtectedFeedback20261027.bounds_gate_on_joint_event_preserves_each_risk` 及 `ValidatedFeedbackLoad20261027.actual_loaded_risk_follows_computed_domain_bounds` 连接到实际候选/实际 loaded 包。结论是每个声明保护块的目标风险不超过旧风险加该块 tolerance；tolerance=0 才是不劣。它们保留共同有效置信事件及同一目标/损失/域等前提，不是仅看全局平均分。
- 法律上下文保持由 `ValidatedFeedbackLoad20261027.activation_keeps_rules_mechanism_and_training` 给出 Gamma、principal、lossVersion、journal 的 frame；学习器变更保持整个 service、checker、保护域和账本。Gamma/规则/机制保持不等于预测不变或风险不劣，也不等于外部法律真实性已经证明。

`ProtectedFeedback20261027.average_improvement_can_harm_protected_point` 是所需有限反例：权重 9/10 与 1/10 的两点上，平均错误从 9/10 降到 1/10，而旧关键点错误由 0 升到 1。故新任务/平均表现改善不能替代旧关键任务保护。`FormalTail20261024.u15_2_full_agreement_preserves_risk`（复用原 `Final20261021.Iteration.u15_2_preserved_predictions_equal_risk`）对同一有限 law、同一 loss 和所有输入预测相等，给出风险严格相等；在同一输入、同一错误定义下，逐点行为全保留与严格纠错不能同时成立。改变目标、域或损失会换命题，不能通过“兼容”改名规避。

### 15.5 L113/L115：允许参数/候选机制变化，不允许自造权限或替换可信检查器

冻结 L113：“把更新对象分为经验参数θ、候选机制φ、固定计算机制E_mech、外部法律规则N和权限策略A。给一个允许前两者改变、后几者保持或经独立审批证据改变的有类型转换系统。证明当前策略不能仅凭自己产生的‘授权证明’给自己扩展权限；若采用证明携带更新，明确可信检查器及所证明性质，不把能证明语法合格当作现实法律许可。”

冻结 L115：“讨论验证器也被修改时何以发生证明循环。给一个有限信任基或版本化外部检查合同，并说明它解决的是相对可信基的正确性，不是无条件绝对安全。此处不要求也不授权现实系统自行修改检查器。”

现成类型转换选“后几者保持”的分支：θ 是 `TrainingCandidate` 的 fitted table/协议；φ 是 `RoundLearner` 的版本和有限 proposal tables。生成由 `beginAdaptiveRound → prepareNext → processAndFit` 读取当前 loaded 和实际训练 poststate，评估/加载由 `assessAdaptiveRound → evaluate → activate` 完成；φ 变化走 `changeRoundLearner`。E_mech 是固定执行这些转换、`learnerShapeValid` 与 `Authorization.checkGrant` 的程序；N/A 的当前上下文和版本由 service.gamma 及独立授权输入约束。本 API 没有改写上述固定代码或自行替换法律规则/权限政策的操作。

`changeRoundLearner` 检查无 pending generation、每张表长度 m/值域 [0,1]、严格版本推进、permit 存在于外部 catalogue、当前 checker 一致、精确 before/after，以及当前 Gamma 下的 `checkGrant`。`self_issued_or_new_checker_permission_cannot_change_learner` 的实际前提是 permit 不在受信 catalogue 或 checker 不同，结论为原状态不变；它没有声称恶意外部 catalogue 本身不会接纳伪造。`learner_change_keeps_service_budget_and_trusted_root` 保持服务、checker、历史、limit、horizon、保护域；`changed_learner_is_actual_next_generator` 证明新 proposal 的真实使用。参数加载另外经完整 evaluation/sampling/permit 匹配；`replaced_candidate_does_not_reuse_old_permit` 排除把旧许可换给另一候选。

可信基是这些固定代码、当前 checker、外部 catalogue/授权来源以及声明的统计前提。表形和值域证明只证明语法/有限表示合格，不能生成法律许可。若被修改的验证器可自行签名认可自身，再用这份认可为升级放行，会失去独立的信任起点；当前合同用旧 checker 和外部 catalogue 检查新 learner，拒绝声称新 checker 的许可，正是相对固定可信基的有限保证。这里不新增 checker 自修改机制，也不把外部授权真实性、统计真实性或无条件绝对安全标为已证明。

### 15.6 L119/L121：实际两轮和明确终止边界

冻结 L119：“给一份最小、非空的两轮例子：一次真实合格更新、一次因证据不足或范围错配而拒绝，展示状态、候选、指标、风险预算与不变量。再给一个‘两个程序给完全相同有限观测、域外行为相反’的反例，界定不能由这两轮推出的主张。”

冻结 L121：“最后列出一个明确结束判据：该候选相对于声明目标、域、数据和可信基得到何种证明，哪些未证。不得为了完成任务把‘有限可检改进’升级为无限递归改进、通用最优或全法律模型正确，也不得以不存在万能保证为由拒绝给有限可行合同。”

已编译的 `AdaptiveRoundLedgerAudit20261027` 中 `AdaptiveRoundLedgerFixture.firstRound/twoRounds` 串接实际函数，不是只列两个风险数字。它复用 `ValidatedFeedbackLoadFixture.built` 的有限合成训练/验证对象，旧 loaded 表 `[0,0]`、候选 `[0,1]`，同一两点目标标签 false/true；声明保护域 `[10,20]`、每块 400 行、δ=1/20、radius=1/10、tolerance=0，总计划预算 1/10。旧/新两保护块经验错误分别 `[1/2,1]` 与 `[0,0]`。外部 sampling/permit catalogue 是此合成实例的显式输入，不当作现实授权或抽样规律的证明。

| 实际阶段 | 状态与候选 | 指标、额度及保持项 |
|---|---|---|
| 初态 | 固定 checker=55，horizon=3，limit=1/5，旧 loaded `[0,0]` | 同一有限两点风险 1/2，round records 为空 |
| 第一轮 | 实际生成、计算验证、activate/write/read；round.status=`evaluated`，load.status=`loaded`，加载 `[0,1]` | 两点风险 0，records=1，roundSpent=1/10，Gamma/checker 保持 |
| 第二轮 | 从第一轮 post 继续，传入拟合协议的 `lossVersion` 从 7 改为 700，当前 Service 的 `lossVersion` 仍为 7。`(prepareNext …).candidate = .unknown .targetMismatch`，round.status=`generationUnresolved`，没有第二次加载 | 已加载模型风险仍 0，本轮 charge 为 0，累计 roundSpent 仍 1/10，records=2，visiblePrefix `[0,1]`，Gamma/checker 保持 |

这里拒绝的实际枚举是 `generationUnresolved`，不伪写成 `.rejected`；它是范围错配后的 fail-closed 非接纳。第二轮仍留下尝试历史，不能把“保持旧模型”误写为整个可变状态不变。`recorded_prefix_and_next_round`、`recorded_load_is_actual_next_service` 和 `arbitrary_finite_round_actions_keep_budget` 给出相应历史、真实服务和有限费用不变量。上述两轮有现存 `#guard_msgs/#eval` 验收，未在本机重跑。

`FormalTail20261024.u15_2_finite_obs_agree_not_global` 的两个程序为 Bool→Bool 的 old(x)=x 与 new(x)=false；二者在唯一已观察输入 false 上同为 false，在域外 true 上分别 true/false。它直接满足有限观测完全相同而域外行为相反，不需要另造反例。有限观察不能推出全域行为相等；全域预测相等才可使用前述同 law/loss 风险等式。

结束判据限定为：精确候选、当前目标/域/数据、固定可信基与外部 sampling/authority 输入匹配，实际评估与接纳/拒绝记录明确，成功 loaded 能写后读回且成为后续实际父模型，逐保护域风险结论仅在已声明的共同置信前提下成立，有限动作累计额度满足上限。缺项返回其 UNKNOWN/拒绝/冲突，不扩大接纳范围。未证事项保留：现实 sampling/授权真实性、任意新任务、无限未来版本持续改善、通用最优、全法律模型正确和全部 U00 工程闭环。题目要求的有限非空数学合同不以这些更强事项为前提；冻结主线、工程分母与 U00 仍各自记账。

### 既有接受与本次只读 pins

原包 `adaptive-round-ledger-20261027` run `40446553400` / job `121999119450` / subject `5da99fc8cee319bdfb55d46cdcda2cd48df3a293` 的 15 具名目标、20 guarded executions 与 PR43 接受保持。PR39/40 的 `protected-feedback-20261027`（run `40436410064` / job `121965999424`，subject `04942c277eacf3bd7f3b86be1fc353e94b92a9f3`）及 `validated-feedback-load-20261027`（run `40435047031` / job `121961611215`，subject `1314be955e72a2577dc754f9f9d8f8a1b126059f`）原证据不变。旧 `cand8-independent-20261027` run `40356561660` / job `121690497738` / subject `d26bf26022c94abbb61f45be437af514ba73dedd` 为 69 名独立公理输出接受；其历史 CAND8/不提升范围保留。

三条记录共同引用 PR #131 的 Authority 原始构建。其精确 run、job、artifact、checkout 和 tree 见原题表 15.4–15.6 的 `accepted_authority` 证据字段。实际 `lake-clean-build.log` 5612507 bytes，SHA256 `060c462b5d579e904c1253da6d20ab5d6b858ebb48ba2313ac69032b0747150c`：平均改善伤害旧点 L11983–11994；FormalTail 两目标 L12343–12356；加载 audit Built L14286、frame/拒绝/风险目标 L14306/L14347/L14418；round audit Built L16928、frame/反自授/新生成 L17051–17109、有限预算 L17144–17154。两个 Built 是原 guarded driver 编译接受，不冒称本次新执行。`u15_2_finite_obs_agree_not_global` 无公理；round 的 frame 与反自授为 `[propext, Quot.sound]`，`recorded_load_is_actual_next_service` 与 `replaced_candidate_does_not_reuse_old_permit` 为 `[propext]`；本段所列平均改善反例、全域同预测风险等式、加载 frame/拒绝/风险、新生成和有限预算目标为实际 `[propext, Classical.choice, Quot.sound]`。本次登记沿用上述 Lean 源码和原有独立模块证据。

以下为 S131 中直接复用对象的 Git 原字节 pins，源根均为 `proofs/lean/juris_lean/JurisLean/Candidates/`：

| 文件 | bytes | SHA256 | Git blob |
|---|---:|---|---|
| ProtectedFeedback20261027.lean | 23383 | 1afa83764d1ec0231028c6c628b53347a3d6d6543d160d25c4eb40ef4e672851 | f1792782e9617947ab714eb9baf0b4a621d5b560 |
| ValidatedFeedbackLoad20261027.lean | 13591 | 728eef1cb18bbe0073719fde7b0c5ebcf33fc4b340ef32c4fcba07ce03bc56f0 | 748ceaebfb5b119bf8b9c70056df9cdad7dcbb5d |
| ValidatedFeedbackLoadAudit20261027.lean | 10976 | 5a7a3c78bc2116a2357741490a7efb6ffe72ff68da6930f216a8e4f6ecb8f339 | 5f868763b4ffa06f83e832d9661d5cefa28a8f6d |
| AdaptiveRoundLedger20261027.lean | 18250 | 8137187be49e0589cffbadb8e5d0acb73bd017a1e06fbf1166a39b0ec7c8b84c | 2c166e51169957e1ec65f16c39ca4bec7ed8ae30 |
| AdaptiveRoundLedgerAudit20261027.lean | 13165 | 149ee3caee93281b93b8851aebee6cbed4de1563af9c6e58d2375b4087e79301 | 813bae8f408bfaba8ddaaac135deac128c531b03 |
| FormalTail20261024.lean | 61155 | ff86664fb5ccbef8087427ec586ae5b73489d9b2aaba8cb4dd32cfc69802de36 | 2948013348c3cb909b3c18dcc914f0b3cb9846b0 |
| FormalTailCAND8AxiomAudit20261027.lean | 14131 | eef4287ce5fa2b2dd5a07e88f3852ee09a1d7350a835025e2dcf0b2b35b64308 | 084b6596bfd8d1cb7962cc53b96ba170d10225f2 |
| Final20261021/Iteration.lean | 2066 | 48e5d7ecc1ef78752a67dff73e307f3ded58c1d8cab742e9ffbf7ddf2bfb11ea | 7668283ed14b3f8db7929f300c2eb287f5b80ca1 |
