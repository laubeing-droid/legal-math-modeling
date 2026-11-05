# Conditional-history fresh validation and adaptive score leakage

Scope: original 15.2/15.3, correction 13/S15 and E15's mathematical budget. A finite pre-sample visible history fixes the candidate class, sample count, risk budget and continuation decision for each round. The theorem uses the actual normalized restriction of one common probability measure to each positive-mass history cell. Within that conditional measure, the existing iid finite-class theorem derives the single-round event. The finite union and history partition then prove the probability of any conducted-round failure is at most the expected sum of its allocated budgets. Cross-round independence is not assumed. Any predictable finite stopping policy is a history-dependent continuation mask covered by that bound.

This is a finite-history/finite-horizon scheme, as selected in the original finite alternative. The fixed population law, bounded loss, measurable samples, history-conditional iid laws and predeclared classes remain explicit premises. The theorem does not infer these premises from different identifiers or from a candidate's claimed confidence. The sample-count lemma proves the stated log(2M/delta)/(2 epsilon^2) sufficient count for the same actual radius.

The executable attack sends coordinate probes to the actual zero-label validation-score function and constructs a predictor only from the returned scores. General proofs show zero validation error and uniform population risk 1 - |seen|/N, hence at least 1 - n/N when at most n points were seen. The six-point execution observes two points and yields validation error 0 but population error 2/3. This does not refute a correctly paid bound for the entire fixed search class. The literal original four-atom failure table has three disjoint events of mass 1/4, union mass 3/4; the independence expression 37/64 underestimates it.

Independent [run 40439612934](https://github.com/laubeing-droid/legal-math-modeling/actions/runs/40439612934), [job 121976530560](https://github.com/laubeing-droid/legal-math-modeling/actions/runs/40439612934/job/121976530560), SUCCESS on `149dee0f69c9158f43af3c26e61a5bcfce1632be`: 12 exact type/axiom targets and 6 guarded execution checks, standard axioms only. Source and driver match that subject after LF normalization; raw original named output and exact source binding are retained. The first draft `effa0f86680d8d9653407cd52cc32a98e0a27d30` / [run 40438981425](https://github.com/laubeing-droid/legal-math-modeling/actions/runs/40438981425) failed a recursive simplification and an unsplit membership case; the successful subject proves those steps explicitly without changing theorem statements.

Construction-card G-PROPOSED correspondence (baseline 825792b83476a767152396d7f5e2ba3017048841): this new namespace/source is absent there; current later proved dependencies are identified below.

| Symbol | Original obligation | Baseline / reuse | Actual consumer | Acceptance |
|---|---|---|---|---|
| conditional_event_mass | 15.2, conditional-to-global step | NEW; uses pinned Mathlib conditional restriction identity | predictable_failure_budget | finite positive/null history cells handled separately |
| predictable_failure_budget | 15.2 / 15.3, adaptive continuation | NEW; finite measure union bound | predictable_failure_expected_budget | arbitrary finite histories/rounds, no cross-round independence |
| history_budget_is_expected_spend | 15.2, expected spent budget | NEW; actual Bochner integral of the history-dependent budget | predictable_failure_expected_budget | exact partition/integral equality |
| fresh_iid_history_budget | 15.2 / S15, derive validity from fresh conditional samples | NEW; consumes ProtectedFeedback.protected_iid_joint_event | bounded-round statistical contract, runtime consumer still pending | actual conditional iid laws and class-dependent radius |
| sample_count_covers_radius | 15.2, sample cost | NEW; uses current finiteRadius | declared per-round sample planning | arbitrary positive n/epsilon satisfying the displayed count |
| probeScores / fromProbeScores | 15.2, validation leakage | NEW; actual score producer feeds reconstructed predictor | zero-validation/population-risk proofs and driver | general finite N, actual six-point execution |
| three_failure_events_not_independent_formula | 15.3, same-table arithmetic | NEW; actual fourPointFailureMass | exact failure-budget counterexample | all three marginals, union, 37/64 inequality |

Implementation enters the root after independent success; its driver remains standalone. UNLOCATED at this batch boundary: actual round ledger/fresh-block reuse rejection/trust-root and rollback consumers, and whole U00. Existing finite RiskTrace accumulation and finite-rank results are retained; this conditional-sampling proof does not claim those old abstract premises are automatically supplied by every runtime trace. Full PR ULM/Authority acceptance is separate.

OPEN=20, closes_debt=false, CAND8=8 outside PROVE_CANDIDATES; no discharges or frozen-pin change, no local Lean/Lake/Elan, and no workflow/toolchain change.



## 原题 15.2 / 15.3 的有限数学归引（2026-11-06 候选记录附记）

本附记追加到本包原 README，保留此前全部历史文字及原 verification/raw。当前为候选数学记录；本轮记录检查见新证据包，PR 全链接受仍待验。本次只复用 S131 `94cf001912dbcd215ade40c3ce556f26f68f8ff5`（tree `7d8d6c043039779e8f6f4c4519073e60fcfb7304`）中已接受的数学对象，不新增证明、源码或消费者，不把 U00 的全部工程/条件接线视作已解除。

冻结依据是题单 `15_多轮改进验证与能力边界.md` 的 L95/L97 与 L101/L103。原句逐段为：

- L95：“构造一个模型根据验证集反馈反复搜索、最终验证分数很高但目标风险很差的有限例子。即使训练样本从未直接包含验证标签，反馈足够多也可能泄漏选择信息。请指出候选独立于验证集、条件于历史的有效检验、独立新样本、可复用验证机制等不同办法各自需要什么假设。”
- L97：“选择一个可独立证明的有限方案：例如预先固定m个候选并联合控制，或每轮使用新验证块并分配δ_t。给出精确样本量／概率界、停止时刻限制与代价，不必同时解决所有自适应数据分析理论。”
- L101：“在同一有限概率表上定义三个失败事件，手算各δ_i*与并集概率，展示并集界无需独立而乘法界需要额外条件。再说明把某一候选自己的置信输出当其失败率上界为什么不构成证明。”
- L103：“将‘模型内部概率预算’‘统计估计置信保证’‘对所有允许轨迹的确定性不变量’分别给出类型和证明责任。若风险界因漂移、样本不独立或选择偏差失效，应返回何种状态？不得把UNKNOWN解释成零风险。”

### 15.2：反馈反例与明确选择的有限方案

`AdaptiveValidation20261027.probe_score_reveals_membership` 和 `feedback_model_eq_unseen` 描述实际评分接口泄漏：对每个坐标提交探针，只用返回的验证错误率构造 `fromProbeScores`，不把验证标签作为该构造的直接输入。`feedback_model_zero_validation` 证明验证错误率为 0；`feedback_model_population_risk` 证明在同一有限域的均匀目标分布下风险为 `1 − |seen|/N`，`feedback_model_large_population_risk` 给出最多看见 n 点时的 `1 − n/N` 下界。既有六点 driver 固定 seen={0,1}，探针输出 `[1/2,1/2,0,0,0,0]`，构造预测 `[false,false,true,true,true,true]`，验证错误率 0、总体错误率 2/3。若“验证分数”取准确率，它是 1。该反例没有推翻对完整预先固定搜索类已经支付复杂度代价的有效联合界。

本行选择已有的有限历史、有限轮数、每轮条件新样本方案，具名依据为 `conditional_event_mass`、`predictable_failure_budget`、`history_budget_is_expected_spend`、`predictable_failure_expected_budget`、`fresh_iid_history_budget` 和 `sample_count_covers_radius`，均属于 `AdaptiveValidation20261027`。同一概率空间 `(Ω, μ)` 上，轮 t 的可见历史 h 在取本轮样本前确定非空有限候选类、正整数 `n(t,h)`、`δ(t,h)∈(0,1)` 及是否继续的 `active(t,h)`。每个正质量历史单元使用真正的条件测度 `μ[|historyCell]`；在其下，本轮可测样本条件 iid，且同分布于声明的固定目标 P，损失在 [0,1]。零质量单元单独处理。跨轮独立不是前提。

令 `M(t,h)` 为该历史下非空候选类的大小。当前 `finiteRadius` 为 `sqrt(log(2M(t,h)/δ)/(2n))`。对正 ε，选择正整数 `n ≥ log(2M(t,h)/δ)/(2ε²)`，已验样本量定理给出半径不超过 ε。所有实际继续轮的任一候选失界概率至多 `E_μ[Σ_t 1_active(t,history_t) δ(t,history_t)]`，这是同一 μ 上的结论，不是把不同实验的数值预算拼接。一个有限特例预先固定正轮数 T 和总预算 `0<Δ<1`，并取正整数 M 使所有轮次及其历史下 `M(t,h)≤M`。每轮用 `δ=Δ/T`，取 `n≥max(1,ceil(log(2MT/Δ)/(2ε²)))`。提前停止只删除后续轮，因此该期望预算至多 Δ。停止决策必须是本轮取样前历史的函数；可以在本轮观察后决定下一轮是否继续，不能把已曝光的本轮样本事后当作未进行，也不声称无限时间或任意非可预测停止有效。

上述方案的样本代价是实际轮的 `Σ n_t`，若每轮对所有 M_t 个候选逐点计算一次损失，则损失调用数是 `Σ n_t M_t`，另需相应求和、比较和历史维护。它没有证明采样、训练、损失计算或精确实数/对数运算单位成本，也没有宣称 wall-clock 性能；账本的 `roundCost` 是风险额度之和，不能充当计算复杂度。

四类办法的前提分别保留：单个候选在评估前独立于验证样本，仍需要有效的抽样/损失定理；预先固定多个候选允许事后挑选，但必须联合控制整个预声明类；依历史选择候选/n/预算，需要各正质量历史单元上的有效条件检验，独立新样本须满足实际条件 iid/同分布，不能从不同 ID 推出；重复使用同一验证集需要另有对自适应交互有效的可复用机制定理及其查询、隐私或稳定性等具体前提，不能仅凭机制名称或预算声明。本行选择并证明的是前述有限新样本方案，不宣称仓库已建立一般差分隐私或任意可复用验证保证。

### 15.3：同一概率表、自证边界与三种不同责任

`AdaptiveValidation20261027.three_failure_events_not_independent_formula` 使用同一个 `Fin 4` 均匀表，每个原子质量 1/4，三个事件分别为 `{0}`、`{1}`、`{2}`。逐项 `δ_i*=1/4`，并集 `{0,1,2}` 质量 3/4，等于预算和。无需事件独立的并集界在此取等号；若误用独立乘法式 `1−(1−1/4)^3=37/64`，得到严格小于真实 3/4 的值。三个事件互斥而非独立；乘法式需要相应联合独立或能推出该乘积的条件，不能只看边际数值。

候选自己的置信输出是数值，不是 `μ(E)≤δ` 的证明。上述探针反例已给出验证表现与真实风险分离的同一有限对象；给它另附一个自称高置信的数字不会改变该风险。统计目标的类型要求明确的测度、事件和可检验前提，并从条件检验/抽样定理得到概率不等式，不能把待证概率不等式改写成无依据的候选证书输入。

- 内部概率预算：`delta : T → H → ℝ`，以及实际有限账本中的 `DomainBlock.delta : ℚ`、`roundCost : RoundRequest m → ℚ` 等，是配置或额度。需要非负/区间、分配和总和责任，本身没有真实失败频率含义。
- 统计估计保证：例如 `μ.real failure ≤ E_μ[spent]`，或存在可测 `good` 且 `1−Δ ≤ μ.real good` 并在 good 上成立风险/区间结论。这是关于声明的同一概率实验的命题，依赖可测性、目标分布、条件 iid、损失界、预声明类和采样时序等实际前提。
- 确定性不变量：`AdaptiveRoundLedger20261027.arbitrary_finite_round_actions_keep_budget` 对任意有限 `List (RoundAction m)`，从初态 `roundSpent s≤s.limit` 推出 fold 后 limit 不变且累计 charge≤limit。`evaluated_round_spends_its_actual_block_budget` 把已实际 evaluated 的轮绑定到请求块预算之和；`finish_round_preserves_budget`、`exact_round_replay_retains_current_state`、`changed_round_key_does_not_spend_or_load` 处理保持、精确重放与冲突。此处量化所有允许动作的有限序列，不使用概率测度，不推出事件失败率。

`beginAdaptiveRound` 在 `finishAdaptiveRound` 收到验证块前冻结候选生成、可见历史前缀和计划；`evaluated_round_has_fresh_events_and_current_checker` 证明 evaluated 分支遵守当前 checker、有限声明、固定保护域以及事件未复用。generation/evaluation unresolved、缺采样证书、预算不足和键冲突保留其确切状态。已 evaluated 而加载被保护/权限拒绝的轮仍支付实际额度；未取得合格 evaluation 的零 charge 不等于零失败概率。漂移、非独立或选择偏差使统计前提失效时，风险结论应为 UNKNOWN/不可归证并退出或拒绝依赖它的接纳；源码不具备从有限 receipt 自动侦测所有这些失效的能力，也不把时间戳或 catalog 匹配冒称 iid 证明。

### 与实际消费者的已存在连接及另账边界

复用 `u00-original-close-20261031` 中的 `U00ActualStatisticalJoin20261031.sample_packet_reads_actual_column`（保留每行、多重性和索引）、`sampled_request_reads_actual_blocks`（同一实际 blocks 且保持原 sampling/permit）及 `actual_chosen_and_loaded_joint_confidence`。最后一个定理在同一声明的 `QΓ` 上，分别要求校准流和每个验证流的可测、流内 iid/同分布、正样本数、有界损失和有效预算；不要求两个流互相独立。在原 evaluate/activate/runLoaded 真正成功的条件下，结论绑定实际加载表、实际选择和实际样本区间，joint confidence 支付 `protocol.failureBudget + plan.failureBudget`。它没有从业务 receipt 推导这些概率前提；条件历史使用时，必须先固定当前合法 Γ/可见过去并提供相应条件测度的全部前提。

`roundSpent≤limit` 只限制验证账本已记额度，不自动限制 producer 校准与 validation 合计。多次实际实验若要共同保证，需要同一实验/历史模型、覆盖所声称实验的有限集合及另行成立的 joint 预算配置。该另账义务、U00 接线与工程分母保留；本附记不修改 U00、caller、评级、discharges、Step2 或 mathflip，也不把当前任意实际轨迹宣告为满足抽样规律。

### 既有接受与不可变复用定位

本包原独立成功 run `40439612934` / job `121976530560` / subject `149dee0f69c9158f43af3c26e61a5bcfce1632be` 的 12 targets 与 6 guarded checks、PR41 接受和失败草稿历史不变。相邻 `adaptive-round-ledger-20261027` 原 run `40446553400` / job `121999119450` / subject `5da99fc8cee319bdfb55d46cdcda2cd48df3a293` 的 15 targets 与 20 guarded checks、PR43 接受不变。U00 原 run `41178784116:1` / job `124471736816` 的条件连接仍按其原包限定范围使用。

本次只读复核还使用已接受 PR131 Authority（精确 run/job/artifact/subject/tree 身份见 `../original15-1-iteration-boundaries-close-20261106/verification.json` 的 `reused_evidence` 字段），checkout `4c686359bcf9f3caefce33abe391b7cada467f37` 与 S131 同树。实际 `lake-clean-build.log` 为 5612507 bytes，SHA256 `060c462b5d579e904c1253da6d20ab5d6b858ebb48ba2313ac69032b0747150c`：本包 12 组完整类型/公理输出 L14016–14158；RoundLedger 15 组 L16929–17154；ActualStatisticalJoin 三组 L20137–20284。对应逐目标实际公理：本包 12 项均 `[propext, Classical.choice, Quot.sound]`；RoundLedger 的 `learner_change_keeps_service_budget_and_trusted_root` 与 `self_issued_or_new_checker_permission_cannot_change_learner` 为 `[propext, Quot.sound]`，`recorded_load_is_actual_next_service` 为 `[propext]`，其余 12 项为标准三项；ActualStatisticalJoin 的三项依序为 `[propext]`、空集、标准三项。没有对未匹配目标填默认公理。

S131 的六个复用源位于 `proofs/lean/juris_lean/JurisLean/Candidates/`，实际 Git 原字节 pins 为：

| 源文件 | bytes | SHA256 | Git blob |
|---|---:|---|---|
| AdaptiveValidation20261027.lean | 13862 | 3e80ddbfcd40858660bc36660e60664fccb6e817728a6e6cef613ab3570e2d45 | d9a4211c36d139f6a2dd3765cc462120682b4915 |
| AdaptiveValidationAudit20261027.lean | 3208 | 9750d99d766ef40f207dbbad2abeef27aa89086ef96f98a191d4e3b67b29ebb7 | 987d7ff96f229a2feef877bd34e6039095ccdfd2 |
| AdaptiveRoundLedger20261027.lean | 18250 | 8137187be49e0589cffbadb8e5d0acb73bd017a1e06fbf1166a39b0ec7c8b84c | 2c166e51169957e1ec65f16c39ca4bec7ed8ae30 |
| AdaptiveRoundLedgerAudit20261027.lean | 13165 | 149ee3caee93281b93b8851aebee6cbed4de1563af9c6e58d2375b4087e79301 | 813bae8f408bfaba8ddaaac135deac128c531b03 |
| U00ActualStatisticalJoin20261031.lean | 14795 | 6d4f08998bb534b21c91b126cea6023ec5082147031d51c97700eb6108abca8d | 1f76509e04ba52c5d11e6d2de654b8a1313f13d8 |
| U00ActualStatisticalJoinAudit20261031.lean | 899 | e4ca88151d5451907224ac6edb03cec0b7fcfcc89ed6a27591426044ff0f4742 | 4322c2e4c6d95eeef501baa8f46eabfe2d9f562d |
