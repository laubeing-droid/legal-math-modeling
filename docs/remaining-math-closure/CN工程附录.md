# CN 连接与全日志编码：第二层工程附录

## 1. 原要求与本次施工位置

本附录引用基线 `bf1e801ff4b39f7d1ec553ec346aa99383bf58bf`。主仓 main、20261108 原件、20261109DeepSeek 审阅原文和原最终回执均不在本子任务的写入范围。

| 原要求 | 原始出处 | 本次数学落点 |
|---|---|---|
| CN 实际后态接反馈核 | `20261109DeepSeek/Codex回执_20261110.md:158,165`；审稿第一层 F13 | `RemainingClosure/CNSemanticConnection.lean` 的 `actual_post_commutes`、`actual_step_law`、`readout_kernel_transport`、`next_action_reads_actual_post` |
| 实体面同一历史读数、六判断与四效果分开 | 审稿第一层 F14；v4 §2.3；当前 `WorldSemantics` | `sixJudgments`、`fourEffects`、`jointLegalReadout`、`legal_entity_feedback_law`、`actual_legal_step_worlds` |
| 实际原生拟合/RSI 留存并进入私有参数 | 原回执 §4 第8项；v4 §8.1—8.4；当前 `Execution.learnReport` | `Engines.fit_to_private_feedback`、`rsi_loaded_report_table`、`learnReport_entity_frame` |
| 完整事件/日志编码 | 原回执 §4 第6项；审稿 F7；v4 §1.2 | `RemainingClosure/FullEventLog.lean` 的双向完整载荷编码、逐边 reports 图运输及实际 CN/业务消费者 |
| 正向推导与法律语义合成 | 原题03.3—03.6（原题单第125—159行） | `CompilerBridge.finite_closure_same_cn_world`、`provenance_same_cn_world`、`Actual.admitted_closure_feedback` |
| 实际 CN episode 与原有理/实数反馈实例的交换 | 原回执 §4 第8项“本次数值／原业务反馈核”；本轮目标 | `Numeric.native_fit_output`、`Menu.public_performance`、`Menu.source_update_commutes`、`source_kernel_projection`、`complete_source_path_projection`、`complete_source_prefix_projection`；新定理等待同提交权威 CI，不能据共同 Dynamics 名称报闭合 |

审阅稿 F13 中“十二制度仍只有纸面、八引擎没有实际调用”的旧事实判断已被当前 main 的 `CN/Completion20261105` 实际源码与既有 CI 反驳。原回执据此 revise/reject 的裁决应保留。但这不自动证明 CN 与原数值核的逐实例交换；本次也没有把二者混为一个问题。

## 2. 真实数据及证明消费

完整命令以 `Σ α, Command α` 保存类型和输入。`FullEventLog.CN.replay_commands` 从当前 CN 的有端点 `History` 证明原命令串重放得到原端点；`complete_history_roundtrip` 经 fresh 操作token编码后仍恢复同一串及端点；另 `runHistory_commands`/`commands_runHistory`/`commands_injective` 重建原端点依赖 History 本身，`token_history_roundtrip` 给出带完整命令载荷的真正双向式。这些命令单射定理的范围是固定initial。跨所有初态另有 `GlobalHistory`/`GlobalCode=(initial,Tokens.encode commands)`；`decodeGlobal_encodeGlobal`、canonical范围的 `encodeGlobal_decodeGlobal` 和 `encodeGlobal_injective` 保留全部起终态及零步历史，`zero_step_roots_distinct` 明证不同根不被同一空串抹掉。`CNSemanticConnection.finite_sequence_catalog` 使任意有限原命令串都有无损目录。不是对全部命令载荷添加可数或标准 Borel 假设。

共同反馈模型采用可数的完整目录历史及有理表，策略允许一般可测 Markov 核。`actual_post_commutes` 将原解释器后态及实际表同时接入既有 `ClosedLoop.update`；`actual_step_law` 是同一策略律的推前；`next_action_reads_actual_post` 明确读新历史和实际新表。`legal_entity_feedback_law` 进一步把六判断、四效果与私人参数一起推前，避免分别拼接边际。

`representedReply` 是该同一 `Dynamics.update` 的单命令投影。十二个制度消费者不仅复述“能构建一个 Dirac”：它们分别复用已有制度成功、失败、范围和保留性证明，给出实际法律结果；一般随机策略的核运输另由上段定理证明。

八个 `Engines.*_feedback` 都经 `retained_call` 读取当前 public `.engine` 命令产生的同一原生报告，随后应用相应旧数学定理。`fit_to_private_feedback` 又用该实际报告的表进入真实 `.learnReport`，并证明 N/F/L 的 frame。表相等不是其前提；原生拟合输出的条件、原有材料准入/版本/请求守卫才是前提。

## 3. 十二制度逐项

| 制度 | 新消费者 | 实际复用的旧证明 | 保留的结果/出口 |
|---|---|---|---|
| 生命周期 | `Institutions.formation_feedback`、`lifecycle_feedback` | `Examples.actual_nonjudicial_formation`、`lifecycle_actual`、`lifecycle_failure_preserves_effect` | 形成不造裁判；撤销真效果；逾期失败 |
| 代理 | `agency_feedback` | `Examples.agency_actual`、`agency_over_scope_rejected` | 授权登记与本人能力；越范围不改登记 |
| 管辖 | `jurisdiction_feedback` | `Examples.jurisdiction_actual` | 普通分支与无普通管辖不同 |
| 证据 | `evidence_feedback` | `Examples.evidence_actual` | pending/admitted/excluded 以及 raw 保留 |
| 善意取得 | `acquisition_feedback` | `Examples.acquisition_actual` | 善意、恶意、遗失物路线各异 |
| 共同犯罪 | `offense_feedback` | `Examples.offense_actual` | 同一人/事件/罪名查询，不能复制未见事件 |
| 破产 | `bankruptcy_feedback` | `Examples.bankruptcy_actual` | 实际受理、债务人、中止与后续利息查询 |
| 国家赔偿 | `compensation_feedback` | `Examples.compensation_actual`、`compensation_missing_prerequisite_not_automatic` | 具名轨道及缺前提未知 |
| 权利冲突 | `rights_feedback` | `Examples.rights_actual` | 保留争议与原关系 |
| 表达式解释 | `interpretation_feedback` | `Examples.interpretation_actual` | 下一实际查询消费存储解释，N不混改 |
| 既判力 | `resJudicata_feedback` | `Examples.resJudicata_actual` | 实际索引的人/事/时点界限 |
| DeepInfer消费 | `proposal_feedback` | `Examples.proposal_actual` | 候选不等于裁断/拘束 |

上表 `Institutions.*_feedback` 只证明单命令一般CN历史运输，本身未连接原数值/原业务学习核。独立复核已指出该差别；本次新增 `InstitutionalContinuation`，逐制度实际后态调用下列真正后续学习连接，不能再拿上表单步见证单独填F13 pass。

| 实际制度后态 | 新同源消费者 |
|---|---|
| 形成和撤销（含空L） | `lifecycle_continuation` |
| 委托后的新增grant | `agency_continuation` |
| 真实普通/专属管辖结果 | `jurisdiction_continuation`、`failure_exits_continue` |
| 原pending/admitted/withdrawn材料状态 | `evidence_continuation` |
| 善意、恶意、遗失物真实出口 | `acquisition_continuation`、`failure_exits_continue` |
| 具名人与事件及缺事件出口 | `offense_continuation` |
| 真实受理/中止与他债务人区分 | `bankruptcy_continuation` |
| 真实刑事赔偿轨道及缺前提出口 | `compensation_continuation` |
| 真实权利冲突后态 | `rights_continuation` |
| 实际存入的表达式解释 | `interpretation_continuation` |
| 实际存入的既判拘束 | `resJudicata_continuation` |
| 原候选输出、无裁断/拘束 | `proposal_continuation` |

`FitReady` 仅列source实际读取的版本1、admitEvidence授权和learnModel授权，所有具名实例由真实post的守卫实算证明。`Numeric.ModelReady` 对cashStart整个N的强要求只保留给原付款Menu；`fitReady_of_modelReady`让它复用增强后的准备引理，没有拿它限制全部制度。`learned_ready`保留一般FitReady域，`learned_modelReady : ModelReady s → ModelReady (learned s y)`另行保留原完整N相等的强后态命题；二者均已在同一模块实编。`actual_institution_frame`保留全部制度外层字段、N/L/账本/裁断/拘束等；`old_evidence_preserved`逐cell保持已有key，E/F新条目保留。

`actual_retained_report`读取同一新后态实际报告。`actual_kernel_projection`由同一次Y的旧native_fit_output和实际learned_read推导原数值核，未把待证交换放进前提；`following_policy_reads_actual_post`把后续给定法律策略复合到此实际新后态，其自身许可支持及信息因子化条件仍保留。`complete_replay`、`common_model_realization`将“先制度原命令，再实际完整学习命令”放回同一个CN.model原历史。这些CN目标在下文绑定的提交上已经整模块构建和公理审计；本轮总状态及完整CI另列第8节。此表不声称每个制度都获准执行performance菜单。

上述是原已有制度参数实例的逐项连接及一般目录运输，不声称凭它们穷尽所有制度的全部具体规则输入。任意一般实例继续采用同一个命令解释器、既有制度表达式和规范参数。

## 4. 八引擎的具体消费而非名字对齐

| 引擎 | 本次留存消费者 | 被实际调用的旧数学证明 | 关键条件 |
|---|---|---|---|
| fit | `Engines.fit_feedback`、`fit_to_private_feedback` | `fit_uses_actual_sample` → `u01_6_fit_card_minimizes_actual_sample` | 同一协议、候选表、实际样本；原有准入/请求/版本；不伪造 IID |
| prob | `probability_feedback` | `probability_uses_actual_posterior` → `posterior_mass` | 实际非零归一化后的原生输出；仅模型内后验；外部 Q 仍要 A-IDENT |
| causal | `causal_feedback` | `causal_actual_identified_value` → `selected_weight_recovery` | 支持/记录概率及既定识别模型；法律 permit 另行保持 |
| bargain | `bargain_feedback` | `bargain_actual_allowed_maximum` → `legal_best_sound` | 原实际菜单、permitted 和同一 score |
| cash | `cash_feedback` | `cash_actual_post_conserves` → `u09_1_quantity_conservation`、`performance_cash_consistent` | 同一原生付款、币种/单位、原守恒与现金一致性 |
| exact | `exact_feedback` | `exact_native_meaning` → `u06_3_eval_exists` | 同一实际原生表达式/结果，不重标单位 |
| behave | `behavior_feedback`、`behavior_actual_selected` | `behavior_model_does_not_filter_illegal_action` + `best_dominates` | 给定阈值范围；实际行为最优不替代获准行动集合 |
| rsi | `rsi_feedback`、`rsi_loaded_report_table` | `rsi_actual_post_budget` → `finish_round_preserves_budget` | 原预算、协议、实际 Loaded 及真实加载状态 |

## 5. 十五题：原能力如何被实际消费

下表旧定位的 `文件.lean::声明` 表示源码文件与准确声明名（不是另造Lean命名空间），行号以所列main基线为准。以下题名逐字沿用审稿第一层 B.3（第349—363行），题单正文起点分别为Q01:97、Q02:97、Q03:109、Q04:87、Q05:85、Q06:87、Q07:269、Q08:99、Q09:143、Q10:99、Q11:91、Q12:93、Q13:93、Q14:87、Q15:87。逐项给消费关系，不能把出现文件名等同于本次新证。旧部分已有独立证明时保留，不重新证明。条件未消失。本表CN源连接的单模块结果为第8节所列 `pass`；F14新增一般公式、跨模块批次及整库权威CI仍分别以其各自原始结果验收。

| 原题 | 实际消费关系 | 本次所补及保留条件 |
|---|---|---|
| 01 连接拟合与泛化误差 | 实际样本 → 原 ERM → CN retained report → Learn → A.θ → next policy | `fit_to_private_feedback`及 `Menu.calibrated_actual_table` 接实际后态；`LearningFiniteClass20261027.lean::u01_1_iid_empirical_risk_uniform`（:149）、`u01_1_iid_approximate_erm`（:177）及旧实际加载置信消费者保留有限类/IID/有界损失前提，不将单样本零风险说成总体无误差 |
| 02 Harness约束与失败封闭 | 实际请求/规范/材料 → CN公开命令守卫 → success/unknown/rejected/conflict/blocked → 同一实际后态 | 十二制度的不同出口进入同一模型；旧 `BusinessFeedbackLoop20261027.lean::unresolved_business_has_no_new_action`（:367）及 `LoadedLegalConsumer20261027.lean::unknown_loaded_probability_has_no_transaction_effect`（:273）仍消费真实失败出口；许可菜单为空不伪造成功 |
| 03 神经符号编译与来源解释 | 当前准入材料/template → `formula_refines` → 旧有限closure / checked DAG → 同一受支持法律世界 → 当前CN查询与反馈 | 新 `CompilerBridge`实际消费有限闭包与来源DAG；负文字独立，既有解释覆盖/保守抽象与MustFacts反例保留 |
| 04 概率统计与共同空间识别 | 原同世界后验 → `PosteriorLawRealization.lean::actual_Q_from_xi`；CN实际 `prob` 结果留存 | 不把归一化当外部 A-IDENT；新 `Menu.source_response_from_same_xi`/`score_from_same_xi` 把实际响应和现金评分绑定 `PosteriorLawRealization.lean::actual_Q_from_xi`（:82）、`PosteriorLawRealization.lean::xi_outcome_marginal`（:74）的同一旧 Ξ；外部 A-IDENT仍是独立原条件 |
| 05 校准域外检测与风险保证 | 旧 `BusinessFeedbackLoop20261027.lean::act` 实际调用 `runLoaded` → `loadedProbability` → `produceInterval` → `chooseLoaded` → `executeDecision`；`known_probability_binds_actual_loaded_and_sample`、`loaded_run_choice_uses_current_model` 消费同一实际表与样本；`frozen_family_probability_confidence` 消费有限样本同分布独立置信证明 | 新 `Menu.calibrated_actual_table` 又把原 `u01_6_successful_pipeline_uses_actual_empirical_minimizer` 应用到这个真实 CN native-fit/retained/learned 表；证书协议、同表、覆盖、支持、风险原条件保留；未宣称一标签样本无条件总体校准 |
| 06 概率决策信息价值与策略 | 原 `legalBest` 实际最大值 → `bargain_feedback`；原有限期Kuhn及记录/收益链保持 | 本次不把单步议价当完整多期博弈；n≤T、fair、独立乘积、单玩家桥四限定保留 |
| 07 法律对象共同模型与表示 | CN完整 core F/E/N/L/A/accounts → 同一有序replay → 六判断/四效果/私人参数联合法律读数 | 原任意EntityQuery读数运输与同一法律查询一致性分别验；根新 `EntitySemantics.CoherentQuery` 要求实际选中rule/template、同范围、相容世界及nature匹配，并给出真实canonical消费者，不能靠多字段同名；`legal_entity_feedback_law`保留完整命令载荷和端点 |
| 08 规范时间证据与程序终局 | 当前norm/template/admitted proof → `actual_legal_step_worlds`/现有 `WorldSemantics.lean::actual_legal_step_semantic_ready` → 实际制度决定 → 存储拘束/范围/时间查询 | `actual_legal_step_worlds`及十二具体消费；无索引仍unknown，不能自动false |
| 09 关系效果数量账本与履行 | 同一实际付款 → 原Native Cash守恒 → CN实际account/ledger与制度效果 → 共同readout | 现金消费者与原FinancialMerge保持；新 `Menu.actual_cash_payoff`/`episode_read` 对同一个实际后态接现金和数值投影，`full_replay`/完整prefix运输顺接以前全部履行 |
| 10 授权变更与多步法律轨迹 | `AuthorizationClosureAudit20261104.lean::checked_permissions_exact_positive_semantics`（:366）/`rooted_refresh_is_actual_authorized_step`（:397）→ 同一旧提交命令的真Trace.Step → full history replay | `FullEventLog.Business.complete_business_log_conservation`消费旧全串提交/刷新；CN的 `complete_history_roundtrip`/`encodeGlobal_injective` 与一般核运输保留同一完整操作载荷；信任根/范围/时限/旧授权不由学习生成，未知图不产生许可 |
| 11 行为法学测量与因果识别 | 真实记录/支持条件 → `U12_1CausalPolicyBridge20261030.lean::actual_measured_policy_causal_value`（:535）/原selectionRecovery → `causal_feedback`留存同一值 | 原测量有效性、一致性、支持、logging匹配、条件交换性/可积条件与法律准用分开；没有permit不会因此生成法律判断 |
| 12 行为响应反馈与政策学习 | `BusinessFeedbackLoop20261027.lean::adviseRecorded`（:148）实际调用 `MeasuredPolicy20261027.lean::adviseMeasured`；`known_advice_reads_recorded_data_within_cutoffs`（:162）绑定真实记录；`U12_3MeasuredPolicyBridge20261030.lean::actual_find_policy_oracle_probability`（:241）/`actual_policy_clipping_bias`（:420）保留原IPS/截断能力；新 `Menu.next_choice_reads_loaded_table`/真实现金最优接回同源Y | 实际行为优选保留违法可能；原非空有限策略族、可测/有界、IID或原指定序贯设计、支持/权重界/截断偏差及原permission分别保留；一般联合学习/均衡不由一玩家实例推出 |
| 13 RSI机制规则与个性权重 | 当前表/实际报告 → `learnReport` → 该主体A.θ；N/F/L/E/决定/拘束/账本frame | `learnReport_entity_frame`；`U00MeasuredRSIEntry20261031.lean::actual_continuation_binds_accepted_row_and_native_entry`（:271）消费真实被接纳记录和个人native入口，`U00RSICandidateBridge20261031.lean::personal_producer_preserves_actual_frame`（:194）保留原frame；机制变更与规则变更继续走各自原权限 |
| 14 反馈学习与候选更新 | 原实际ERM/RSI结果 → retained report → 原实际加载状态 → Learn消费 | `U00RoundPostBridge20261031.lean::actual_round_choice_transports_to_activation_projection`（:126）及 `AdaptiveRoundLedger20261027.lean::recorded_load_is_actual_next_service`（:315）连接真实激活与下一选择；未Loaded/未Evaluated不能读取加载表，候选不造裁断 |
| 15 多轮改进验证与能力边界 | 原 `finishAdaptiveRound` 实际后态预算 → `rsi_feedback`；完整业务动作重放 → 原全串守恒/预算 | `complete_business_log_conservation`消费 `BusinessFeedbackLoop20261027.lean::arbitrary_finite_commands_consume_actual_posts`（:475）和 `AdaptiveRoundLedger20261027.lean::arbitrary_finite_round_actions_keep_budget`（:356）；原horizon/预算/旧能力条件仍保留，不外推无限改进或无条件收敛 |

原NN/ReLU、Shapley、Integrated Gradients、偏离度和条件保守扩展等已保留的数学能力没有因本次CN参数实例只使用原生表拟合而被删除、改写或缩减；它们各自的已有证明仍由主线原消费者承接。本表也不把十五专题的97主问、266原段与105工程要求重新冒称十五条无条件定理（v4:632）。

## 6. 全日志量词修正与审计

旧审稿“只有新occurrence才增加|h|”若h指完整操作历史，已由 `CN.record_only_counterexample` 反驳。新材料记录是一个实际操作，操作历史长度加一而物理 F不变。修正为：新操作增加操作序列长度；新物理发生才增加物理发生清单。源 v4 §1.2 本就区分事件、测量、记录及reports关系，因此这是还原原要求，不是缩减日志。

`Tokens.decode_encode` 对任意完整源载荷列表成立；`encode_decode` 的另一方向明确限定在fresh规范编码的像上，不能要求任意历史已有token都碰巧等于新分配token。旧身份字段仍完整位于payload，未被新操作token替换。

`Tokens.encodedReports` 是逐record/event对的关系，`reports_roundtrip` 证明编码全图解码后的集合相等。它不把整个关系压成“所有cross配对均相关”的单一布尔值；早期新草稿的该错误已在独立复核后删除修正。

`Business.u00_event_identity` 保留实际 EventId、测量、记录和目标/机制版本；`copied_payment_record_counts_once` 实际消费旧 `record_count_once`。`measurements_not_collapsed` 保留同事件下第二份有效测量。`complete_business_log_conservation` 对解码后的完整原业务命令串消费旧实际守恒与预算证明。

## 7. 同源实际 CN episode 的新连接与验收

`Numeric.Menu` 不是另造原生计算核心。`native_fit_output` 先实际证明两个候选的旧ERM结果；`public_performance` 推导现有公开履行入口的 permission、同币种/单位、已准入来源、真实F、fresh现金身份和Native守恒条件。`actual_cash_payoff` 保留原 allocation/surplus 分型，并将真实 paid 增量用作效用。

菜单的两支是实际付款1，以及同Y付款2/0。`actual_native_choice`/`chosen_maximizes_actual_cash` 消费旧 `legal_best_sound`，`score_from_same_xi` 与 `expected_actual_cash` 证明分数就是所选原命令的同世界真实现金期望。这里的 `realizedPayoff` 从实际后态账户读取paid差，`realizedPayoff_eq_amount` 消费原实际履行，`native_choice_maximizes_actual_expected_cash` 直接比较该真实后态读数的期望。`actual_reachable_learning_changes_choice` 更给出从(0,0)先选0、真episode(Y=true)到(1,5/8)并保持LegalReady、下一真实命令选1的可达见证；每轮没有重置样例。

`Menu.sourceModel` 的历史保存全部 `(a,Y)`；`fullCommands` 从前一完整后态顺接生成全载荷原命令。`full_replay` 对整个命令串给出真实 CN 后态；`source_update_commutes` 消费实际表学习和实际原履行，`source_kernel_projection` 推导完整核推前。`source_private_is_actual` 表明辅助实数参数每一步确从原实际加载表写入。

`complete_source_path_projection` 和 `complete_source_prefix_projection` 调用另一单写模块 `ProcessTransport` 的一般路径/完整联合前缀运输。这里的交换前提已由 `source_kernel_projection` 证明，未作为CN待证内容塞入假设。实际自适应动作日志没有被说成公平动作日志；原有限期博弈四限定仍保持。

量词为任意有理初态、任意有限完整日志、相应真实源模型的整条路径律。原 W1 的稳定性针对该投影在旧不变平方及分布条件下的数值核，不推广为任意CN制度全体都收缩；原μ*仍属于原实数状态空间。

## 8. 验证记录

本节是单模块回执。F13、全日志及该CN文件全部新证明为 `pass`；同轮总批次仍为 `partial`，失败在根模块 `EntitySemantics` 的5处语法/不可判等问题；仓库规定的完整权威CI为 `not_run`。根代理继续修复并执行后续整体验收。

| 对象 | 同提交验证结果 | 状态 |
|---|---|---|
| FullEventLog完整token/reports、全局root与dependent History双向、业务消费 | 源SHA256 `d84cb111b0ffef15779ee1b7aed0901c3c5d1f57b21221335991d3cbf026128f`；同轮原日志:2368显示整模块构建，global三条双向/单射目标:2395—2403给标准公理 | pass |
| CNSemanticConnection全部新定理，含FitReady、强learned_modelReady、12个真实continuation及失败出口 | 源SHA256 `c46b239b02cf4c5971add07af2918cc2ede83a50b882879fca47f2929accb00f`；原日志:2555显示整模块构建；本文件142个#print目标142/142命中，仅`propext`、`Classical.choice`、`Quot.sound`或更少，无其他公理 | pass |
| F13实际原核/后续policy/完整命令重放 | `actual_kernel_projection`、`following_policy_reads_actual_post`、`complete_replay`、`common_model_realization`、全部12个具名continuation、`failure_exits_continue`均在上述整模块中构建；强`learned_modelReady`原日志:2802—2804、F13核/策略:2988—2993、12实例:3003起及失败出口:3039—3041均有标准公理回执 | pass |
| 同轮跨模块批次 | `EntitySemantics`原日志:3051起仍5错误；不能把CN单模块结果写成整批通过 | partial |
| 整库权威CI及最终同版本总回执 | 由根代理在其余错误修复后执行；本轮模块计划scope为`CURRENT_AND_REVERSE_DEPENDENTS_NOT_PROOF_ACCEPTANCE` | not_run |

绑定提交：`f863522a76a0e1dea1640af33418faa1b757b7e6`。GitHub Actions：[run 42562004392](https://github.com/laubeing-droid/legal-math-modeling/actions/runs/42562004392)。本机原始artifact日志：`D:\Codex\1.法律工作区\legal-math-modeling工作区\20261110\剩余目标验证\module-f863522a\changed-module.log`；同目录`module-plan.json`保存此次计划范围。该run整体为失败，以上`pass`严格指表中已实际构建并有公理日志的模块和目标。

最后整体验收必须绑定最终提交、run及artifact。这里没有把目标JSON、源码头注或旧main绿色CI当成本次新命题的验证结果。
