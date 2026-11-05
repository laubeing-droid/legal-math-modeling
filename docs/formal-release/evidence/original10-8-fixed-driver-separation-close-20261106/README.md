# 原题 10.8 固定推进器与任意推进器的有限分离

**状态：SOURCE_CHANGED_MODULE_AND_RECORD_CHECKS_AND_CI_INDEX_PASS / PR_ACCEPTANCE_PENDING。** 本稿只对应冻结 `10_授权变更与多步法律轨迹.md` L157、L159、L161。最短工作是两个具名数学连接和既有纸面算法的本题实例说明；不恢复未知原V2源码，不替换现有函数，不承担部署或其他专题整合。

## 证据层与实际 source

冻结包基址为 `D:/Codex/1.法律工作区/legal-math-modeling工作区/20261021挺进统一法律数学模型/理论统稿与ZCode施工包_v003补齐来源版_20261021T091138Z_fd4965/`。

- **题给事实**：题10 L93给联合态 `(L,Q)`、consume 的两个分量、fixed correctStep真实连续两次consume、完整数量记录及forms保持；L95给Q-only可替换检查及固定入口的TS/SVB条件。它们可以参与数学推导，不自动成为本轮代码/编译证据。
- **既有纸面证明**：`13_原题逐问补正正文.md:157` 已有保Q篡L的反例及固定/任意量词区分，并要求复用S08.3加有限逐边检查；S08.3位于同文件L119–129。这里归引，不重写其Horn、世界、程序闭包证明。
- **本轮真实读得的源码**：`Seams/InstitutionalEffects.lean:598` 的 `JurisLean.Seams.InstitutionalEffects.performance_not_creation` 是实际局部forms保持定理；`Seams/UnifiedQuantLedger.lean:97` 的 afterPay 操作完整 `List LedgerItem`；`Candidates/Final20261021/Acceptance.lean:109` 的 `a_u09_continuous_10_7_7` 是现有另一固定合成fixture的数值证据。这些路径相对C的 `proofs/lean/juris_lean/JurisLean/`。
- **仍未知的历史实物**：原 `FixedOneCaseTwoPaymentsV2`、原runStates源码路径与local-build产物本轮未定位。冻结包 `依据/v001/落实包.md:61` 本就区分“题给事实可参与纸面分析”和“当前仓已编译实现”。未知路径不阻断自包含数学义务，也不允许宣称恢复了原源码。

本轮源 `FixedDriverSeparationAudit20261105.lean` 只有两个新增定理，6对check/axiom（2 own＋4 reuse）。namespace为 `JurisLean.Candidates.FixedDriverSeparationAudit20261105`：

1. `q_only_two_posts_do_not_certify_forms`：对任意完整 `q1 q2 : List UnifiedQuantLedger.LedgerItem`，否定“所有保留这两个Q的输出都保持forms”的全称结论。明确坏输出 `(([],q1),([],q2))`，Q的金额、身份、类型、基础、受益人、请求状态以及列表顺序全部原样；不是仅保余额。
2. `fixed_given_two_steps_preserve_forms`：按数学定义 `s1=consumeGiven(s0,p1)`、`s2=consumeGiven(s1,p2)`，连续调用既有performance_not_creation，得到两段forms等价链。没有`jointCorrect`、simulation、forms输出成立等结论性前提。

源中 `GivenPayment/consumeGiven/fixedStepGiven` 是**明确声明的题给定义在固定非负整数付款片段上的数学表示**，用实际 InstitutionalEffects.next/performance 和 UnifiedQuantLedger.afterPay；该片段包含给定7、7，完整Q为List LedgerItem。它既不是原V2导入，也不是当前 `Final20261021.Trace.correctStep`；没有声称它与未知原V2类型、runStates或Accepted输出定义相等。审查若只需要forms，不能据本数学表示的next碰巧为恒等进一步宣称原V2整个L恒等。本轮 source CI已验证这两个本地数学连接，并不补造原V2历史编译。

## L157 精确量词与条件结论

取题给正确固定轨迹 `S0=(L0,Q0)`、`S1=(L1,Q1)`、`S2=(L2,Q2)`，以及题给已形成关系r。题给局部performance保持forms，结合固定连续定义得

`forms(L1,r) ↔ forms(L0,r)`，`forms(L2,r) ↔ forms(L1,r)`，从而`forms(L2,r) ↔ forms(L0,r)`。

这不是整体联合正确性假设：证据是两个局部效果定理和明确的中间态代入。完整数量输出使用题给fixed推进定义与Q核的既有结果，不能由forms保持反推数值不变。

构造可替换坏推进器，仅在该固定输入返回 `S1*=([],Q1)`、`S2*=([],Q2)`，其余输入可沿用fixed结果。由Q-only检查的题给读集合，两个完整Q相同使其数量验收结果与正确输出一致；而r在空关系账本上的forms为假，与给定正确轨迹forms为真冲突。因此“任意推进器数量通过⇒全联合状态正确”为假。对正确初始forms非空性，可直接复用 `JurisLean.Seams.InstitutionalEffects.projection_append_form`（同文件L206）：形成记录给出真观察。该反例不调用实际合法executor去抹除L，也不指控固定推进器出错。

原入口条件原样保留：

`TS(c.sourceId) ∧ SVB(c.sourceId,κ,c.record) ∧ runStates(correctStep,K,c)=ok(out)`。

依冻结L95的**题给固定入口事实**，在该条件下引用其固定三状态和对应证据，再用上述forms链；TS和SVB仍是独立外部条件，SVB不增加history、事件表或新参数。此公式没有在新Lean文件中另定义TS/SVB/runStates来冒充原接口；也没有将整个“out联合正确”写入新前提。外部真实来源、付款身份、材料范围和实体法解释未由内部计算证明。

## L159 有限检查的本题补充

算法本体归引补正正文S08.3 L121–129；这里只明确本题新增边检查怎样消费10.6的逐边合同。输入为：给定n步候选轨迹及实际返回/诊断、独立冻结的有限授权与规范表、日志和查询上下文、每类操作的局部合同与允许转换表、明确观察族。表由独立规范/证据输入给出，不从候选执行结果反推“允许”。没有外部语义依据的条目保持条件/缺证。

逐边检查返回以下三种数学结果之一：本有限合同全部通过；具体不相容见证；缺证/未知见证。它不把检查结束或未发现否定当现实合法性。

| 检查 | 有限输入上的实际比较 | 失败/未知见证至少包含 |
|---|---|---|
| 授权绑定 | 主体、对象、动作、内容版本、旧Γ授权规则版本、有效时窗、完整payload及获准nextContext | 边号i、被用授权行/缺失授权、错配字段、请求值与授权值；未知来源仍记独立证据缺项 |
| 日志可见性与选择 | recordedAt/knownAt相对相应cutoff；按固定法律时点、对象/问题筛选；保留冲突/未知 | i、日志行、查询Γ、违反的时间比较或冲突版本对；不改用今天状态解释旧cutoff |
| 环境读取 | next evaluator实际读取的版本及history/Γ与前一步已发布后态一致 | i、预期后态引用、实际读取引用/版本/Γ；结果文字相同不代替读取一致 |
| 局部Pre/Post/Frame | 成功步按已给局部合同；后步实际前提由前步post/frame及持续Γ推出的部分直接核对，其余必须重验 | i、操作、失败谓词/字段、期望与实际值；known noncommit须有some post才能用frame |
| 连续轨迹与表示对应 | 相邻边实际后态等于下一前态；按固定观察核对允许转换及声明有限抽象路径 | i、错配前后态/观察、缺失允许边；unknownCommit=none在此停止，不能伪造h0或成功零步 |

例如给定第二步引用初态而非第一步后态，返回边i=2、字段previous_output_ref、expected=S1、observed=S0。给定篡L但Q正确的输出，Q检查通过而forms字段见证失败；这说明增强的联合检查为何能拒绝Q-only漏过的候选，不宣称旧Q-only已经有此检查。

可靠性证明仅需有限归纳：每个通过项对应所列字段/合同的布尔或表项判定；按边号依次把通过的post/frame和相等的实际后态传入下一项，其他前提必须由显式检查/独立证据提供；遇不相容或缺证立即保留其索引/字段。若所有n项通过，就得到**该给定有限表及外部条件下**的逐边合同合取和连续性；并非自动证明表本身现实合法、业务所有未来执行终止或外部TS/SVB为真。

成本口径明确如下：n为待核业务边数；g≥1为每条边涉及的显式合同原子、授权/转换表、日志和观察记录的总数上界；K=Σk_i为所声明有限抽象路径的总边数；B为一个比较所读取的编码长度上界，`C_cmp(B)`为完整字段/数值比较的真实成本。局部合同限输入给出的有限布尔/表项判定，不含任意未计费判定程序。L只计全部输入与证书的读取长度，独立外部证书的额外核验成本另记`C_cert`。每个业务边的cutoff日志扫描、观察比较和最多g²次两两冲突检查由n·g²覆盖；每个抽象边最多扫描g个允许转换条目，另计K·g，不能用输入读取长度L吸收这些重复比较。因此本题保守增量界为 `O(L + (n·g² + K·g)·C_cmp(B) + C_cert)`，再加原S08.3验证成本。这里g计显式条目而非仅状态个数；若只有状态数界，须先换算实际转换表、日志与观察记录规模。失败输出保留实际业务边/抽象边索引及字段见证。整数/字符串等长比较可按O(B)计；有理数交叉乘法须计实际乘法成本，不能无条件写单位代价。

总界是S08.3本身明确的分支/可见性/Horn/世界/机会检查成本，加上述轨迹成本；本题不再证明其封闭局部定理。只检查给定有限输入，不为证业务未来终止而模拟无限重试，不要求实现、部署、测试或组件迁移。

给定10、7、7直接是非空实例：10→3→0、分配7/3、余付0/4。现有数值引用 `JurisLean.Candidates.Final20261021.Acceptance.a_u09_continuous_10_7_7`（L109）及 `a_u09_three_observations`（L113）保留自己的模型类型；它们佐证同一算术实例，但不被写成与新JointState或未知原V2对象同一。两笔记录是真实不同付款、TS/SVB与法律适用仍是条件。当前源码的具体坏引用见证 `Acceptance.n_non_continuous_consume`（L122）、`n_poststate_name_not_binding`（L126）可引用为当前固定实例，不能冒称原V2错误。

## L161 八项有限交付索引

| 本章成果 | 具名证据归引 | 本轮证据边界 |
|---|---|---|
| 授权反例 | [10.1接受包](../original10-1-authorization-close-20261104/README.md)：`AuthorizationClosureAudit20261104.four_binding_erasure_witnesses`、`unrooted_cycles_create_no_permission` | 完整绑定/独立根信任前提，不自造授权 |
| 桥接定理 | [10.2接受包](../original10-2-finalize-close-20261105/README.md)：`FinalizeReadClosureAudit20261105.actual_finalize_next_eval_reads_selection` | 下一实际读取同一已发布snapshot；不等于司法终局 |
| 历史查询手算 | [10.3接受包](../original10-3-history-close-20261105/README.md)：`HistoricalRevocationClosureAudit20261105.append_replay_enable_replace_revoke`、`fixed_cut_replay_uses_invisible_append_stability` | 固定cutoff/legal time与明确追溯分支 |
| 失败路径frame | [10.4接受包](../original10-4-partial-step-close-20261105/README.md)：`PartialStepGateAudit20261105.noncommit_returned_state_has_full_frame`、`unknown_commit_has_no_returned_post` | known returned state；unknownCommit无确定post |
| 有限轨迹不变量 | [10.5接受包](../original10-5-trace-invariant-close-20261105/README.md)：`FiniteTraceInvariantAudit20261105.finite_prefix_i`、`actual_reported_protocol_post_i` | 完整I限Acceptance.opening及实际有限前缀 |
| 逐边合同及扩展边界 | [10.6接受包](../original10-6-protocol-dependency-close-20261105/README.md)：`ProtocolDependencyAudit20261105.actual_record_roundtrip_does_not_supply_external_reference`、`actual_rejection_blocks_unconditional_strict_rank` 及包内26项复用合同；[PR126](https://github.com/laubeing-droid/legal-math-modeling/pull/126) | 已全链及合后接受，S126 `b849cae8661745a22b0c0917d33f9feb1716c6fa`；source/root/AA身份分开，无全业务终止 |
| 精化与可交换图 | [10.7接受包](../original10-7-representation-refinement-close-20261105/README.md)：`RepresentationRefinementAudit20261105.actual_finite_trace_projects`、`historical_query_parameter`；[PR127](https://github.com/laubeing-droid/legal-math-modeling/pull/127) | 已全链及合后接受，S127 `7df87d6c33538dbc9d51b45038e07ed40474d077`；13 own＋3 reuse，限实际pay/refresh及其观察 |
| 固定/任意推进器分离 | 本包 `FixedDriverSeparationAudit20261105.q_only_two_posts_do_not_certify_forms`、`fixed_given_two_steps_preserve_forms`，题给固定接口条件与S08.3归引 | 本轮source CI通过，records/full PR接受待完；不声称原V2源码恢复或现实联合正确 |

八项证据按原题的独立前提、局部合同、实际连续后态、有限路径与表示观察连接；缩写定理名统一位于 `JurisLean.Candidates` 命名空间，完整FQN和各自source证据见所链包。完成这些有界数学成果不增加新业务机制或全仓框架；既有工程与U00承担整体执行语义的独立义务不因此解除。

## 实际 source、metadata 与验收边界

独立 [changed-module run 42062621684](https://github.com/laubeing-droid/legal-math-modeling/actions/runs/42062621684)，attempt 1，job `127368163315` SUCCESS，模块 `JurisLean.Candidates.FixedDriverSeparationAudit20261105`。source checkpoint `c8e579e3f8bc04331e81fd8659bfe935434e20cf`，tree `67bdd1e9e2aef0a94659897270554ab0c2e79b8e`，唯一 parent 为 S127 `7df87d6c33538dbc9d51b45038e07ed40474d077`。源文件 3799 bytes / 80行，SHA `6f897e3d21d113b94dab2ead353fcb6bf893dbeb03b8d35dd3030308c4ddba96`，blob `f731e5f25a935ba3f1550e97b086a60bd0b2013c`。其余七个job因changed-module模式跳过；不是完整PR/full-release通过。

官方 Artifact `changed-module-only-42062621684-1`, ID `13431214307`，ZIP 2884 bytes，SHA `e75fd984a3ddf83cdd1ccf9430a69ad88e4ae36830ed2e6c84e059992c65d009`。原字节 `module-plan.json` 275 bytes，SHA `8ece6669c27a86a8f3a43e3dc68b8606f54a3f45efb6dc75745b968d3b12796a`；`changed-module.log` 13773 bytes，SHA `6b2c61397c2578c062e5507661be571899270441e1ef48a6bd767751dbcbae1b`。6对实际输出为2 own＋4 reuse、12消息、0 errors / 0 sorryAx；两项无公理，一项仅propext，三项标准三公理。逐目标完整FQN、源码行、raw输出与实际公理集合直接取 `source-target-outputs-r1.json` 登记于 verification.json，未回填默认公理。两个Acceptance数值目标确属本轮四个reuse；原V2历史编译仍未知。

历史上 dispatch-r1 HTTP500、PID1280/exit1，是派发失败，没有可归证的失败源码CI。随后 dispatch-r2 PID32900/exit0 创建上述唯一source run。两份实际收据与原stdout/stderr保留在 `D:/tmp/original10-8-source-r1/`，完整区分见 verification.json 的 dispatch_history；不虚构 failed source run。

source通过后根 checkpoint `d18b3fc23a85841bd292824b2c27c352ee51d3a5` / tree `dfc4eee3f99e23011235ee58e6a6fe76b2642e34` 仅增加本模块import，root blob `11698181c7e6aaf38424884ecc7b26c7e126c964`。AA单次writer删除已由本模块成功输出的两条重复print（performance_not_creation和projection_append_form）；独立metadata checkpoint `96e1bde0abbdc3cb44d419d21d77427497690aeb` / tree `6ebba11abbf1eb58341f6d2674397f84a86112f6` / parent `d18b3fc23a85841bd292824b2c27c352ee51d3a5`，AA blob `8a2fd26f305836567732051fcf4528dd8654c96f`。这只去重审计输出，不改证明/定义/假设。source、根和FullMath原内容不变。manifest实际绑定此clean metadata checkpoint，594 files / 0 diverging；source CI仍只绑定source checkpoint，不能混成同一subject。

本批只将10.8 L157/L159/L161候选登记为COVERED，计数由79/13/5变为80/13/4；其他96数学行、105工程行、6cuts不变。U00只在当前条件链edges8/9增补限定证据，不改caller、参数流或评级。U50维持50 wiring/0 narrow/0 open/124 bindings，global discharges、Step 2、math_flip均false。L159交付有限算法设计、失败/未知见证及含K/g/C_cert的成本界，不声称新增运行程序。题给事实、新数学表示、已有数值实例和外部TS/SVB各守原边界。

本地记录与索引验收：7 项 derived writers 各一次完成（AA单次删除两条重复print并独立metadata checkpoint，其余六项接续），12 项 required checks 均 exit 0，受影响稿件回归为 2 passed in 1.02s；CI index 为 616 runs / 1498 quotes，index tests 为 12 passed in 5.36s，标准 --check exit 0。旧 615 条 metadata 保留，仅新增本轮成功的一条 source run；HTTP500仅派发失败，不构造失败source CI；实际 staging、full/authored diffcheck 结果及官方 raw 尾空格诊断另见 `D:/tmp/original10-8-records-20261106/index-stage-r1-receipt.json`，不把非零 full check 解释为 PASS。完整 PR 接受仍待完成。
