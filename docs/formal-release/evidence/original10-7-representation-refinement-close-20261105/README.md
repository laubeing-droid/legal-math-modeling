# 原题 10.7：实际付款／刷新解释器的跨表示精化

状态：SOURCE_CHANGED_MODULE_AND_RECORD_CHECKS_AND_CI_INDEX_PASS / PR_ACCEPTANCE_PENDING。本包只对应冻结 `10_授权变更与多步法律轨迹.md` L149/L151/L153；源文件为 `RepresentationRefinementAudit20261105.lean`。R2 source CI 已通过后才接根，本批数学行候选登记为 COVERED；完整 records PR、exact-subject 全链及合后接受尚待完成。

本项阻断原题的剩余义务是：给现有实际付款／刷新解释器一个独立定义的抽象迁移及其观察投影，证明实际合法步和有限已报告轨迹落在该抽象合同内，并给出原题要求的三种丢失信息反例。复用 `Ledger.consume_committed_origin`、实际 CaseRecord codec、已验收的等总额不同归属反例；不重写它们。

## L149：状态、观察和合法一步

实现状态 C 为实际 `Ledger.Handle`。抽象状态 S 为 `BusinessView`：保留 gamma、revision、完整 debt、formations、allocated/paid/surplus、完整 cash、used、完整 receipts、normHistory 和 env。它省略此付款／刷新片段没有读取的 procedure、judgment 等字段；不声称这两个表示在其他事件或所有法律语义上等价。冻结共享定义 L89 允许不加入实际没有用到的分量。

表示映射为 `project`，`Ref(c,s)` 精确指 `project c = s`。观察族为上述业务字段的坐标观察，尤其包括完整收据和现金事件中携带的付款身份、归属、规范版本，不只是总余额。`actual_observation_projection` 展开当前必须对照的 cash、used、receipts、gamma、history、env；其余保留字段由 `project` 的对应坐标定义读取。

抽象 `payEffect` 直接定义抵充量、余付、现金、已消费身份及追加收据，`refreshEffect` 直接定义新 gamma、追加日志和实际环境选择；它们不是“存在一个实现步”的别名。`payError` 直接在抽象字段上执行身份解释、适用、作用域、单位、版本、环境、形成关系、授权、非负、身份及现金重复检查。`LegalStep.pay` 要求收据身份 fresh 及这些检查成功；`LegalStep.refresh` 要求同案与按旧 gamma 实际核验的授权成立。外部法律解释、来源对应和授权根的真实性仍是独立输入。

对实际已提交付款，`Ledger.consume_committed_origin` 给出 fresh、实际 validationError=none 和实际 commitPayment 后态；`project_commit` 将实际字段更新投影为 `payEffect`，`actual_payment_legal` 因而构造 `LegalStep.pay`。对实际成功刷新，`actual_refresh_projects` 展开真实 refresh 分支得到投影等式，`actual_refresh_legal` 从该分支取得同案和旧上下文授权，构造 `LegalStep.refresh`。任意 `Ref(c,s)` 的版本只需用 `s=project c` 代换，未添加模拟结论作为前提。

每次成功付款都增加一条完整收据；`pay_effect_receipt_length` 和 `pay_effect_not_stutter` 证明即使付款额为零也不能以零步隐藏其效果。实际 replay 继续使用原 Handle；明确的已知拒绝／冲突／pending 或刷新未决停止在原 Handle，因此在本观察族上可以用零步。诊断输出仍按真实执行器返回，未把失败改写成成功。`unknownCommit` 没有确定报告后态，`unknown_commit_has_no_reported_post` 单独保留这个边界，不给它填上旧态。

非空成功例沿用现有 `Acceptance.opening`、`request 1`、`request 2` 与绑定完整 payload 的 `Acceptance.grants`。已验收的 `Acceptance.u00_pipeline_success` 给出实际 Pipeline 的付款成功，`Acceptance.a_u09_continuous_10_7_7` 给出后态余额 3/0、累计 allocated=10、paid=14、surplus=4；各实际提交步再应用本项的 `actual_payment_projects` 和 `actual_payment_legal`。这些既有固定实例仅说明本合同有非空应用，不代替上面的通用条件证明，也不证明现实来源或授权证据真实。

## L151：有限提升和更新交换式

`actual_finite_trace_projects` 对实际 `runTrajectory grants initial steps` 的指令列表归纳。空表给 `LegalPath.nil`；真实 committed payment 和成功 refresh 各用上面已证合法一步接归纳路径；replay 递归而不插入业务变化；已知停止分支给原态零步；unknownCommit 与“有报告后态”的前提矛盾。授权目录 grants 在整段归纳中不变，每一步读取其当时实际 gamma，不从裸 `Trace.Path` 反造授权。

这是逐步构造的路径：每个非停顿抽象节点都是对应实际 Handle 的 project，因此在每个中间节点、而不只终点，所有声明的业务观察一致。若一次实现步对应多步抽象迁移，一般拼接长度应为各段长度之和；本片段实际构造每个成功业务指令一条抽象边、已知无变化分支零条边。这里只覆盖固定付款／刷新指令及真实解释器的报告分支，不推出任意新增事件的精化。

前向模拟给出实现行为落在允许规格内的存在性；它不要求当前一条指令列表、给定授权目录或实际策略遍历抽象规格允许的所有请求与行为，所以不推出逆向模拟或行为完备性。原题没有额外要求必须用双模拟证明的性质。

准确的交换式为：实际付款提交后 `project after = payEffect (project before) req`；实际刷新返回 `.known after` 时 `project after = refreshEffect (project before) change.gamma change.event`。历史查询的参数另外记 q，不能偷换成刷新后的 next：

```text
queryAt q (refreshEffect s next e)
  = Temporal.proposed_applicability q (s.history ++ [e]).
```

`historical_query_parameter` 证明此等式。知识截点、法律时点等仍包含在各自 Gamma 中；撤销是否影响历史读数由实际选择规则与 q 决定。没有宣称撤销普遍与旧查询无条件交换，或新旧参数下结果必相同。

## L153：三个反例

1. 只看总额：复用 `ParametricAllocationAudit20261104.l163_equal_total_does_not_fix_identity` 的实际 afterPay 结果；总额相同，身份归属不同。因此观察族保留完整 cash 和 receipts。
2. 只看 codec：`codec_does_not_constrain_independent_history` 对实际 `CaseRecord` 复用 `caseFragment_roundTrip`，但 `(record, [])` 与 `(record, [1])` 的独立历史不同。它否定仅凭 codec 的接收规则，不声称实际执行器采用该规则，也不从 codec 推出来源真实。
3. 只看终态：`same_terminal_misses_intermediate_authority` 比较 `[Acceptance.opening]` 与候选 `[opening, Acceptance.post1, opening]`。首尾相同，post1 却是实际 commitPayment 字段效果、收据长度增加，且空授权目录对该请求返回 false。第二条是绕开授权执行器的非法候选写入后任意恢复旧态，既不是实际合法执行路径，也不是存在合法回滚 API 的主张。它具体说明终点相等不足以检查中间付款授权。

## 实际 source 与根接入证据

R2 source `d9a06696449238581ddecaa5227256a4f6ebebd9`，tree `16cd55d4f41b038430eba21434fd5bc11aa92c71`，唯一 parent 为 R1 `3dfe8389c43ab5f342fa524fb9300b0df8747d71`。独立 [changed-module run 42052361175](https://github.com/laubeing-droid/legal-math-modeling/actions/runs/42052361175)，attempt 1，job `127331532518`，模块 `JurisLean.Candidates.RepresentationRefinementAudit20261105` SUCCESS；其余七个 job 为 mode 条件跳过，不是完整 PR 或 full-release PASS。

官方 Artifact `changed-module-only-42052361175-1`, ID `13426778384`，ZIP 9049 bytes，SHA `8bd6b4f76c008112ec33048ec31ac03d42a575b7f2e9ac468fca859019ad25fc`。成功 raw `module-plan.json` 为 281 bytes，SHA `b66de2dee56a7057a8fe96137b49365a7c3e65098df7c0e224bcd5678ed480fd`；`changed-module.log` 为 73787 bytes，SHA `ea56abc6ca8ba28d4cca80a4c67436d88fd20e166d4dc9033291ac8528d5f65e`。16 对目标为 13 own＋3 reuse、32 条实际消息，0 errors / 0 sorryAx；公理分布为 11 组三项标准公理、3 组 propext/Quot.sound、1 组仅 propext、1 组无公理。逐目标 FQN、源码行及实际完整公理输出从 source-target-outputs-r2.json 原样登记于 verification.json，未默认回填。上文两个 Acceptance 固定实例是既有证据，不属于本 run 的 16 对目标，也不冒称本轮 runTrajectory 新执行结果。

R1 [失败 run 42051222352](https://github.com/laubeing-droid/legal-math-modeling/actions/runs/42051222352)，attempt 1，job `127327533778`，source `3dfe8389c43ab5f342fa524fb9300b0df8747d71`。官方 Artifact `changed-module-only-42051222352-1`, ID `13426762120`，ZIP 10435 bytes，SHA `3d2c04897979c1dbe784dcb5ae8152c6580dddd5d497df42b9c928dd85cb3179`；失败 raw 原字节保留于 `D:/tmp/original10-7-source-r1/raw/`，5 条 source diagnostics 及 pins 见 verification.json。源文件无 sorry 文本，失败 elaboration 的自动 sorryAx 不计成功证据。R2 仅添加 receipt-length 的精确 change 和调整 refreshEffect 字段布局；13 个声明、前提与16对目标不变，没有删除结论或加新假设。

根接入 checkpoint `ab259fa967ac07db1afba4f12e9f3b2c428f4dc4`，tree `554a2f3c21bb6cd3dac02658c86142cb8eed7b89`，parent 为成功 R2，仅给 JurisLean.lean 新增本模块 import。source blob `9f1a62e7db5a7cc6640bbc789fbe1cf0c69c1b5b` 原字节不变；source 为 18986 bytes、344 行，SHA `ca411d6061ea5d95903c4cf3106b1597521f5a7c71702e3a94bc5292deb79c24`。AA 单次 writer exit 0 且 Git 内容不变，无额外 AA checkpoint；manifest 绑定此 clean root checkpoint，593 files / 0 diverging。根与 manifest subject 不冒称独立 source CI head。

本批同时按既有证据将 08.8 L145/L147 登记为候选 COVERED，追加说明见 finite-legal-validation-20261027/README.md；旧两条 source run、四个源文件及 PR54/main 证据保留，没有新增 08.8 proof 或重跑旧 module CI。原题候选计数从 77/14/6 改为 79/13/5，仅这两行；其余95数学行、105工程行、6 cuts不变。七项工程接线及U00仍按独立分母履行整体冻结理论的执行语义和验收义务，不因数学登记解除。U00仅既有条件链 edges8/9 增补10.7精化证据，不改caller/ratings；08.8无需重复尾注。U50为50 wiring/0 narrow/0 open/124 bindings，global discharges、Step 2、math_flip=false保持。

本地记录与索引验收：7 项 derived writers 各一次完成（AA先单次检查无Git内容变化，其余六项接续），12 项 required checks 均 exit 0，受影响稿件回归为 2 passed in 1.10s；CI index 为 615 runs / 1495 quotes，index tests 为 12 passed in 6.01s，标准 --check exit 0。旧 613 条 metadata 保留，仅新增本轮失败R1和成功R2两条 source run；实际 staging、full/authored diffcheck 结果及官方 raw 尾空格诊断另见 `D:/tmp/original10-7-records-20261105/index-stage-r1-receipt.json`，不把非零 full check 解释为 PASS。完整 PR 接受仍待完成。
