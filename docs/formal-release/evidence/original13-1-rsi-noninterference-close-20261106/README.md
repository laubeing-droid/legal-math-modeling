# 原题 13.1 参数分区与准入证据

状态：SOURCE_CHANGED_MODULE_AND_RECORD_CHECKS_AND_CI_INDEX_PASS / PR_ACCEPTANCE_PENDING。本包登记原题13.1 L95/L97，并关联13.2纯归引，尚待本批完整PR及合后接受。

冻结依据为题单 13.1 L93–98、补正正文 S13 L218 和总稿 L622–643。以下 `RSI` 指 `JurisLean.Candidates.Final20261021.RSI`。

## L95 五类提议转移与非干扰

`RSI.State` 的五个字段对应机制、规则包版本、个人 checkpoint 函数、测量日志序列和操作日志。冻结总稿给出的可写集合包含授权流程可以追加的日志。下表给出 Lean 中的纯提议转移和实际 frame，操作日志在这些纯转移中保持原值。

| 操作与输入类型 | 结果和实际写字段 | Frame 和前提来源 |
|---|---|---|
| 数据追加，`Behavior.MeasurementLog` | `appendData` 产生新状态，`D'=D++[row]` | `u13_2_data_frame` 保持规则、机制和整个个人函数，定义保留 logs。记录来源、标签和用途按冻结合同外给。 |
| 一次 Cond，两列 `List ℚ` | `conditionalEstimate` 返回本次 `Result ℚ` | `u13_2_condition_does_not_train` 证明 `prepareUpdate s .condition = s`，持久状态全保持。实际分支检查长度、非负权和有效权和。 |
| 个人提议，`PartyId × Checkpoint` | `prepareUpdate s (.personal who candidate)` 给指定主体的候选替换 | `u13_2_personal_frame` 保持规则、机制、数据、其余主体，定义保留 logs。同一主体的新值由函数更新代入得出。数据证据与生效权限仍按冻结合同外给。 |
| 规则版本提议，`Nat × SourceRef` | `prepareUpdate s (.rule version ref)` 仅写规则版本 | 定义保持机制、个人函数、数据与 logs。允许替换及其适用性由独立授权合同判定，`ref` 是引用。 |
| 机制版本提议，`Nat × SourceRef × SourceRef` | `prepareUpdate s (.mechanism version validation ref)` 仅写机制版本 | 定义保持规则、个人函数、数据与 logs。独立验证和授权是两项外部输入。 |

令 `x=(c,e)`。固定的 `eval` 在 `proposed_rule_service eval s x` 中只接收 E、N 和 x。个人更新保持 E/N，并在本条条件下保持 c/e。两次调用的三个参数逐项相等，直接复用 `u13_1_noninterference`。读集合同同时约束 x 的构造，避免通过隐式输入把个人预测送进规则服务。

## L95 合法统计证据改变案件判断的有限实例

同一主体先有版本 1 的 checkpoint，预测为 2/5。实际 `prepareUpdate initial (.personal owner …)` 将其替换为版本 2，预测为 3/5。`u13_2_personal_frame` 给出 E/N 相等。固定规则版本 1 允许本案的统计输入经过 `statisticalInput`，入参分别为外部已准入的 `some (2/5)`、`some (3/5)`，闸门逐次核对准入值与实际 checkpoint 输出相等。固定的 `caseValue` 在 e 有值时比较 e 与 1/2，前后分别得到 `some false` 与 `some true`。外部入参为 `none` 时，前后输出都为 `none`。

对应具名声明为 `JurisLean.Candidates.RSIAdmittedStatistics20261106.admitted_statistics_change_case_value_under_fixed_rules`。这是同一次个人更新伴随两个独立准入值的有限实例。两次 c/e 的 e 分量不同。准入的事实与效力由该外部输入承载。规范包的保持和案件读数的变化分别登记。

## L97 泄漏反例及排除

冻结总稿 L643 的错误实现让规范优先级直接读取 `θ>1/2`。取 E、N、案情与证据输入相同，两个候选规则的顺序由该比较切换。θ=2/5 时比较为假，选择第一候选。θ=3/5 时比较为真，选择第二候选。同一个规范读数随着内部经验参数改变。这个反例使用的是直接读取 θ 的错误路径，和上一段的外部准入证据路径有不同输入合同。

目录或文件名无法排除两条路径共享可变引用。用 `proposed_rule_service` 的显式参数类型限定规范 evaluator 的读集，并用 `u13_1_noninterference` 核对同一 x 上的更新前后输出。若外部证据许可未定，证据分支保持无准入值，实际规范冲突仍走既有的授权裁决合同。

本题的状态提议、准入实例和泄漏反例只承担 13.1 的数学义务。当前 U00 边 12、13 的具名消费者各有其原合同，本批实例没有新增实际消费路径。

## 复用的实际证据与本轮 source

五类转移使用原RSI源码 `proofs/lean/juris_lean/JurisLean/Candidates/Final20261021/RSI.lean`，4175 bytes，SHA `9a5bc5e53c8e4d12a4bc4006d637f063ccf835165f3c3b8f3b5fa11d4fa7ac8e`、Git blob `b0239a3cb86b91153dc1ec45f228e648f52e6aab`，本批原字节不改。[PR129](https://github.com/laubeing-droid/legal-math-modeling/pull/129) 已接受的 Authority exact subject M `d5d31e480d91470e3de2caf53eabe0c67a686073` / tree `6eb3436690e27dabd528366c6c64e4b1c939f1a3` 提供同x非干扰和frame的实际输出：axiom-audit.raw.txt L1625–1631为u13_1_noninterference（无公理），lake-clean-build.log L9590–9613为personal_frame（仅propext）、condition_does_not_train和data_frame（均无公理）。完整run/job/artifact与文件pins、逐段raw见verification.json；它们属于已接受full-root复用证据，不冒称本轮source的额外check/axiom targets。规则/机制提议的其余frame按已编译prepareUpdate定义逐字段归引，独立授权不由纯提议函数自产。

新增声明的独立 [R2 changed-module run 42081631722](https://github.com/laubeing-droid/legal-math-modeling/actions/runs/42081631722)，attempt 1，job `127435917108` SUCCESS；source `202cf6e5dc68915d8c38fd03c5eb68a2cb7302e9` / tree `6f14b7de2ff6d0e6741ca2dcf03ec04381341870` / 唯一parent R1 `b11d0d4aedf838451d301bf08bf2f01066cc87c7`。源2506 bytes、57行，SHA `b94d720d3a18f9dacac1473424abc23107cd19e756e0d819464428b33133400a`，blob `e0268ccf9b1ef7c139d3905e89e9fb81d810811e`。1 own / 0 reused targets / 1 pair / 2消息，0 errors / 0 sorryAx，实际公理[propext, Classical.choice, Quot.sound]。原日志有1条 unnecessarySeqFocus linter warning，原样保留，不因样式重跑。其余七个job因mode条件跳过，不能代表本批完整PR通过。

官方 Artifact `changed-module-only-42081631722-1`, ID `13440732388`，ZIP 916 bytes，SHA `47935448aa926e610deea72968983893e5d6caf03e2a0a67139aa5f31c291cce`。成功raw module-plan.json为265 bytes、SHA `0ce83f1ffcf82e43d28215cd8af7c698f1c1e11873537f835d8048740499d243`；changed-module.log为1228 bytes、SHA `3fbb71135e09f3ede9149c3e591f8e40a233aebfe71562b3354ac1c545d5ade2`。逐目标FQN/源码行/raw完整公理输出直接取实际 source-target-outputs-r2.json，未默认回填。

[R1失败 run 42080749208](https://github.com/laubeing-droid/legal-math-modeling/actions/runs/42080749208)，attempt 1，job `127432839563`，source `b11d0d4aedf838451d301bf08bf2f01066cc87c7`，官方 Artifact `changed-module-only-42080749208-1`, ID `13440636593`，ZIP 1658 bytes、SHA `41797cd31eacbe57056dd8fe69b3328b76dd78ab03a561f6bfa9c9d7d73fd168`。原ZIP/raw/metadata留在 `D:/tmp/original13-1-source-r1/`，明确diagnostic和pins见verification.json。decide未充分展开proposed_rule_service的失败恢复产生sorryAx，源文件无sorry文本；失败raw不混作成功证明。R2仅将该单行改为显式simp展开及decide +kernel，所有定义、陈述和外部前提逐字不变。

source通过后root checkpoint `f21d511dc837f42bd35d0b4a3b79090be55bb8c1` / tree `cdc11bc68bf79414544a2f714fa7912a77e04ef1`，parent为成功R2，仅新增root import，root blob `1a8bf44c8a3aba8f1e4524ebe19a37113fa540cd`。AA writer单次exit0且Git无变化，无额外AA checkpoint；manifest实际绑定该clean root checkpoint，596 files / 0 diverging。source proof、root/manifest和未来records H/M身份分开。

L97只归引冻结总稿L643的2/5→3/5优先级泄漏及其读集排除；没有新增L97 Lean定理。外部准入值的事实/效力、规则和机制变更的授权/验证、实际存储的精化仍是独立条件；同x非干扰不覆盖主动改变e的合法统计证据路径。当前U00 edges12/13实际消费、caller、历史、评级与文件均不改；U50仍50 wiring/0 narrow/0 open/124 bindings，discharges、Step2、math_flip均false。canonical仅13.1/13.2候选COVERED，82/11/4→84/10/3；其他95数学行、105工程行、6cuts不变。

同批13.2 L101/L103的A/B/C有限提议表、声明观察与交换关系、同一10/7材料的重命名/类别变化反例，只追加归引到[既有U13.3证据包](../u13-3-debt-close-20261028/README.md)。旧独立module与PR129接受证据、原四源pins保留；无新13.2 Lean或module CI，不把外部权限当已实现。完整关联元数据见verification.json。

本地记录与索引验收：7 项 derived writers 各一次完成（AA先单次检查无Git内容变化，其余六项接续），12 项 required checks 均 exit 0，受影响稿件回归为 2 passed in 0.98s；CI index 为 619 runs / 1503 quotes，index tests 为 12 passed in 5.81s，标准 --check exit 0。旧 617 条 metadata 保留，仅新增本轮失败R1和成功R2两条 source run；实际 staging、full/authored diffcheck 结果及官方 raw 尾空格诊断另见 `D:/tmp/original13-1-records-20261106/index-stage-r1-receipt.json`，不把非零 full check 解释为 PASS。完整 PR 接受仍待完成。
