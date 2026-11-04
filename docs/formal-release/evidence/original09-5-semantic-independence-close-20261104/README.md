# 原题 09.5：权限、义务、发生与文书效果的语义独立性

**状态：** 源模块与冻结原题的有限 ToyTheta 义务映射为 COVERED；完整记录验收、PR 与 post-merge 核验仍待完成。source checkpoint `0b6bd5aa8ade03b6132dffe2b3dbcf00634ca416`，tree `1355460ed08d9083048197d56ced01c9f02f7c4e`，parent `f0b0e9b8ec9540d6fa650a1c7f41fbc495225cd4`。changed-module run [`41773914244:1`](https://github.com/laubeing-droid/legal-math-modeling/actions/runs/41773914244)，job `126389720124`，只构建 `JurisLean.Candidates.SemanticIndependenceAudit20261104`。Artifact `changed-module-only-41773914244-1`, ID `13296003017` 的 ZIP 为 1457 字节，SHA-256 `87b6f383a0229e8db07617440536ab95cb15f943e6c71bf37c5a6341c4b34ded`；本包的 `changed-module.log` 与 `module-plan.json` 是该 ZIP 成员的原始字节拷贝。CI 有 7 组 theorem `#check`/`#print axioms`、2 个定义检查，错误 0、`sorryAx` 0。直接源码/工具链 pin 见 `verification.json`。

## 冻结条文与源证据

冻结题单为 `09_关系效果数量账本与履行.md` L169–176，子项 L171、L173、L175，关联 U09.3。源文件中的 `ModelsTheta`、`semanticEntails` 与七个 theorem 的完整 FQN 列在 `verification.json`；模型和结论只覆盖显式构造的有限 ToyTheta。

- **L171：** `three_complete_witness_models` 给出同一个有限模型里的见证；`obligation_semantically_entails_power` 证明本 ToyTheta 下 O⇒P；三个 non-entailment theorem 分别给出 P不蕴含O、O不蕴含发生、发生不蕴含P 的见证。这不是对任意 Theta 或真实法域的普遍结论。
- **L173：** 三个实际 witness 的输入位 `(l,g,b)` 为 100、110、001，其中 `l` 是许可、`g` 是文书触发条件成立、`b` 是行为发生；同一模型定义输出 `P=l`、`O=l∧g`、`X=b`。因此 100 给出有许可但触发条件不成立且未发生，110 给出许可与触发条件成立但未发生，001 给出无许可/无触发条件但行为已发生。各 false 位由这些明示语义确定，不是可任意互换的零位。三个 non-entailment theorem 据此分离 P、O、X。已有事件位分离保留为既有证据，不冒充这组同一 ToyTheta 反例。
- **L175：** `same_received_pay6_document_different_obligation` 使用同一 context 与收到内容 `pay 6`，issuer 不同，证明相应模型中的权利/义务结果不同；`received_content_and_permission_entail_obligation` 证明显式收件内容与 permission 条件蕴含同一个 Obligation。该结果依赖源码中明示的文书与 licensed/triggered 条件，不证明现实文书效力。

R1 run [`41773241403:1`](https://github.com/laubeing-droid/legal-math-modeling/actions/runs/41773241403)，Artifact `changed-module-only-41773241403-1`, ID `13296300452` 是失败历史，success binding 为 false，不能作为成功证据。R1 的两处错误来自 Bool/Prop 语法及 proof rewrite；R2 只改这两处 proof tactic 语法，`ModelsTheta`、命题、量词和前提均未改变。R1 编译恢复输出出现的 `sorryAx` 是失败后的 Lean 恢复诊断，源文件没有显式 sorry/admit/axiom。

## 边界

本轮新证据只说明有限 ToyTheta 内的语义关系和反例。它不证明任意 Theta、真实法域或生产运行时上的语义独立，也不把既有事件位差异当作本模型的证明。当前 U00 的 15 条消费边均没有实际 caller 消费该 toy 模型或文书桥，故 `affected_edges=[]`，没有改写 U00、边评级或制造运行时接线。原题允许 toy 论证；本轮不另加真实法域实例义务。

U09.3 是以前已关闭的债项，不因本记录重开。全局 discharges、Step 2、`math_flip` 仍为 false；工程 105 项、6 cuts 与完整模型/PR 验收不由 changed-module 绿灯升级。
