# 原题 09.4：有序债项分配与参数化计息

状态：数学映射为 **COVERED**；本包记录 source/module 证据，完整记录验收及 post-merge 核验仍待完成。Source checkpoint `4a1156c7d19081d0f67dfee8633b82d5a6f3fed7`，tree `b3c5c2eb92b4fa4da706d95515399157fe1409ef`；changed-module run `41761045186:1`，job `126348571018`，仅构建 `JurisLean.Candidates.ParametricAllocationAudit20261104`。CI 输出有 12 组 theorem `#check`/`#print axioms`：5 个新目标、7 个复用目标，以及 2 个 definition-only 检查；8514 个构建任务成功，错误 0、`sorryAx` 0。已保留 R1/R2 失败包作为历史，不计入成功证据。官方 probability audit surface 生成器随后从可变根 `JurisLean/AxiomAudit.lean` 去除了这三条重复 `#print axioms`；三个 declaration 仍由源文件保留，并在本新模块 footer 被审计。metadata-only checkpoint `c19c7fef45e7b9f613a869c06c9a63bad482e3f5` 的 parent 是 source checkpoint `4a1156c7d19081d0f67dfee8633b82d5a6f3fed7`，该 metadata commit 本身未跑 source CI。冻结的 `Final20261021/AxiomAudit.lean` 未变。

## 冻结条文与本轮证据

冻结题单为 `09_关系效果数量账本与履行.md` L161–168；09.4 子项为 L163、L165、L167，绑定 clauses U09.3。精确 source/tree、artifact digest、14 个 source/toolchain pin 和目标列表见 `verification.json`。Artifact `changed-module-only-41761045186-1`, ID `13291075352` 的 ZIP 为 5707 字节，SHA-256 `743033ba00617068a73bf9d73341b5578211ce7daf33c565e6c2101c1dc85785`；本包中的 `changed-module.log` 与 `module-plan.json` 是该 ZIP 成员的原始字节拷贝。

- **L163：** 固定有序的非负金额列表用于向量记账；一般守恒、非负与完整记录 frame 复用已有结果。本轮新例实际比较 `afterPay 5` 作用于 `[id1=5,id2=5]` 与反转列表：投影分别为 `[(1,0),(2,5)]` 与 `[(2,0),(1,5)]`，两边余额均为 5。它说明相同总额不固定受偿身份；不把输入列表顺序解释为法律优先顺序。
- **L165：** 新的 `AllocTheta` 证据条件绑定实际 items、付款身份、来源债项/行索引、法律时间版本与 facts。其 `certified_allocation_updates_actual_list` 将证书连到实际列表金额更新，证明逐项范围、总量/余付关系、同单位、长度与顺序、完整非金额 frame 和实际余额守恒。沿用的 `Ledger.u09_3_general_allocation` 是有限金额核；本轮不把 greedy updater 冒充任意分配桥，也不宣称付款现金或法律清偿被更新。
- **L167：** `AccrueTheta` 显式接收实际状态、`t0/t1`、formula、rounding、effectiveness 与事实条件，并连到现有 `Ledger.accrue`；现金、paid、refund 保持不变的部分复用 `u09_3_accrual_not_cash`。`Acceptance.opening.state` 增加 1 后余额为 11 的目标只是在 Lean 中的计算反例，不表示现实法律已批准计息。

## 条件与未证明扩展

原题中当前条件结论保持其精确范围：同单位、身份绑定、分配上下界与付款预算均作为证书可核实条件出现。opaque theta/facts 谓词只表达输入条件，不证明现实中的具体法律规则或事实。没有默认单利/复利、计息基数必等于余额、费用与债项单位必相同，也没有对所有金额强加非负计息条件；缺少条款/事实时不从空缺推断公式。

固定 V2 目前仍为标量/greedy 表面。本轮接口是条件 quantity producer，尚未证明 V2 已一般调用任意 theta 多债分配；具体法律排序规则及事实实例、一般 theta 执行接入及由此产生的现金/法律状态效果仍属未证明扩展。没有新增单位转换或未来产品义务。U09.3 仍是此前已关闭行，本包不重开它。全局 discharges、Step 2、`math_flip` 仍为 false；工程 105 项、6 cuts、完整模型/PR 验收不由 changed-module 绿灯升级。

## Source attempts

- Run [`41759899549:1`](https://github.com/laubeing-droid/legal-math-modeling/actions/runs/41759899549)，job `126344859791`，Artifact `changed-module-only-41759899549-1`, ID `13289389530`：失败，保留为 R1 历史，`success_binding=false`。
- Run [`41760546379:1`](https://github.com/laubeing-droid/legal-math-modeling/actions/runs/41760546379)，job `126346970499`，Artifact `changed-module-only-41760546379-1`, ID `13290342081`：失败，保留为 R2 历史，`success_binding=false`。
- Run [`41761045186:1`](https://github.com/laubeing-droid/legal-math-modeling/actions/runs/41761045186)，job `126348571018`，Artifact `changed-module-only-41761045186-1`, ID `13291075352`：成功，唯一 source success binding。
