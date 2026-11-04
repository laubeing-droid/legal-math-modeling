# 原题 10.3：追加式撤销与双时态历史

**状态：** Source R2 changed-module CI、11 项记录检查、额外 gap-status 检查与两项 paper 回归均通过；PR 全链与合后验收仍待完成。R1 失败保留为历史。来源：R1 [41902182379](https://github.com/laubeing-droid/legal-math-modeling/actions/runs/41902182379)；R2 [41904164860](https://github.com/laubeing-droid/legal-math-modeling/actions/runs/41904164860)。

## 冻结义务与本轮证明

冻结题单 `10_授权变更与多步法律轨迹.md` L115–122，子项 L117、L119、L121，关联 U08.1 与 U10.1。本轮只映射这三段；保留各自原有边界，不把有限模型扩成任意追溯规则或运行时组件。

- **L117：** `append_replay_enable_replace_revoke` 以 v₀、v₁ 和启用、替代、撤销三事件运行实际版本选择与重放。`overwritten_status_pollutes_fixed_historical_query` 展示可变 current status 如何污染固定历史查询；`past_knowledge_and_current_material_are_distinct` 区分当时知识截点下的判断与用今天材料评价过去法律时点。
- **L119：** `fixed_cut_replay_uses_invisible_append_stability` 复用不可见追加下的稳定性；`late_old_event_is_not_past_knowledge` 排除晚到旧记录伪装成当时已知；`unknown_retroactivity_preserves_different_past_outcomes` 保留 prospective 与 fromReplacement 两个明示分支。`expiry_revocation_and_precedent_replacement_have_distinct_effects` 在有限实例中区分授权到期、规范撤销与先例替代。
- **L121：** `same_bound_receipt_requires_five_cache_dimensions` 与 `five_cache_dimension_erasure_witnesses` 覆盖对象、问题、规范读取版本、知识截点、法律时点五个必要绑定维度及逐维擦除反例。`historical_environment_is_not_current_cache` 区分历史环境与当前缓存；复用 `check_full_bindings` 与 `timed_compiler_consumes_selected_version`。五维投影是必要绑定条件，不是完整评价可复用的充分条件。

本模块只给出有限历史重放、选择和绑定证据；不实现运行时缓存，也不证明任意追溯效力或现实法源事实。十五边复核表的边 9（账本→授权/轨迹）登记本轮历史/当前材料读法、追加撤销与当前授权回执复用边界，见[本轮关债包](README.md)及独立[source CI](https://github.com/laubeing-droid/legal-math-modeling/actions/runs/41904164860)；这是条件链的证明证据补登记，不升级旧 U00 接线、现实授权或旧 Pipeline 完整合同的结论。未改变旧 caller、参数流、公共 callee、运行时消费者或接口；不改边评级。边 3 的来源 DAG→消费者缺口无本轮对应贡献，不登记。

总账只将原题 10.3 从 PARTIAL 调为 COVERED，原题计数为 74 COVERED / 15 PARTIAL / 8 NOT_RECONCILED。105 项工程要求、6 个 designated cuts 不变；全局 discharges、Step 2 与 `math_flip` 仍为 false。

## Source 结果与失败历史

Source checkpoint `0d660ec522b9250056399401e9dd682e36fceaac`，tree `2f7d37b4987e10f51d4f649e546519a3f9292f37`，parent `d3a7f17e5dd4ae8b95cd5b6dfae9d990d3b03231`。R2 run `41904164860`, attempt 1, job `126834234100` 成功；该 changed-module run 只构建本模块，其他七个 workflow jobs 按条件 skip。Source CI 不是全链或 PR 验收。

Artifact `changed-module-only-41904164860-1`, ID `13358909538`：ZIP 24,468 bytes，SHA-256 `da293ab030a27f43dc3390558eb3cc29ad3b05aa485c81c74645acdc4953fedb`。本目录的 `module-plan.json` 与 `changed-module.log` 是 ZIP 成员原始字节；两成员 SHA、13 项 `#check` / `#print axioms` 结果与源 pins 见 `verification.json`。

R1 run `41902182379` / Artifact `changed-module-only-41902182379-1`, ID `13358767529` 为失败历史：第 127 行引用已更名的 `at` helper，后续第 160 行 `decide` 未能化简；失败输出出现 `sorryAx`，不计为通过目标。R2 只把 `gamma := at 2 2` 改为 `gamma := gammaAt 2 2`，命题与前提未变。R1 artifact ZIP 为 25,353 bytes，SHA-256 `6519a68635ca52f5356a279623004f800dba8b8714e1be09f0ddeecd9de7a3dd`；原始包保留在 Dtmp。

17 项结构测试在 R1 source commit 前运行并通过，R2 未重跑。两项 paper 回归、11 项 required checks、gap-status check 与 CI-index 检查的范围和独立收据见 `verification.json` 与 Dtmp 记录目录；它们不替代 PR 全链验收。

## 记录范围

本包绑定 frozen 10.3 的 L117/L119/L121、R2 source subject 与 changed-module artifact。`verification.json` 保留 10 个本模块目标、3 个复用目标、失败历史、源 pins、生成器/检查命令及真实收据。有限构造不证明任意历史查询、通用缓存实现、生产 caller 接线或现实法律正确性。
