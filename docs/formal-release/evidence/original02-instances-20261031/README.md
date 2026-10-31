# 原题 02.2 / 02.3 / 02.5 / 02.6：已审有限实例补充证据

本包是原题进度对照使用的非 debt 模块证据，`closes_debt` 保持 false；它不是第二个归档关项，也不改变 U02.2/U02.3 的归档文本。source `86f8f643437a35ee0bedc149ecd04a55f0f9aa2e`、run `41163607765` / attempt 1 / job `124426303750` 通过实际 changed-module CI。Artifact `13027184875`（`changed-module-only-41163607765-1`）为 6231 bytes，SHA-256 `26205b64130b95078ff659e1718d9be1a7778568d2e16bbb0fdaeb3254ff1aeb`；原 ZIP 两成员和从实际 driver 输出逐块提取的16块指纹见 `verification.json`。5个目标的 `#print axioms` 词汇计数为 propext 5、Classical.choice 2、Quot.sound 5；对象 `#check` 有6行、3个不同对象名。

## 本次实例与原题行

- **02.2**：`stale_resource_checks_do_not_compose` 用 0→1→2 资源状态给出“相同旧状态的两次 gate 通过，连续第二步后的 invariant 失败”的有限反例；`preparation_failure_frame_and_unknown_commit` 记录内部准备失败时 proposal 为空、payment.current 保持 initial、无 outcomes、unsupported obligation，并区分 `unknownCommit` 无可读 poststate。旧 U02.1 Pipeline/Trace 和 U10.1 实际 refresh-to-Step 证据继续承接真实步骤/状态不变量合同；本次有限实例不声称具体数据库或外部副作用精化。
- **02.3**：`finite_gate_has_nonempty_safe_instance` 给出过滤后非空安全动作集并保留来源 proposal；`hidden_permissions_force_refusal` 给出不可区分观察下无法同时放行两个相反许可状态的有限边界。既有 `HarnessRisk` 证据继续限定条件风险分母；覆盖、误阻断与“零覆盖不等零风险”使用既有 legal-action-domain/HarnessRisk 证明，不由本次有限 gate 例子单独概括。
- **02.5**：`checked_trace_does_not_supply_primitive_truth` 证明可检查/可重放的有限 trace 不推出 primitive fact/rule truth 或相应模型关系；`hidden_permissions_force_refusal` 另给相同可见观察、不同许可的不可区分边界。通用 trace/checker 语义仍引用既有 `finite-legal-validation-20261027` 与 U02.1 evidence，不扩成监控器普遍能力定理。
- **02.6**：`preparation_failure_frame_and_unknown_commit` 将准备失败帧与后态未知 commit 分开；`stale_resource_checks_do_not_compose` 展示重试/复用旧 gate 不能把旧状态检查当成连续状态的保证。拒绝、失败保持、真实消费路径继续引用既有 `legal-action-domain-20261027`、U02.1 Pipeline 和 U10.1 协议证据。

复用证据身份和原包位置在 `verification.json` 中列出：既有 legal-action-domain、HarnessRisk、U02.1 actual-pipeline 和 U10.1 protocol。新实例只表明有限模型中的指定性质与边界；它们不证明现实输入/规则全部为真、不构成生产部署或全部工程 105 完成，也不关闭原题之外的 U00 全路线。
