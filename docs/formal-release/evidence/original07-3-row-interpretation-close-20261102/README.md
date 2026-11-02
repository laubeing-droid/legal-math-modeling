# 原题 07.3：固定原始事件解释与 rowSeam

状态：本行数学映射为 COVERED；canonical 候选 C 待完整记录 PR 验收，完整验收前不视为 main 已关账。本包补的是冻结题单 07.3 L279 中 raw / payload / Interpretation / rowSeam 的条件连接与同 raw 反例，不扩成全局来源真实性或任意 extractor 结论。

## 冻结承诺与既有结果

冻结题单 07_法律对象共同模型与表示.md L277–280（U07.3，L279）要求 CaseRecord 桥、observedRef / observedRel 关系，以及原始事件、payload、Interpretation 与 rowSeam 的对应。冻结源文件 SHA256 为 1bf38abdd67bbacde464bc47814a672220a223d4a553f3cebf8812b066b3458a；本包保留其原路径与行范围，不修改冻结文件。

07.3 原有三项 evidence 对象完整保留在 canonical 原行：SourceCompilation 的固定快照提取、SourceStages 的 typed μ / 历史支付绑定，以及先前 U07.3 固定绑定实例。本包再引用这些已接受结果，复用 actual_record_observations、extracted_observed_reference_resolves、static_source_semantic_and_quantity_bridge、actual_record_and_binding_interpretation 与 same_material_record_do_not_determine_semantics。这些既有结果仍受各自已声明的 accepted-output、mu / resolveFaithful、objectMeaning / paymentMeaning 等前提约束；本包不重证也不扩大它们。

## 本轮局部类型与条件解释

新增 EventPayload 仅含 formation rel 与 performance obligor rel amount。新增 EventSourceRow 仅含 source : String、sourceRef : String、sourceOrder : Nat、已有 JurisLean.Event 与该 payload。这里的字符串 sourceRef 是本局部行合同；它不等于已有的 Nat 包装类型 Final20261021.SourceRef。EventSourceRow 不是 ConsumedView 新字段，也没有改写旧 CaseRecord。

rowSeam 按 payload 构造既有 InstitutionalEffects.SeamEvent JurisLean.Relation；formation / performance 的 event id 都取同一行 raw.eventId，其余构造字段来自 payload。外部 meaning 的类型是 MaterialSnapshot → Nat → String → String → JurisLean.Event → Option EventPayload。对固定 material、branch、meaning 与行，Interpretation 明确要求 meaning 返回该行 payload；semanticSeam 对同一个 meaning 的结果作 Option.map，并按 payload 映射到旧 SeamEvent。

interpretation_rowSeam 证明：在上述明确 Interpretation 前提下，meaning 经 semanticSeam 得到的结果恰为 some (rowSeam row)。这是条件语义连接。meaning 是外部给定输入，Lean 结论不证明 raw 事件来自真实来源，也不证明 meaning 对原材料忠实。旧 resolve / μ 路径仍按旧定理的显式前提复用，不被这个局部 meaning 替代。

## 同一 raw、不同 payload 的有限反例

same_raw_event_distinct_row_seams 对固定 material、branch、既有 CaseRecord 构造两行。两行的 source（σ）、sourceRef、sourceOrder 和完整 raw Event 全相同；因此完整 CaseRecord 相同，record.key（κ）也相同。raw 为 ⟨"event", 0, "formation"⟩。两 payload 分别携带 relationId 为 r0 与 r1 的既有 JurisLean.Relation，其余 Relation 字段相同；于是 payload 不同且 rowSeam 不同。同一个、先固定的 meaning 返回 formation r0：解释接受第一行而拒绝第二行。

这个例子说明同一 raw Event 与相同记录键不足以决定 payload / rowSeam 的语义；条件解释由显式 meaning 区分。它不是现实材料真值反例，也不声称两行属于旧 ConsumedView、同一真实 catalog，或新接入旧 Pipeline。

## 本轮实际模块构建与选取目标

Changed-module run 41387601998:1 的 source subject 为 commit 5212227eb12f707d6a890f3082acf61d86a9f525，tree 42e8158a10e011ed4a668fbc0c50afda10e1da39，branch formal/close-original07-3-raw-semantics-20261102，job 125091802196 成功。Artifact changed-module-only-41387601998-1, ID 13115534601 的 ZIP 为 7,835 B，SHA256 3d5eeca34aa9a8ea41acf53afbe3c69ef2155787150afbd5593dca30261e3d6e。实际 plan 只请求 Audit 入口；raw log 显示新 source 于 L722 构建、新 Audit 于 L723 构建，整体于 L747 成功。日志中未见 error: 或 sorryAx。

下表的 8 项是本包选取的实际输出，不是导入构建的全部输出。旧行号指已接受的 07.1 共享日志；新行号指本包逐字节保存的 changed-module.log。

|具名目标|声明位置|实际输出|公理|
|---|---|---:|---|
|SourceCompilation20261027.actual_record_observations|SourceCompilation L157|旧日志 7635–7640|[]|
|SourceCompilation20261027.extracted_observed_reference_resolves|SourceCompilation L163|旧日志 7641–7651|[propext]|
|SourceStages20261027.static_source_semantic_and_quantity_bridge|SourceStages L509|旧日志 19458–19485|标准三项|
|SourceStages20261027.nonempty_source_stage_fixture|SourceStagesAudit L190|旧日志 19488–19490|标准三项|
|U07_3FixedBindingAudit20261029.actual_record_and_binding_interpretation|U07_3 L89|旧日志 19763–19807|标准三项|
|U07_3FixedBindingAudit20261029.same_material_record_do_not_determine_semantics|U07_3 L237|旧日志 19824–19849|[propext, Quot.sound]|
|Original07_3RowInterpretation20261102.interpretation_rowSeam|本包 source L66|本包日志 724–731|[]|
|Original07_3RowInterpretation20261102.same_raw_event_distinct_row_seams|本包 source L76|本包日志 732–746|标准三项|

“标准三项”指实际日志中的 [propext, Classical.choice, Quot.sound]。新 plan 的唯一 include 是 JurisLean.Candidates.Original07_3RowInterpretationAudit20261102；该 Audit import 并构建本包 source。被导入旧模块的额外 Audit 输出不计入上表 8 项。

## 保留的实际原始日志与边界

本包 changed-module.log 是从 Artifact changed-module-only-41387601998-1, ID 13115534601 的 ZIP 成员原字节复制，54,184 B，SHA256 bd40ef731a16f32d9eaf0931a797375142551adf52a3c9583fc71a897aafaae2。API 元数据、ZIP、plan 和展开成员的具体路径及摘要见 verification.json。旧完整构建日志不重复复制；其实际 artifact 来源在 Dtmp，字节相同的跟踪文件为 [lake-clean-build.log](../original07-1-source-identity-close-20261102/lake-clean-build.log)，5,216,301 B / SHA256 663af0a0b4256d0d8c97b53c30a08f55fa878a33d587c433c558550afcf898bf。

本包只把当前数学映射提为候选 C。canonical 完整记录 PR、独立复核与合并前，本行不视为 main 已关账。原有三项 evidence 对象及其分母、subject 与边界均保持原样。现实来源真实性、任意 extractor 忠实性以及旧运行管线是否消费此局部 EventSourceRow 仍是各自原状态；本包没有声称接入或关闭这些范围。
