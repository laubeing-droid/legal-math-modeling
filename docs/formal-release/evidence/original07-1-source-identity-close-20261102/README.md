# 原题 07.1：来源快照中的有限对象身份

**记录状态：独立证据与交付草稿；canonical 行尚未更新。**本包只整理冻结 L271 的对象身份范围和已有证明，不新增 Lean 定理、现实实体解析算法或 runtime caller。原有 SourceRepresentation 与 SourceStages 证据包及各自 accepted subject 保留不变。

## 冻结原题

冻结题单 `07_法律对象共同模型与表示.md` L269–271 的标题为“法律对象与规范身份如何由 μ 获得，而非由字符串冒充？”。L271 要求：

> 在明确的来源快照和对象种类范围内，给出 μ 的定义域、证据义务及 SameObject 等价关系。构造三个有限例：同一付款有两个材料副本；不同付款共享裸 eventId；同一表键下有两条不同行。说明规范 ID 何时精确刻画 μ 等价类，区分可靠性（不误合并）与完备性（不漏合并）。对 sourceOrder、历史下标、来源引用、eventId、债项 ident 分别说明是位置、引用还是对象身份。完成于一个非空身份模型与至少一个错误识别反例，不要求现实实体解析算法。

对应 canonical row 的 `source_lines=[269,272]` 与 `clauses=[U07.1,U07.3]` 原样保留。此处只对应 07.1，不把 07.3 的其他义务折入本包。

## μ 的范围与有限例

SourceRepresentation 在固定语境中把 `μ` 明确作为 `SourceRef → Option ObjectId` 的部分解释输入。其已定义域是 `ResolvedReference μ := {r : SourceRef // ∃ object, μ r = some object}`。`InterpretedSame μ a b` 表示两项引用由 μ 解释为同一个 `ObjectId`；`resolved_identity_is_equivalence` 证明它在此已解析域上是等价关系，`semanticKey` 取已给 μ 见证中的对象键，`semantic_key_exact` 证明键相等恰等于该 SameObject 关系。`resolveObject` 只在匹配行恰好一条时返回 known；无匹配为 unknown，多条匹配（包括重复行）为 conflict。

固定合成模型 `identityExample : SourceRef → Option ObjectId` 的实际赋值是：

| SourceRef | μ 的值 | 例子中的身份意义 |
|---|---|---|
| 0 | payment 1 | 与 Ref 1 表示同一付款的材料副本 |
| 1 | payment 1 | 与 Ref 0 同对象，虽引用值不同 |
| 2 | payment 2 | 与 Ref 0/1 是不同付款 |
| 3 | none | 未解析，不与自身或其他引用建立 SameObject |

`bareEventExample` 对所有引用都返回 EventId 9；所以 Ref 0 与 Ref 2 共享裸 eventId，却不属于同一个 μ 等价类。这是第二类有限反例。第三类是独立的表键例，不属于 `identityExample` 的对象分类表：`firstAmount [(1,7),(1,9)] 1 = some 7`，行序反转后为 `some 9`。共享表键及 first-match 结果都不能单独证明对象身份。

L271 指定的五个字段按现有模型作如下区分：`sourceOrder` 与历史列表下标是位置；`SourceRef` 是引用/查找域元素而不是对象身份本身；裸 `EventId` 不足以识别对象；债项 `ident` 是特定视图内的匹配键，不能代替完整债项相等。SourceStages 的 `sameDebt` 比较债项 `ident/kind/basis/beneficiary/status/amount` 及其 `debtRel/obligor/unit`；成功绑定还核对付款、债项、关系的唯一匹配行和完整载荷字段。该结论仍限于给定的 μ、快照和 typed rows。

这里的证据义务是：对适用范围内的引用，外部解释 μ 必须提供适当的对象见证；在已解析域上，证明说明 μ 所定义的同对象关系与 semanticKey 相等一致。有限非空模型由 Ref 0/1/2 提供。Lean 证明不会自行证成现实 μ 的真实性，也不声称实现现实实体解析器。

## 两个既有证明包与本次输出

- `source-representation-20261027` 保留其独立 PASS：15 个命名类型/公理目标、12 个 guarded execution；subject `9a2d0bbfff264c8593fe148378a64460741a250a`，run `40457212969` / job `122033215316`。其原范围还包括观测充分性和有理数量桥，本包不重写或扩大该范围。
- `source-stages-20261027` 保留其独立 PASS：28 个命名类型/公理目标、22 个 guarded execution；subject `6d2c873824692e750fa929855fb2587c0d009cda`，run `40468260025` / job `122068840408`。它提供 typed identity、完整债项比较和有限来源阶段消费者，不证明现实来源真实性。
- 本包把这两个 Audit 中的 43 个 `#check` / `#print axioms` 目标映射到 PR98 的实际 Authority full-build log。实际 build 使用 accepted PR98 synthetic subject `223bf1529e1f11d05187b2f3723d4552d83befcd`、tree `31c197b7819c48146b93f0abfa549399c9fd31eb`；API run 的 head 是 feature tip `9de1037a28c7e201b994889bf2bc1bf0faab1e50`，job `lean-full-clean-build` 成功。字段语义分别列在 verification，不把 PR API head 冒充 synthetic build subject。
- 43 个目标按各自声明行、Audit 行和原始 log 行逐项映射；其中 15 个来自 SourceRepresentationAudit、28 个来自 SourceStagesAudit。43 组 axiom 输出仅含 `propext`、`Classical.choice`、`Quot.sound` 的子集；6 项不依赖公理，没有 `sorryAx` 或非标准公理输出。各包历史记录中的 12/22 个执行检查不计入这 43 个 axiom 输出分母，也不由它们替换。

本包随附的 `lake-clean-build.log` 是 actual artifact ZIP 中该成员的二进制逐字节副本，不是摘录。Artifact ID `13107276983`，ZIP 699759 B，API digest `sha256:4cb1bd5192c000bc5e93bfaaa7d14f7978b3207daeede382e7b5cd821406dc06`；原始日志 5216301 B，SHA256 `663af0a0b4256d0d8c97b53c30a08f55fa878a33d587c433c558550afcf898bf`。verification 绑定所有 43 项的声明位置、Audit 的 `#check/#print` 行、日志实际行号和公理输出。

## SourceCompilation 的分开边界

`SourceCompilation20261027` 的 `extractView` 是另一项固定 snapshot/catalog 例子：它要求唯一匹配 `InterpretationRow.material=s` 与 branch，再执行引用/版本和有限 payload 检查；`extracted_view_is_exact_selected_payload` 证明输出就是该 snapshot 与被选中行。它没有构造上述 μ，也不证明 primitive source meaning。其 Audit 的合成例甚至展示：替换付款解释后，extractor 仍可因 catalog 单行且检查通过而返回 known，但单独给定的 `primitivePaymentMeaning` 为 false。故 snapshot/catalog 的绑定与 μ 的同对象解释、材料真值、现实来源真实性是不同证据层；不把 SourceCompilation 作为本包 μ 定理。

## U00 消费边边界与建议增量

U00 既有十五边表中，旧快照边 1“来源→表示”记录 Pipeline 调用与来源解释/actual-world mapping 前提；边 2“表示→编译”记录 facts/supportTable 分开的参数流。当前条件链表仍将边 1 的来源解释保留为外部前提，将边 2 的支持表/固定 φ 一致性保留为条件。07.1 的 μ/有限 identity 结果可作为数学 producer 说明，补充“在已给定 μ 的解析域和明确对象种类中，typed key 精确刻画 SameObject，并有有限非空例及错误识别反例”。它不生成现实 μ、不建立源真值或新增实际 caller，因此边 1/2 的 runtime 参数流与评级均不应变化。

SourceCompilation 的 selected snapshot/catalog 结果继续单列为证据绑定说明，不称为 μ 构造或 primitive truth proof。整份证明不把 sourceRef、字符串、裸 eventId、债项 ident、目录行唯一性本身升级为现实法律对象身份。

**候选处置：**本行数学映射为 `COVERED`；canonical 候选 C 待完整记录 PR 验收。原题 07、U00、105 工程要求和消费边均不因本包而整体关闭或升级。