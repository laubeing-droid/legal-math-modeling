# 原题 07.4：往返、观察保持、语义反映与表示充分性

状态：本行数学映射为 COVERED；canonical 候选 C 待完整记录 PR 验收，完整验收前不视为 main 已关账。本包在原题 L283 的泛型定理基础上，给出一组实际账本历史观察和一个有限反例；不声称选择了现实编码，也不声称生产编码已满足观察充分性。

## 冻结承诺与已有泛型结果

冻结题单《07_法律对象共同模型与表示》L281–284 的原句（L283）为：“证明 d∘e=id_R 推出 e 单射，但不自动推出满射或 e∘d=id_M。给最小反例。设观察族 O 包含实际需要的对象身份、逐笔分配、阶段余额等，定义相对 O 的表示充分性及其与 O 分离点性质的关系。仅观察最终余额时，可有不同付款历史都到 0；由此说明何时只能得到观察等价而非对象相等。分别处理保持方向与反映方向。完成于清楚的交换图、定理和删掉关键观察后的反例，不将记录往返夸大为现实真实性。” 冻结文件为 32,221 B，SHA-256 `1bf38abdd67bbacde464bc47814a672220a223d4a553f3cebf8812b066b3458a`；本包未改冻结文件或原题行范围（L281–284，U07.1）。

复用已存在的 `SourceRepresentation20261027` 结果：若表示 `e : R → M` 保持所声明观察；若观察族分离 R 中对象，则结合保持性可推出 e 单射。旧定理的方向分别是观察保持 `e a = e b → read_o a = read_o b` 和分离 `((∀ o, read_o a = read_o b) → a = b)`；它们不把观察充分性或现实真值当作已证明前提。旧 `u07_1_retraction_injective`、`u07_1_section_surjective` 和 `u07_1_rho_idempotent` 仍各自按其显式 round-trip 前提陈述，不把单侧逆误写成双侧逆。

## 实际有限账本历史与观察族

新实例取 `ActualHistory := Ledger.Handle × List PaymentRequest`。`commitTrace` 顺序调用既有 `Ledger.commitPayment`，保留每步 `(Receipt, Handle)`；请求只作为此账本函数的输入，不由本实例赋予法律准入或现实执行效力。实际观察族 `ActualObservation` 恰有四项：

|观察|读取的数据|
|---|---|
|identity|初始 gamma、revision、debt relation / obligor / creditor；以及每笔回执的 typed key、完整 payload、固定 `μ(payload.source)` 的 `Option ObjectId`|
|allocations|每笔实际 `Receipt.allocated` 与该回执 payload amount 的原 `AmountTag`|
|stageBalances|初始 debt amount 及逐步 commit 后各 `Handle.state.debt.amount`，保留完整 `Amount` tag|
|terminalBalance|阶段余额列表的最后一项；历史构造确保该列表非空，没有默认零余额分支|

观察值通过 `Sum` 将身份数据、逐笔分配、阶段余额列表与终局金额分开。`μ` 是固定外部部分映射；`None` 只表示该次源标识未解析，不表示两个来源是同一对象。该族没有自动币种换算，也没有选择表示编码 `e`。`ObservationAdequate e (actualRead μ)` 是相对于此明确观察族的条件性质；本包不证明某一生产编码满足它。

```text
R  -- e -->  M                 保持：e(r₁)=e(r₂) ⇒ ∀o, readₒ(r₁)=readₒ(r₂)
^             |
| d           | ρ = e ∘ d
└── d∘e=id_R  └────────────── ρ∘ρ=ρ（由旧泛型结果）；不推出 ρ=id_M

readₒ : R → Vₒ      对象相等 ⇒ 观察相等；观察族分离时，观察相等 ⇒ 对象相等。
```

新有限见证 `unit_bool_retraction_not_reflection` 给出 `e : Unit → Bool` 恒为 `false`、`d : Bool → Unit` 恒为 `()`：`d ∘ e = id_Unit`，但 `e` 不满射，且 `e ∘ d ≠ id_Bool`。旧 `preservation_without_reflection` 的有限结论被实际复用来推出不满射；新定理直接证明双侧恒等失败。它不改变泛型定理的 R/M。

## 只观察终局余额的反例

沿用旧 `same_balance_does_not_identify_history`：金额历史域为 `List ℚ`，历史 `[10]` 与 `[4, 3, 3]` 的旧终局余额观察都为 0，但两条金额历史不相等。这里的列表是被观察的金额历史，不是本节 `commitTrace` 生成的支付交易轨迹。删去完整历史/身份/逐笔分配/阶段余额，只保留终局余额，就只能得到观察等价，不能据此推出对象相等。

## 本轮模块构建与实际审计输出

Changed-module run `41407568309:1`，job `125152967148`（`changed-modules`）成功；subject `b39268e1331b0afec4bd155b10a973a4ac636263`，tree `5eb8c124238abf99558e1380248e482af6e680b7`，branch `formal/close-original07-4-observation-instance-20261102`。Artifact `changed-module-only-41407568309-1`，ID `13123399277`，ZIP 2,291 B，SHA-256 `16c20daf5375d8b50e4bd53aaffd6c690a23f5c4f10f48ac4eb647d66e939885`。Module plan 只 include Audit 入口 `JurisLean.Candidates.Original07_4ObservationInstanceAudit20261102`，`removed_modules=[]`；实际 build 完成于 8,492/8,492 jobs。未见 `error:` 或 `sorryAx`。

下表列出 Audit 实际 `#print axioms` 的 11 项，不将 `ObservationAdequate ... : Prop` 这一 `#check` 当作声明/定理计数。Audit 还有两个泛型 theorem 的实例 `#check` 和其它选定 declaration 的 `#check`；这些 check 不增加 print 分母。

|实际 `#print axioms` 目标|Audit `#print` 行|原始日志行|实际公理|
|---|---:|---:|---|
|`SourceRepresentation20261027.adequate_representation_preserves_all_declared_observations`|21|108|[]|
|`SourceRepresentation20261027.adequate_separating_representation_is_injective`|22|109|[]|
|`SourceRepresentation20261027.resolved_identity_is_equivalence`|26|112|[]|
|`SourceRepresentation20261027.semantic_key_exact`|28|115|[Classical.choice]|
|`Final20261021.Representation.unknown_not_an_identity`|30|118|[]|
|`SourceRepresentation20261027.same_balance_does_not_identify_history`|32|123|[propext, Classical.choice, Quot.sound]|
|`SourceRepresentation20261027.preservation_without_reflection`|34|128|[propext, Quot.sound]|
|`Original07_4ObservationInstance20261102.unit_bool_retraction_not_reflection`|36|132|[propext, Quot.sound]|
|`Final20261021.Representation.u07_1_retraction_injective`|38|136|[]|
|`Final20261021.Representation.u07_1_section_surjective`|40|139|[]|
|`Final20261021.Representation.u07_1_rho_idempotent`|42|142|[]|

这些输出仅证明本次指定模块在所记录 Lean 工具链下构建并呈现上述定理/公理依赖；不证明运行时已采用这些观察，不证明真实来源真值，也不把本候选记录当作已合并关账。canonical 原有唯一 evidence 对象保持原值并追加本包记录；本行数学映射现登记为候选 C，完整记录 PR 验收前不视为 main 已关账。

## 原始字节与边界

本目录 `changed-module.log` 是从 artifact ZIP 成员逐字节复制。ZIP API digest 与下载文件大小及 SHA-256 一致；ZIP 解包成员的字节长度和 SHA-256 见同目录 `verification.json`。本包没有复制旧全量构建日志。旧行 [same_balance_does_not_identify_history](../original07-3-row-interpretation-close-20261102/README.md) 等仅作范围背景，本次输出计数只按本次 Audit 的实际日志定位。

此候选不证明现实来源真实性、生产观察编码的充分性，或运行 Pipeline 已接入 `ActualHistory` / `actualRead`。金额观察保留 `Amount` 标签，不隐含跨币种转换；记录往返不扩大为法律效力或现实真实性结论。