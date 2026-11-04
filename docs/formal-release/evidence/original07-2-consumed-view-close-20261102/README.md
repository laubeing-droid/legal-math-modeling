# 原题 07.2：有限消费视图与实际读取

状态：记录草稿，供独立审阅。本行数学映射为 `COVERED`；canonical 候选 C 待完整记录 PR 验收，完整验收前不视作 main 已关账。本轮是对已编译源和既有反例的有限映射说明，不新增 Lean 定理、抽取器或来源语义。

## 冻结承诺与范围

冻结题单 `07_法律对象共同模型与表示.md` L275 要求有限 `view(c)` 覆盖当前实际消费的债项完整记录、付款行、事件解释、来源引用、顺序、观察对象与必要单位；给出 `Extracts(E,V)` 或显式提取函数；把真实性、提取忠实性、内部一致性的责任分别说明；提供 record 不变而视图变化的反例；并限定为“本题观察族”的完整性。题单同时排除覆盖所有潜在事实、把最终法律正确性藏进提取函数，以及声称固定模板下任意篡改仍会通过精确比较。

本记录固定一组已有调用参数 β：材料快照 `s : MaterialSnapshot`、分支 `b : Nat`、有限目录 `K : List InterpretationRow`；来源模型调用再固定 `background`；付款绑定/两笔阶段调用固定 history index 1、2；若纳入有限编译读取，则固定 `rules`、`ruleGate`、`nodes`、`root`、`query`；解释读取再固定其显式读者/语义参数（下表）。这些额外参数不是由 `extractView` 自动生成的，也不因视图相等而成为来源真值证明。

本次有限观察族记为 𝔽₀₇.₂：两个既有 `ExtractedView` 上下文投影（材料、分支）、以下九个 `decoded : ConsumedView` 字段投影，以及下表明确列出的 source/binding 派生读取。对固定 β，若 `extractView s b K = .known out`，已有 `extracted_view_is_exact_selected_payload` 给出 `out.material=s`、`out.branch=b`、`viewChecks s out.decoded=true`，并存在唯一匹配行 `row` 满足 `row.decoded=out.decoded`。因此上下文两投影由前两等式相等；任意列明的载荷投影 `f` 由 `congrArg f row.decoded_eq` 相等。这里不声称 Lean 已定义或证明通用 `ObservationAdequate` 实例，也不把 `Gamma.observationFamily : Nat` 擅自解释成 𝔽₀₇.₂。

## 两个上下文投影与九个完整载荷投影

|读取|实际载荷/读取函数|相关定义|所保留的内容|
|---|---|---|---|
|ExtractedView.material|`out.material`|`ExtractedView` L108–111|固定材料快照；成功提取定理给出 `out.material=s`。|
|`ExtractedView.branch`|`out.branch`|`ExtractedView` L108–111|固定分支；成功提取定理给出 `out.branch=b`。|
|record|`out.decoded.record`|`ConsumedView` L69–70|完整引用的 `CaseRecord`，不是只按 key 重建|
|relations|`out.decoded.relations`|L71|有序的完整引用关系记录|
|ledger|`out.decoded.ledger`|`FullDebt` L50–54；`ConsumedView` L72|有序债项及 item、关系、obligor、`AmountTag`|
|payments|`out.decoded.payments`|`FullPayment` L56–60；`ConsumedView` L73|有序付款行、key、目标债项和完整 `PaymentPayload`|
|initialHistory|`out.decoded.initialHistory`|`SourceHistory` L62–65；`ConsumedView` L74|初始来源/关系或支付事件历史及其引用|
|historyEvents|`out.decoded.historyEvents`|`ConsumedView` L75|有序 formation/payment 事件历史|
|objects|`out.decoded.objects`|`ConsumedView` L76|引用到 `LegalObject` 的有序映射|
|observed|`out.decoded.observed`|`ConsumedView` L77|被观察来源引用及其 `RelationId`|
|atoms|`out.decoded.atoms`|`ConsumedView` L78|有序引用的输入原子|

## 固定 β 下的派生读取

|读取族|实际代码/前提|由精确载荷映射能说明什么|
|---|---|---|
|引用与上下文版本|`citations`、`citationPresent`、`viewChecks`（SourceCompilation L80–101）|按 `ConsumedView` 中各字段的原顺序枚举引用；检查 parse/unit version 与快照一致、引用的 source/position 存在、observed ref 解析为所述 relation，以及付款 case/revision/source 与快照/引用相符。|
|记录读数|`recordOf`、`actual_record_observations`（L155–162）|同一载荷给出 record 的 key、claimedAmount、registered 读数。|
|指定付款和历史顺序|`candidatePayment view index`、`bindPayment`、`BindingChecks`（SourceStages L70–107）|本次固定 index 1、2；选择使用 history list index，并检查付款/债项/关系键唯一、history/payment key 与 source 对齐，以及付款方、收款方、关系、金额、单位、日期和版本的一致条件。|
|两付款顺序与阶段|`SourceFrame`、`frameFromBindings`、`accepted_view_binds_both_actual_payments`、`public_consumer_reads_actual_extraction`（SourceStages L253–320）|固定消费的是 history 中 formation 后的两笔支付；后续状态按前一阶段输出继续计算。证明只对应这些函数的实际序列。|
|条件语义解释|`PayloadInterpretation`、`actual_record_and_binding_interpretation`（U07_3 L82–111）|固定 `objectMeaning`、`paymentMeaning` 与 `catalogInterpreted`；且 `sourceModel background s b K` 已接受时，得到所选行的条件解释结果。它不建立这些解释函数对真实来源忠实。|

|量与来源桥|`static_source_semantic_and_quantity_bridge`（SourceStages L509–522）|要把 observed relation 读为 `mu` 中对象，必须提供 `resolveFaithful`；该定理另保留 record key、实际第二阶段支付和数量编码。它不构造 `mu`，也不证明 `resolveFaithful`。|
|有限编译的 source 投影|`compileView`、`compiler_reads_actual_extracted_output`（SourceCompilation L193–242）|固定 `rules`、`ruleGate`、`nodes`、`root/query` 时，已证编译结果保留其实际 `ExtractedView` 输入。这里只把 source 投影纳入 𝔽₀₇.₂，不声称 query 为真。|

## 单位、顺序与外部责任

`AmountTag` 的字段是 `currency`、`unit`、`ruleVersion`；`Amount` 是有 tag 的有理值。`Gamma` 分别带 `normVersion`、`lawDate`、`observationFamily`，但不含 `AmountTag`。因此本次逐字段保留 `FullDebt.unit` 和付款 `amount.tag`，`BindingChecks` 要求二者相等，并检查付款 `normVersion`/`factDate` 与固定 `Gamma` 对应；citation 的 `unitVersion` 另与 `MaterialSnapshot.unitVersion` 对齐。这里没有汇率转换、跨单位等价或单位标签到外部法律含义的证明。

列表字段及 `MaterialSnapshot.fragments` 原序被完整选取载荷保留；付款选择明确使用 history index 1、2，阶段消费以前一阶段输出为输入。`citationPresent` 对 fragment 检查 source/position，不另证任意 sourceOrder 字段如何解释。对未列入该固定观察族的事实不作完整性声明。

来源真实性、reader 对原始材料的提取忠实性、解释目录对真实对象的忠实性和最终法律正确性都不由 `extractView` 建立。`interpreted_material_to_query` 将 `catalogFaithful`、`primitiveMeaning`、`rulesSound` 作为显式前提；`static_source_semantic_and_quantity_bridge` 将 `mu` 和 `resolveFaithful` 作为显式输入。`actual_source_has_joint_object` 也以 `sourceModel ... = .ok out` 为前提；不把该条件存在性提升为所有输入非空。缺少这些外部依据时，只能报告结构性选取/绑定结果，真实含义为 UNKNOWN。

## 反例与非空见证

`same_material_record_do_not_determine_semantics` 固定同一个材料快照和 `CaseRecord`，分别给出两个目录，使两个抽取各自成功但支付 payload 不同；合并两个目录后，抽取返回冲突。定理还给出外部 `objectMeaning`/`paymentMeaning`：一个视图满足该解释，另一个不满足，且其 observed relation 与给定 object meaning 不符。这是同一 record 不决定视图/语义的有限反例；它没有声称固定目录中任意篡改都能通过精确检查。

`nonempty_source_stage_fixture` 是独立合成非空见证：给定 `stageView` 可成功得到 `SourceFrame`。`actual_source_has_joint_object` 则是接受成功条件下的存在性结果。两者都不是无条件的真实来源存在证明。

## 既有构建证据与边界

本包引用已接受的 Authority full clean build 原始 artifact。实际 artifact member 的 Dtmp 来源路径保留于 verification；仓库不重复保存 5.2 MB 文件，字节相同的既有跟踪副本为 [`lake-clean-build.log`](../original07-1-source-identity-close-20261102/lake-clean-build.log)。该副本为 run `41364107892:1`，job `125020511901`，API head `9de1037a28c7e201b994889bf2bc1bf0faab1e50`，合并测试 subject `223bf1529e1f11d05187b2f3723d4552d83befcd`，tree `31c197b7819c48146b93f0abfa549399c9fd31eb`，父序 `[10049e40f3a73dda559ad3b0b0d97f8f0b313371, 9de1037a28c7e201b994889bf2bc1bf0faab1e50]`。Artifact ID `13107276983` 的 ZIP 为 699,759 B / SHA256 `4cb1bd5192c000bc5e93bfaaa7d14f7978b3207daeede382e7b5cd821406dc06`；其中 `lake-clean-build.log` 为 5,216,301 B / SHA256 `663af0a0b4256d0d8c97b53c30a08f55fa878a33d587c433c558550afcf898bf`。Dtmp 保留实际 artifact/member 来源；`artifact.package_copy` 引用已跟踪的 07.1 共享日志，本包未另复制 raw log。

下列 12 个目标是本包选取的实际输出子集，不是全构建目标数：4 个 SourceCompilation 目标、5 个 SourceStages 目标、1 个 U07.2 joint-object 目标、2 个 U07.3 固定绑定/语义反例目标。SourceCompilation 的独立既有 9-target 证据和 U07.1 的 43-target 映射各自保留原分母；本表不以 12 或 43 声称完成全部 07.2 / U00。

本包不改变 canonical 状态或两条既有证据对象，且不关闭其他 07 义务。07.2 仍待独立审阅本有限观察族映射及完整记录 PR 接受；没有声称覆盖未定义的 observationFamily 语义、所有现实来源或最终法律结论。