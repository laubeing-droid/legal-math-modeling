# 原题 07.5：局部契约、共同纤维与共同对象

状态：本行映射为 COVERED；canonical 候选 C 待完整记录 PR 验收，验收前不视为 main 已关账。本包只整理冻结 L287 对“局部各有见证”与“共同见证”的区别，并映射已接受的六项定理；不增加新证明或新的模型前提。

## 冻结承诺与逻辑范围

冻结题单 `07_法律对象共同模型与表示.md` 的原题行范围是 L285–288，L287（U07.2）。其承诺要求区分 `∀ i, ∃ wᵢ`、`∃ family, ∀ i` 与单一共同见证；按投影相等构造纤维积

```text
W = { (w₁, w₂) | f₁(w₁) = f₂(w₂) }
```

并说明仅局部非空不能推出共同纤维非空。一个明确给定的共同基点 `b`，若每个局部纤维均含有满足相应局部契约的见证，则是非循环的充分条件。最后须把静态共同对象及其局部契约分别映射到已给模型，不将这个条件结论扩大成任意输入或现实来源真实性。冻结原稿字节/行范围仍由 canonical 保留；本轮未改原稿。

## 三种量词与纤维积

- `independent_local_witnesses_iff_tuple`（SourceStages L362）给出 `∀ i, ∃ w, P i w` 与依赖函数 `∃ ws : (i : I) → W i, ∀ i, P i (ws i)` 的等价。该结果只把逐项见证收成一个 family；它没有要求不同投影相同。
- 若要求同一 `base : B`，应使用纤维 `fᵢ⁻¹({base})`。`compatible_fibers_compose_local_contracts`（L369）以显式前提 `∀ i, ∃ w, projection i w = base ∧ P i w` 构造同一 family；不会由单独的 `∀ i, ∃ w, P i w` 推出该前提。
- `nonempty_local_models_can_have_empty_common_fiber`（L377）是精确反例：两个 `Unit` 局部域都非空，但常值投影分别为 0 和 1，因此共同纤维为空。它说明需要兼容条件，不声称这是现实案件数据。

## 冻结模型中的共同对象与 C1–C5

既有 `JointObject` 是 `SourceFrame × Nat`。`actual_source_has_joint_object` 的参数固定为 `background`、`material`、`branch`、`catalog` 及 `out`；仅当前置条件 `sourceModel background material branch catalog = .ok out` 成立时，定理才给出 `x : JointObject`，使 `suppliedLayers out = jointLayers background x` 且 `JointContract background material branch catalog x`。这不是任意层的兼容定理。

`JointContract` 将同一 `x` 的实际抽取视图、两笔已绑定付款、金额与阶段构造、旧模型合同、事件/关系字段、固定背景字段以及阶段递进/守恒逐项连在一起。旧 `LegacyContracts` 恰由下列五个既有谓词组成；`fixed_background_preserves_exact_old_contracts` 证明对给定 `background, frame, n` 的 `modelOf background frame n` 保持该五项，并保留 `candidate`、`norms`、`weight`：

| `LegacyContracts` 组成项 | 实际谓词 |
|---|---|
| 1 | `UnifiedNonDegenerate` |
| 2 | `UnifiedInterpretationPreserved V RelationId model` |
| 3 | `UnifiedChainCorrespondence V RelationId model` |
| 4 | `UnifiedFiniteProcessComposition V RelationId model` |
| 5 | `UnifiedTimeAndUncertaintyPreserved V RelationId model` |

冻结标签的边界也按实际类型保留：C1 是不带 `M/c` 参数的全局项；C3 中固定的 `legalPay(10)` 不由 `M.candidate` 生成。上述五个 `LegacyContracts` 谓词是本次已有结果实际连接的五项旧合同，不把其类型名称强行等同于冻结标签。背景的 `candidate` 被原样保留；本结果没有新增 `M/c` 参数。`unified_legal_derivation_on_declared_fragment` 的泛型结果只提供其声明的五项合同，不能代替 `sourceModel = .ok out` 的前提，也不声称任意层都能装配。

## 六项实际输出映射

下列六个定理都来自已接受的 full-source build 日志。原始日志保持在 07.1 包共享文件中，本包不复制 5.2 MB 日志。行号指该 raw log 中目标声明/类型输出所在行及相邻 axioms 输出行；完整路径、来源 artifact 和每个目标的实际 axioms 见 `verification.json`。

| 目标 | 本题中的作用 | raw log 输出 / axioms 行 | 实际 axioms |
|---|---|---:|---|
| `SourceStages20261027.independent_local_witnesses_iff_tuple` | 局部见证与 family 的量词等价 | 19391 / 19393 | `Classical.choice` |
| `SourceStages20261027.compatible_fibers_compose_local_contracts` | 显式共同基点下合成局部契约 | 19394 / 19398 | `Classical.choice` |
| `SourceStages20261027.nonempty_local_models_can_have_empty_common_fiber` | 局部非空但共同纤维为空的反例 | 19399 / 19401 | `propext`, `Quot.sound` |
| `U07_2JointObject20261029.actual_source_has_joint_object` | 成功 `.ok out` 条件下的静态共同对象 | 19113 / 19126 | `propext`, `Classical.choice`, `Quot.sound` |
| `SourceStages20261027.fixed_background_preserves_exact_old_contracts` | C1–C5 与固定背景字段的保持 | 19403 / 19411 | `propext`, `Classical.choice`, `Quot.sound` |
| `Seams.unified_legal_derivation_on_declared_fragment` | 声明片段上的五项旧合同 | 19188 / 19195 | `propext`, `Classical.choice`, `Quot.sound` |

此次重用的实际 full-source run 为 `41364107892:1`、job `125020511901`，成功；API head 是 feature `9de1037a28c7e201b994889bf2bc1bf0faab1e50`，日志所绑定的 merge subject/tree 是 `223bf1529e1f11d05187b2f3723d4552d83befcd` / `31c197b7819c48146b93f0abfa549399c9fd31eb`。这是一份已接受 source build 的历史证据重用，不是本轮新 dispatch。

## 边界

`JointObject` 的构造条件依赖固定背景、材料、分支、目录，以及 `sourceModel` 成功返回 `.ok out`。这些证明不认定目录真实、输入来源忠实或法律结论正确，不推出任意模型层全局兼容，不改变旧 Pipeline 的调用关系。C1–C5 仅按上述具名类型保留。canonical 仍是候选 C，完整记录 PR 接受前不宣称 main 已关闭本行。