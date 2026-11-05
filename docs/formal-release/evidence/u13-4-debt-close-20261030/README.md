# U13.4 fallback selection and risk: OPEN 4 → 3

This package records the U13.4 close against the archived residual exactly as preserved in the pinned scope archive: “Absent personal/population/prior/retrieval branching present; validate distinct provenance/scope policies for the fallback sources and nonidentification witnesses.” The evidence is bound to source `ad4beec80456a8562a4c2a0dbf231000fb922e8d`, run `40976943681`, job `123807204758`, attempt 1. The changed-module artifact is `changed-module-only-40976943681-1`, artifact ID `12943003053`, 6709 bytes, SHA-256 `c2fa2f1e56fa4ee308883e63862cda2af7307f5acaa0aa78fa209fe94c02b1ff`. The ZIP contains `changed-module.log` and `module-plan.json`; `axiom-audit.raw.txt` is a targeted extraction from the actual log, not a native ZIP member.

The audit checks 19 proof targets and 23 public objects. Sixteen proofs use `[propext, Classical.choice, Quot.sound]`; `prior_success_is_declared` and the reused missing-checkpoint theorem use `[propext, Quot.sound]`; the reused `u13_1_noninterference` theorem reports no axioms. No target has `sorryAx`, a nonstandard axiom, or conflicting output. The source inventory contains the two U13.4 modules, four directly reused proof modules, and the U13.3 audit driver used for its historical empty-sample example. Full paths and byte hashes are in `verification.json`.

The audited fallback branch reads its actual fitted table, calibration result, applicability input and optional personal checkpoint under the existing sample, law, iid, measurability, loss and radius premises. Its conclusion is a conditional population-risk bound, not a per-case win-rate guarantee. The sampled branch reads checked mature measurement rows and labels and returns their equal-weight sample mean, with its error bound under the stated same-law and iid conditions. Declared priors remain separate model inputs. Missing or invalid source attempts return named `UNKNOWN`; the normative partial function remains separate. Source references and applicability inputs do not prove source authenticity, physical applicability, or iid sampling.

The previous U13.3 audit driver contains an anonymous empty-sample instance of the accepted two-world nonidentification theorem. That source-built example is cited as historical reuse (`audited_target: false`), not as one of this run's printed targets. Five earlier U13.4 failed runs are retained in `verification.json` as diagnostic history only; none is proof evidence.

This closes only the U13.4 archive residual. It does not establish an RSI-wide improvement theorem, change original-question 13.4, close original-question 13.5, or connect the old Pipeline/consumer. Original-question 13.3 is updated using this fallback evidence together with the earlier U13.3 receipt; the broader U13.4 original-question row remains as recorded. Global manuscript discharges, math flip, Step 2 and the frozen tip pin remain unchanged.

## 原题 13.5 域外回退与可信服务边界 · 2026-11-06

冻结题单 L119、L121 与补正 S13 L222 分别规定作用域判据、域外非识别和三种服务结果。下文 `F` 指 `JurisLean.Candidates.U13_4ColdStartFallback20261030`。

### L119 有限判据和非识别

令查询 x 为 `q.point : Fin m`，声明域 s 为 `q.request.scope`，个人 θ 为可选 checkpoint，D 为 `ModelSource` 中实际送审的校准记录及其拟合表、损失、候选 cutoff 和误差半径。查询协议、风险阈值及外部适用性输入随 q 和 source 保留。对实际校准预测，`InScope(x,s,θ,D)` 取下列可检查的准入合同。

1. 查询点与声明域相符。`F.basisMatches` 检查任务、目标、特征、规则版本、机制、scope、查询点、母体及显式适用状态。`F.queryCompatible` 将学习协议的任务、目标、特征版本和有效域与查询相联。有个人 checkpoint 时，`F.auditedReady` 还要求 checkpoint 匹配和版本相等。
2. 以实际 D 运行 `F.auditProduction`，从给定拟合表、损失、候选 cutoff、样本和半径检查产生校准证书。查询要求实际表值通过选定 cutoff，表宽、协议、证书与实际表一致，并通过 `consumeCalibration` 的支持和风险界检查，实际要求已给支持标志、0<lowerCoverage 及 0≤upperRisk≤q.riskLimit。有个人 checkpoint 时，返回值还须与其 prediction 一致，数值须落在 [0,1]。`F.audited_success_reads_actual_inputs` 绑定这些计算所消费的原对象。
3. 字段和版本匹配、是否通过已选 cutoff、证书与实际输入一致性都能有限检查。cutoff 和经验风险/覆盖率由实际样本计算，概率界仍以相应采样律、同分布、独立性、损失和半径条件为前提。声明的 applicability 与来源真实性由独立依据承担。若另问某点是否曾在 D 中出现，可逐项比较有限记录的 feature 得到可检的出现标记；样本未出现与真实母体支持不可等同。现有校准路径按声明域与所选规则核验，保留其实际合同。

直接复用 `JurisLean.Candidates.LearningBoundary20261027.u01_3_two_worlds_same_training_uncontrolled_deployment`。两个世界的训练输入都只有 false 点且标签都为 false，未见点 true 的标签分布分别集中在 false 和 true。仅依赖相同训练数据的确定性学习器在该点给出同一预测，至少一个世界在该域外点的损失为 1。因此这些训练输入无法唯一识别域外标签分布。原论证采用有限确定性学习器和给定损失。

### L121 规范、描述、预测的分支合同

| 服务 | 实际输入、输出与证据 |
|---|---|
| 规范 | 固定 N 所给的规则函数为 G_N，代入 `F.normativeService` 的 G。 `F.normative_query_uses_only_G` 证明规范字段由 G_N 和其规范查询输入决定。补正的 2×3 同单位示例给 6。已有 `F.original_fee_service_example` 用另一个给定 G 返回规范金额 120，同时预测为 `unknown .missingEvidence`。 |
| 描述 | `F.descriptionService` 检查声明母体、查询范围、版本、观测时点及实际 measurement/label 对应，并对有效数据计算等权频率。`F.description_success_reads_measurements` 把输出的 `Description.input` 与实际 `DataSource` 绑定，其中保留母体、作用域、来源、采样/测量引用及实际记录。频率按该来源解释。 |
| 预测 | `F.sourceAttempts` 按个人校准、人口校准、显式先验、样本候选的顺序实际求值。 `F.selected_prediction_has_executed_source` 绑定选中的实际成功分支。校准预测按前述判据核验。样本预测另核实际描述和 `radiusVerified`，其概率误差定理仍要求正样本量、可测、合法 δ 和独立同分布等明示条件。先验成功保留 `declaredPrior` 类型及给定的概率、适用域、来源和条件字段，按声明的模型条件解释。 |

每个经验来源的范围、支持与误差检查分别判定。底层失败可为 `scopeMismatch`、`targetMismatch`、`unsupported`、`notIdentified` 或 `missingEvidence`，各理由按其发生层区分。`auditedPrediction` 将校准生产或消费的未成功结果归为 `missingEvidence`，`samplePrediction` 将描述未成功也归为 `missingEvidence`。某来源失败时依次尝试其余来源，四种都无 known 才由 `F.no_valid_source_unknown` 得预测总出口 `unknown .missingEvidence`。最外层保留的是这个总理由。已有 `SampleCalibrationConsumer20261027.query_outside_selected_rule_refused` 提供选定 cutoff 域外的直接拒绝。

`F.audited_prediction_risk_under_existing_conditions` 是实际校准输出的选择风险界，`F.sample_prediction_error_under_existing_conditions` 是实际等权均值的误差界。两者依赖各自明确的概率前提。描述频率、带条件的先验概率、有限样本均值和带校准条件的总体风险各有原类型和解释范围。预测出口未知时，规范字段仍按固定 G_N 的输入独立求值。

本次归引沿用 U13.4 的既有 19 目标源回执和已接受的 Authority 类型输出。原回退源码、实际消费者和外部证据条件沿原合同验收。
