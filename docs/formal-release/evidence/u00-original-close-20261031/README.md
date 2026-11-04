# U00 条件合成：独立来源与消费路径核验

19个具名源模块目标已通过独立 changed-module CI。本包覆盖冻结总稿 §13 的条件命题，与49项已接受证据共同构成 U00 闭口依据。当前整合树的全链门、证书与合并由本轮 PR 另行验证；本包本身不声称这些整合验收已完成，也不声称整个97题、105工程、六切口或冻结理论完成。scope-archive.json 中的 remaining_obligations 原文保存在 original_residuals，作为2026-10-27历史快照；当前残余按冻结总稿 L734–748、新19目标与49项既关证据解释，不续挂已由此覆盖的旧泛化残余。

## 同树来源审计

Subject eba3880d57f9da974508123e7cc6fc689db5ebe5, tree 4461be332c3f271a2f0b0cc4343e2b10cd064d1e; run 41178784116, attempt 1, job 124471736816 succeeded. Artifact changed-module-only-41178784116-1, ID 13034126936, ZIP 16,252 bytes, SHA-256 fc88ae769f2ea1d2519a0a6a407e99527c9532d451a29c96decccdd1b3dd8241; both ZIP members and all 14 source pins are recorded in verification.json.

The exact driver raw contains 19 #check/#print axioms theorem pairs and three object checks (41 output blocks; 65,256 bytes; SHA-256 dc410e21a278d8d00a377e5508b7179e11ae02de77fd73358f597db2adb3e5cf). Seventeen targets depend only on the standard propext, Classical.choice, and Quot.sound axioms; sample_packet_reads_actual_column depends only on propext; sampled_request_reads_actual_blocks has no axioms. No target has sorryAx, a nonstandard axiom, or a conflicting target line. The driver binds actual selected-source validation and current rule input, actual sample packet/blocks, actual round activation/post, personal continuation, actual measurement/log, and actual assessment/next action.

## Frozen conditional contract and evidence composition

The archived U00 row is not read as a permanent assertion that no later proof may complete any named subclaim. The frozen §13 requires one conditional composition under compatible same-case Γ/S, a nonempty shared interface, named layer premises, and actual outputs consumed by the next stage. Deterministic edges reuse U10.2 finite induction; representation/source edges reuse U07/U03 exchange results; statistical statements stay inside declared joint validation law Q_Γ, retain marginal guarantees, and do not assign probabilities to legal branches λ. This package supplies the actual finite path for source selection/failure retention, protocol evaluation, measurements, payment/refresh and eventual native assessment/next action; the 49 earlier proof/wiring admissions remain the accepted main baseline.

每个原 legal interpretation、actual world、source fidelity、applicability、fixed φ 以及 scope 合同均是具名外部前提。对统计合成，固定可见过去 h 与当前 Γ；在 Q_Γ 对可测且正质量的历史单元条件化后，各流分别满足既有 U14/U15 与 HarnessRisk 定理列明的可测性、iIndepFun、IdentDistrib、有界损失、正样本量和预声明族前提。时钟、版本、回执、同一标识或状态位都不推出采样律；不假设跨流或跨轮独立。

有限预声明实验集 T 覆盖所有声称实验，并由外部配置 Σ_{t∈T}(protocol.failureBudget_t+plan.failureBudget_t)≤Δ_joint；这里 protocol.failureBudget 与 plan.failureBudget 分别是既有协议失效预算和本轮 validation-plan 预算，c_t/v_t 仅为这两个输入的简写。多轮预算复用 `AdaptiveValidation.predictable_failure_budget`、`history_budget_is_expected_spend` 与既有有限/可和 HarnessRisk 结果；不在本轮新增预算定理。runtime `roundCost` 只求和 validation 实际 charges；其 limit 只限制实际 validation 收费，不是 joint cap Δ_joint。联合失败界要求上述独立预算配置，不从 roundCost 推出；可数形式依赖既有非负可和 δ 结果。

post 桥的精确等式是 `(finishAdaptiveRound ...).post.service = (activate ...).post`。另一个结果只把实际 `.known` chosen 投影传到较少 exposure 的 activation-service 投影；方向是单向的，不声称全部 state 字段相等。

## Explicit boundaries

The fifteen-edge table retains its 2026-10-27 Pipeline snapshot and now separately records current proven source→protocol→actual inputs→assessment/next-action evidence. This does not assert that the legacy Pipeline code was replaced, that every old consumer calls these declarations, or that real source truth, external legal authority, sampling-law validity, runtime deployment, unlimited RSI, or all engineering interfaces are proved. Global archive discharges, Step 2, and math_flip remain false.

## 2026-10-31 D3/D4 Python regression evidence (provisional)

- D3 missing/unknown standing rejects without writing a success output: `python -m unittest discover -s tools/unified_math_v2/tests -p test_run_v21_admission_20261031.py -v` — exit 0, 2 tests passed.
- D4 withdrawal resolves only the submitted evidence key, accepts `ev:<event_id>` and the raw event id, and rejects empty, unknown, or artifact references: `python -m pytest tools/unified_math_v2/tests/test_process.py -q` — exit 0, 29 passed and 5 subtests passed.
- The existing `unified-math-v2-reference.yml` workflow runs `python -B tools/ulm_consolidation/scripts/run_all.py --output work/consolidated-python`; that runner invokes `python -B tools/unified_math_v2/scripts/run_v21.py --output work/consolidated-python/v21`, whose `unittest` discovery covers `tools/unified_math_v2/tests`, including both touched test modules. Same-subject workflow verification is still pending; these local synthetic checks are provisional and make no Lean or legal-correctness claim.
