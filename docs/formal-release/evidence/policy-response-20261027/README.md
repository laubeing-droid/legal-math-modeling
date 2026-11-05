# Strategic response, exact damping and legal information boundaries

Original 12.1, 12.2 and the information boundary of 12.6 / S12 are proved for their stated models. Every threshold in (0,1] gives the original three net utilities 0,.4,.9; gaming is the unique maximizing response. A rule reading only the score cannot distinguish equal-score effort and gaming even though their true outcomes differ.

The shifted logit calculation is proved equal to the original softmax of those actual utilities and is a positive normalized distribution. Its actual finite expected outcome and score are computed. At beta=0 they are 1/3 and 2/3; as real beta tends to infinity, the true outcome tends to 0 while the score tends to 1. These are model implications, not a verified behavioral law.

The same algebraic affine implementation supports exact rational execution and the original real-domain theorems. Its n-step formula holds for arbitrary n and initial state. The two original maps have the same unique fixed point 1/2. The reflection map has no limit from any noncentral real initial state. Damping preserves [0,1] when the rate lies there and converges to the original fixed point from every initial state in [0,1] exactly when 0<rate<1. This excludes both zero-step stasis and the undamped reflection endpoint. Local affine behavior can coexist with two distinct global fixed points; a globally stable center can lie outside an independently given legal interval. Identical behavioral data cannot recover two different admissible-policy sets.

Independent [run 40451401604](https://github.com/laubeing-droid/legal-math-modeling/actions/runs/40451401604), [job 122014729609](https://github.com/laubeing-droid/legal-math-modeling/actions/runs/40451401604/job/122014729609), succeeded on `c77fd50a8e6c0b937b0315ea1a6647387d7ba561`: 17 exact type/axiom targets and 7 guarded executions, standard axioms only, both LF-normalized sources bound. The real logit/limit results are kernel theorems, not Float approximations; the guarded executions exercise exact rational utility and trajectories. Raw 34 type/axiom message blocks are retained. The first subject `ff43e3c7f33ba32535d8f7f74a3db3670983feae`, [run 40451010939](https://github.com/laubeing-droid/legal-math-modeling/actions/runs/40451010939), failed Fin-numeral reductions and real-limit elaboration. Its unchanged claims were repaired with explicit finite indices, real constants and noncomputable real comparison; it is not PASS evidence.

G-PROPOSED correspondence (baseline 825792b83476a767152396d7f5e2ba3017048841): the namespace/source is NEW. The pinned Mathlib exponential and geometric-limit theorems are reused, with the original utility table, actual expectations, iteration and boundary cases supplied here. Frozen Policy's general contraction and signal/incentive statements remain unchanged.

| Symbol | Original obligation | Actual consumer/check |
|---|---|---|
| preparationUtility / finite_response_payoffs | 12.1 finite responses and score information | both original thresholds and exact response ranking |
| logitPreparation / logitQuality / logitScore | 12.1 finite rationality | original-softmax equivalence, normalization, actual expectations and limits |
| affineResponse / affine_iterate_formula | 12.2 actual n-step response | full real-domain convergence and exact rational executions |
| damping_converges_for_all_iff | 12.2 all rates and all initial states | sharp open-interval criterion, stasis/oscillation endpoints |
| local_affine_behavior_does_not_give_global_contraction | 12.2 local versus global claim | explicit distinct fixed points despite the specified local behavior |
| behavior_only_cannot_recover_admissible_sets | 12.6 separate normative basis | arbitrary data-only algorithm, identical observations and incompatible allowed sets |

This is not yet the finite admissible-policy suggestion implementation or business/measurement/policy/RSI consumer. Those and U00 remain separate. Root integration follows independent success; full PR/main acceptance is separate. OPEN=20, closes_debt=false, CAND8=8 outside PROVE_CANDIDATES; no discharges/frozen-pin/workflow/toolchain changes or local Lean/Lake/Elan.


## 原题 12.1 与 12.2 逐段归引 · 2026-11-06

以下 `P` 指 `JurisLean.Candidates.PolicyResponse20261027`。有限响应、实数 softmax 和仿射动力学复用上面独立模块的实际输出，以及 PR46 与合后 main 的既有验收。二元审计复用 `U12_4FrozenAuditModel20261029.frozen_audit_model_acceptance` 的既有模块与 PR64 验收。两条模块源码的绑定分别见 [policy-response 原始回执](verification.json) 和 [U12.4 原始回执](../u12-4-debt-close-20261029/verification.json)。

### 12.1 L95、L97–100、L102

题给 `Fin 3` 的三个行为依次为不投入、真实准备和形式性迎合。真实结果衡量题给窗口内的准备完成度。`P.finite_response_payoffs` 在有理阈值 `0 < θ ≤ 1` 给出下表，并证明行为 2 严格优于另外两项。

| 行为 | 分数 | 准备完成度 | 成本 | θ = 1/2 净收益 | θ = 1 净收益 |
|---|---:|---:|---:|---:|---:|
| b₀ | 0 | 0 | 0 | 0 | 0 |
| b_E | 1 | 1 | 3/5 | 2/5 | 2/5 |
| b_G | 1 | 0 | 1/10 | 9/10 | 9/10 |

两阈值的唯一最优响应都为 b_G，准备完成度为 0。`P.score_only_cannot_distinguish_preparation` 给出 E/G 同分异质及有理值通过概率相等。对实值概率，`z(b_E)=z(b_G)=1` 同样由函数代入给出 `π(1)=π(1)`。只读 z 的规则在两种行为上面对同一输入，即使增加模型复杂度也是如此。

`P.logit_is_original_softmax`、`P.logit_is_probability`、`P.logit_actual_means`、`P.logit_zero_means`、`P.logit_high_rationality_limits` 给出实际效用的 softmax、正且归一的质量、两个期望及端点。Lean 定义取 θ=1/2。表中 θ=1 的收益逐项相等，故代入原 softmax 后权重和归一化分母逐项相等。β=0 时质量与分数期望分别为 1/3 和 2/3。β 趋于正无穷时分别趋 0 和 1。两端比较得到质量下降、分数上升，适用域为题给三行动候选行为模型。

L99 的最小额外观测取题给二元审计结果 V。在同一准备完成度定义、审计机制和观察窗口内，记录 V 及独立核实的 E/G 类别以确定条件分布。记 `pE=P(V=1|E)`、`pG=P(V=1|G)`。两类 z 恒为 1，故 `pE≠pG` 足以区分 `(z,V)` 的条件分布。个体在两类分布支持重叠时仍可能无法识别。题给完美审计 `pE=1,pG=0` 是有限可区分例。既有 `frozen_audit_model_acceptance` 在 `pE,pG∈[0,1]` 给出质量非负且归一、三项收益及 E 严格最优的条件 `pE−pG>1/2 ∧ pE>3/5`。`Final20261021.Policy.distinguishable_signal_insufficient` 的 `pE=3/5,pG=1/2` 实例区分了测量信息和激励效果。

L100 将根据合法公开程序要求如实准备材料列为允许的响应情形。实际授权、规则适用和行为性质由外部规范与事实判定。相同高分和不同准备完成度的例子说明分数只能作筛查观察，案件实体判断仍需独立的事实和法律依据。此有限收益表、信息不可区分结论和审计条件完成 L102 的数学交付。

### 12.2 L106、L108–111、L113

在闭区间 `[0,1]` 和度量 `d(x,y)=|x−y|` 上，`T₁(x)=1/4+x/2` 将区间映到 `[1/4,3/4]`，`T₂(x)=1−x` 将区间映回自身。`P.original_maps_and_unique_fixed_points` 给出共同唯一固定点 1/2。`P.affine_iterate_formula` 给出 `T₁ⁿ(x)=1/2+2⁻ⁿ(x−1/2)` 及 `T₂ⁿ(x)=1/2+(−1)ⁿ(x−1/2)`。`P.affine_converges_to_center` 和 `P.reflection_has_no_limit_except_center` 分别给出 T₁ 全初值收敛及 T₂ 的非中心振荡。

`P.damped_as_affine`、`P.damped_preserves_unit_interval` 给出 λ∈[0,1] 时的自映射及误差 `θₙ−1/2=(1−2λ)ⁿ(θ₀−1/2)`。`P.damping_converges_for_all_iff` 给出所有 θ₀∈[0,1] 趋向原共同固定点的完整参数集 `(0,1)`。只要求每条序列有极限时参数集为 `[0,1)`。λ=0 序列恒为初值，λ=1 除中心外振荡。两个收敛问题按冻结补正 S12 L208 分列。

一般收缩前提由 `Final20261021.Policy.u12_2_contraction_sufficient` 的非空完备度量空间和自映射上的 `ContractingWith` 给出。此处 `[0,1]` 在绝对距离下完备，实际仿射式给 T₁ 的常数 1/2 及阻尼映射的常数 `|1−2λ|`。`P.local_affine_behavior_does_not_give_global_contraction` 给出在 x≤1/2 时等于 x/2 的映射，且 0 和 1 都是固定点。两点距离仍为 1，无法满足全域常数小于 1 的距离界。局部导数、单次轨迹或损失下降都缺少全域成对距离的约束。

L111 取唯一特征点 x₀，政策 πθ 在 x₀ 选择动作 1 的概率为 θ，并报告数值预测 θ。`D_{πθ}` 是同一部署策略的单步数据分布，动作 0 和 1 的质量分别为 `1−θ` 和 θ，两点结果 Y 均为 1/2；θ∈[0,1] 保证非负且归一。平方损失为 `(1−θ)(θ−1/2)²+θ(θ−1/2)²=(θ−1/2)²`。新具名连接 `JurisLean.Candidates.PolicyPredictionBoundary20261106.accurate_stable_policy_can_be_outside_legal_constraint` 对这一个 loss 和同一个 `update(θ)=(θ+((1−θ)/2+θ/2))/2`，同时证明 θ*=1/2 的损失为零、update 的固定点等式、所有 θ₀∈[0,1] 迭代趋向 θ*、以及 θ*∉[0,1/4]。该 update 正是原更新 `T(θ)=(θ+E_{D_{πθ}}Y)/2=T₁(θ)`，证明复用 P 的仿射收敛反例，不另换政策或分布。允许域 [0,1/4] 独立外给，不从预测损失或部署数据推导。故同一有限分布实例同时准确、稳定并违反外部约束；这里只证明有限数学反例，不据此认定现实政策合法。

L113 分别登记存在、唯一、收敛和合法。给定 T₁/T₂ 均存在唯一中心。T₁ 从所有初值趋向中心，非中心初值的误差在每个有限步仍非零。T₂ 只有中心初值保持在中心。阻尼在 λ=1/2 时一步命中中心，其余参数按误差公式判断。合法性仍需外生约束核验。应用范围为题给有限响应和线性更新，真实制度的响应与授权需要各自的外部证据。

### 本次实际证据与接受边界

本追加是原题12.1/12.2数学归引，不改上文历史证据。12.1的阈值、实际softmax/β端点和信息区分复用 [PR46](https://github.com/laubeing-droid/legal-math-modeling/pull/46) 及原policy-response回执；二元审计复用 [PR64](https://github.com/laubeing-droid/legal-math-modeling/pull/64) 和U12.4回执，保留两包既有main接受及原source绑定，不重跑旧module CI、不改四个复用源文件。旧剩余中因果解释和支持缺口识别区间属于冻结L119/L121的12.3；该行既有证据与状态本批原样保留，不将其重新挂到12.1。

12.2 L111新增连接的独立 [changed-module run 42072666500](https://github.com/laubeing-droid/legal-math-modeling/actions/runs/42072666500)，attempt 1，job `127404500057` SUCCESS。source `7b5bc93414f8786f9baecebc8bb8a5709e32d88e` / tree `2be03c6df685a3170e468fe11a7998e7b441cac0` / parent S128 `6cf2c5bb83ba2c6b01ae3743f9be99891abaea2a`，源1482 bytes、37行、SHA `b2cebb05a2707ed2ee0f13d3ca828801cb902f77c8b76c9911a2b320043940b5`、blob `bc78e3320b2f2a697f9050beed03e041909c80c7`。1 own / 0 reuse / 1 check–axiom pair、2条实际消息，0 errors / 0 sorryAx，实际公理为[propext, Classical.choice, Quot.sound]。这不是其他既有命题的新编译或完整PR通过。

官方 Artifact `changed-module-only-42072666500-1`, ID `13437615683`，ZIP 1037 bytes，SHA `25dbd503d9bbf13e5a9453b9249e3f0484e20780313b569755ae8c3aa56fb98f`；原字节raw及[本轮verification](original12-1-2-close-20261106/verification.json)位于dated子目录。module-plan.json为271 bytes，SHA `a54b734c463ad7d9ca9cd42e614fd270da202b1b9a17daaf464b9f36fe56c5d7`；changed-module.log为1618 bytes，SHA `6bb54f2c7b30ac3f872089d6bd619ef05c1fba0cbc1a66e82fc80fdbe1237337`。旧目录的raw及verification原样保留。

source成功后root checkpoint `56e0a0ee2860423c1cf30f591faaf86b03d69c1a` / tree `858a766ae51511915a6fb281bcfedc30371a5a58`，parent为source CP，仅新增root import，root blob `df7b506084f73ccd1a22268ad25b08fe8134b4ce`。AA writer唯一执行exit0且Git内容不变，无额外AA checkpoint；manifest实际绑定此clean root checkpoint，595 files / 0 diverging。source、root/manifest与未来records H/M分别标识，不把root当独立source CI subject。

本批只将12.1与12.2候选登记为COVERED，数学计数80/13/4→82/11/4；其他95数学行、105工程行、6cuts不变。没有新增实际消费者，现行U00 edges11/12的caller、历史、评级及消费文件不改；U50仍50 wiring/0 narrow/0 open/124 bindings，discharges、Step 2、math_flip均false。上文OPEN=20等属于当时记录，不作为当前全局计数。给定行为模型、独立审计机制、外部允许域与实际法律依据保持各自边界；不宣称部署、全局行为规律或原模型之外的政策合法性。

本地记录与索引验收：7 项 derived writers 各一次完成（AA无Git内容变化，其余六项接续），12 项 required checks 均 exit 0，受影响稿件回归为 2 passed in 0.94s；CI index 为 617 runs / 1500 quotes，index tests 为 12 passed in 5.37s，标准 --check exit 0。旧 616 条 metadata 保留，仅新增本轮成功的一条source run；实际 staging、full/authored diffcheck 结果见 `D:/tmp/original12-1-2-records-20261106/index-stage-r1-receipt.json`，不把非零full check解释为PASS。完整PR接受仍待完成。

