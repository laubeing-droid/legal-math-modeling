# U12.1原题答复：12.3历史政策评价与12.6行为学习的权限边界

本文对应冻结题单《12_行为响应反馈与政策学习.md》的原12.3第117–124行、原12.6第150–157行。下文的制度、时间、数据和模型均为题设或明示的合成对象，不据此断言现实中的因果条件或法律权限成立。

本包最终独立审计绑定 subject `1959afb04058afbff8495baea92ef6ac1687a577`、run `41004233670`、job `123895367398`、attempt 1、artifact `changed-module-only-41004233670-1`（ID `12954856579`，9,300 bytes，SHA-256 `0fa985ccbd5247a8bc53d2638d84a0e01256ad64b92470722e510821e5f873be`）。driver 实际审计 20 个 proof targets 及 7 个公开对象/instance checks；17 个 proof 依赖 `[propext, Classical.choice, Quot.sound]`，`feedback_reads_actual_external_label` 与 `performance_magnitude_is_actual_allocation` 依赖 `[propext, Quot.sound]`，`u13_1_noninterference` 不依赖公理。原 17 个目标先前已在 subject `0592802552669d5059d9b1014f73c275f58e99b4`、run `41003069558`、job `123891696536` 通过；本次在新增三个原题推论后重审全部 20 个目标。`axiom-audit.raw.txt` 是从实际 `changed-module.log` 摘取的 20 个 proof 类型及公理输出；ZIP 两个成员的原始大小和 SHA-256 记于 verification.json。正文区分纸面数学推导、具名 Lean 结果及其条件。完整权威全链与合并仍待完成。

Prior diagnostics are recorded only as history, not as acceptance evidence: run `41000829816` failed with ten proof-body elaboration errors in the earlier candidate; run `41002575698` compiled the source but its driver referenced `performance_magnitude_is_actual_allocation` under the wrong `MeasuredPolicy20261027` namespace instead of `BusinessMeasurement20261027`; run `41000801891` was a cancelled wrong-ref dispatch; never started; no jobs.

## 12.3（第117、119、124行）：从真实条件动作律到IPW

固定一个参与人响应机制、案件分布和处理版本。设实际单位空间为任意可测概率空间 `(Ω,P)`，基线协变量 `X:Ω→XSpace` 的值域为任意可测空间，动作集 `Act` 有限。对每个动作给定可测、可积的实值潜在结果 `Y(a)`；`A` 为实际动作，`Y` 为实际结果。目标政策满足 `π(a|x)≥0`、`Σ_a π(a|x)=1`，且各坐标可测。

使用实际变量而不是另造一个具有期望恒等式的日志模型，令

\[
T=(\{Y(a)\}_{a\in Act},A),\qquad
K(x,\cdot)=\operatorname{condDistrib}(T\mid X=x),\qquad
\mu(a\mid x)=K(x)\{(v,b):b=a\}.
\]

`K`是实际联合变量的条件律，满足 `P_X⊗K=Law_P(X,T)`。有限实值潜在结果向量与动作的结果空间为Standard Borel；这没有要求原Ω或XSpace为有限空间或Standard Borel空间。分母μ是这个条件律的动作边际。

识别需要以下各项，而不是仅靠权重代数：

1. **一致性与处理版本**：在所固定的干预含义、环境及暴露定义下，`Y=Y(A)`，P几乎处处成立。把不同通知内容等不同处理版本混成同一个动作，会破坏此项。
2. **条件可交换性**：对P_X几乎处处的x，潜在结果向量v与动作b在真实K(x)下独立。已独立验证的接口采用实际纤维上的 `IndepFun (fun z => z.1) (fun z => z.2) (K x)`，没有把欲证的加权均值相等当假设。该条件不是由预测精度验证的。
3. **目标支持**：对P_X几乎处处的x，`π(a|x)≠0`蕴含`μ(a|x)>0`。这里只要求目标实际使用的动作有支持，不要求统一正下界，也不要求零质量协变量点处的支持。
4. **同一目标总体与机制**：本式用日志的P_X评价同一冻结环境中的干预。若目标X分布不同，需要另有总体权重和相应迁移依据；不能仍把日志P_X的期望称为目标总体价值。
5. **实际结果与日志机制**：观测标签确实测量上述Y，日志分母确实是实际分配机制的条件概率。来源字段、文件存在、字段版本相同都不证明这两项。

定义冻结行为价值与评分为

\[
V_P(\pi)=E_P\!\left[\sum_a\pi(a\mid X)Y(a)\right],\qquad
S_\pi=\frac{\pi(A\mid X)}{\mu(A\mid X)}Y.
\]

先用一致性将S中的Y替换为Y(A)。对满足上述条件的x，令 `m_a(x)=∫v_a dK(x)`。真实条件独立给出

\[
\int 1\{b=a\}v_a\,dK(x)=\mu(a\mid x)m_a(x).
\]

因此，逐动作条件化并在有目标质量的格子上约去非零μ，得到

\[
\begin{aligned}
E_P[S_\pi]
&=\int\sum_a\frac{\pi(a\mid x)}{\mu(a\mid x)}
       \left(\int1\{b=a\}v_a\,dK(x)\right)dP_X(x)\\
&=\int\sum_a\pi(a\mid x)m_a(x)\,dP_X(x)\\
&=E_P\!\left[\sum_a\pi(a\mid X)Y(a)\right]=V_P(\pi).
\end{aligned}
\]

最后一步用真实条件律的分解／全期望；中间的消元才是纯代数。对无支持但π也为零的格子，不进行“除以零后约分”：该格的目标贡献为零，评分可明定为零。Lean中的实数除法在零分母处取零，这一总化约定本身不是识别依据。若π>0而μ=0，上述推导不能使用，评分的总化值也不能填补缺失的潜在结果均值。

这里没有把评分可积性偷放进前提。将同一纤维消元用于绝对值，并利用 `0≤π(a|x)≤1`，可得

\[
E_P|S_\pi|
=\int\sum_a\pi(a\mid x)E[|Y(a)|\mid X=x]dP_X(x)
\le\sum_aE_P|Y(a)|<\infty.
\]

同时 `E|Σ_aπ(a|X)Y(a)|≤Σ_aE|Y(a)|`。这使上述积分运算有依据，也说明无需统一逆概率上界来证明这一识别恒等式。有限类集中不等式另需加权观测有界，不能仅从这些L¹条件推出。

已独立验证的 `U12_1CausalPolicyBridge20261030.finite_action_causal_ipw` 对应这条一般有限动作、任意X／Ω、可积实值结果的推导。既有 `PolicyEvaluation20261027.finite_policy_ipw` 是有限有理核的代数恒等式，不能单独承担上述因果与测量含义。

实际二值测量实例采用 `MeasuredPolicy20261027.observationDatum` 和实际 `policyScore`。已独立验证的 `actual_measured_policy_causal_value` 要求：`consumeMeasurement` 实际成功返回该行；其标签的指示值几乎处处等于实际Y；一致性与真实K纤维独立成立；所填logging表几乎处处等于K的动作边际；目标覆盖成立。题给 `m_a(x)` 通过潜在结果的条件期望前提输入，再经全期望连接到有限 `policyValue`，没有假设观察均值与潜在均值已经相等。这个Bool消费者实例不替代前面的一般实值结论。

## 12.3（第117、119–120行）：数值、截断极限与偏差

题设两组各占1/2。条件均值及历史动作概率为：

| x | μ(1\|x) | m₀(x) | m₁(x) | π(1\|x) |
|---|---:|---:|---:|---:|
| 0 | 1/4 | 2/5 | 4/5 | 1 |
| 1 | 3/4 | 7/10 | 3/10 | 1 |

历史政策价值为

\[
V_P(\mu)=\tfrac12(\tfrac34\tfrac25+\tfrac14\tfrac45)
+\tfrac12(\tfrac14\tfrac7{10}+\tfrac34\tfrac3{10})=\tfrac9{20}=0.45.
\]

目标政策总选A=1，因此 `V_P(π)=(4/5+3/10)/2=11/20=0.55`。全部非零重要性权重只有：在 `(X,A)=(0,1)` 为4，在 `(1,1)` 为4/3；A=0时目标概率为零，权重为零。最大权重为4。若还要把加权结果本身界为[0,4]，另需结果Y确在[0,1]；仅给出四个均值不推出结果有界。

把权重截为 `min(w,2)` 后，iid且可积时该估计式的总体极限为其期望：

\[
E_\mu[\min(w,2)Y]
=\tfrac12\tfrac14\,2\,\tfrac45
+\tfrac12\tfrac34\,\tfrac43\,\tfrac3{10}
=\tfrac7{20}=0.35.
\]

故截断估计相对原目标的偏差为 `0.35−0.55=−0.20`；原价值减截断期望的损失为 `+0.20`。这些既有数值直接复用 `PolicyEvaluation20261027.original_policy_values_and_clipping`，不另造同义数值定理。

对非负w、c及Y∈[0,1]，点态恒等式给出 `wY−min(w,c)Y=(w−c)₊Y`。若完整加权结果可积，截断项和尾项也可积，故

\[
E[wY]-E[\min(w,c)Y]=E[(w-c)_+Y].
\]

既有 `U12_3MeasuredPolicyBridge20261030.clipped_weighted_expectation_exact` 已连接点态式与精确期望偏差。截断降低极值可以改善波动，却改变了被估计期望；围绕0.35得到更窄的置信区间，不等于对原目标0.55取得无偏保证。

## 12.3（第121行）：撤销无支持格的已知均值后，兼容范围为[0.15,0.65]

现在将 `μ(1|0)` 改为零，并按原题撤销 `m₁(0)` 已知这一条件。其他均值及X权重保持题设。记未知均值 `θ=E[Y(1)|X=0]`。Y∈[0,1]仅给出 `0≤θ≤1`，于是纸面计算为

\[
V_P(\pi)=\tfrac12\theta+\tfrac12\tfrac3{10}
=\tfrac12\theta+\tfrac3{20}\in[\tfrac3{20},\tfrac{13}{20}]=[0.15,0.65].
\]

两个达到端点的完整总体可明确构造：X仍各占1/2；X=0时A恒为0，Y(0)为均值0.4的Bernoulli变量；下端模型令未观察的Y(1)恒为0，上端模型令其恒为1。X=1时两模型使用同一个历史动作核，以及均值0.7、0.3的潜在结果机制，并令动作与潜在结果条件独立。两模型在所有实际可见格子的 `(X,A,Y)` 分布相同，却分别给出0.15与0.65。因此两端可达，上述区间不能仅凭日志缩窄。

既有 `PolicyEvaluation20261027.original_support_gap_sharp` 对有理u证明 `u/2+3/20` 及两界；`support_gap_endpoints_observationally_compatible` 证明0／1端点的相同 `bernoulliVisibleLaw` 及端点价值。新增短推论 `U12_1OriginalInstances20261030.original12_3_real_support_range` 精确刻画实数value能写成 `θ/2+3/20`、`0≤θ≤1`，当且仅当 `3/20≤value≤13/20`，已由 run `41004233670` / job `123895367398` 独立验证。该推论补足实数仿射区间的双向刻画，没有把旧有理数声明改写成一般实值总体定理；实际兼容总体与端点仍用上述构造及旧端点证明连接。若需要中间实数点的兼容总体，可令X=0的未观察Y(1)恒为θ；可见格子保持不变。

若反而继续把 `m₁(0)=0.8` 当作可靠的外部已知条件，价值仍为0.55；那是使用新增均值信息，并非零支持日志识别了该格。

## 12.3（第122、124行）：部署与缺失边界

上述0.55评价的是题设冻结案件分布、参与人响应、处理版本和单次动作后的结果。π部署若改变X分布，应以新的目标X权重重算，并说明为何分层潜在结果均值可迁移；若响应、干扰暴露或处理含义变化，连原来的m_a(x)也未必适用。这些单步数值不能不加说明地命名为长期制度效果。

分母必须是实际记录政策，或具有独立估计依据并另行计入估计误差的政策。仅观察最终动作，不等于知道动作生成机制。已独立验证的实际测量桥要求logging表与真实条件动作边际几乎处处匹配；它没有证明任意拟合的分母满足该匹配，也没有给出估计分母的免费无偏保证。

结果是否记录还需要另一条机制。若R为记录指示，观察报告须保留 `None`；不能把未记录结果编码为Y=0。若实际 `R⊥Y|X,A`、目标使用的格子上 `ρ(X,A)>0`，且ρ确为真实记录概率，则条件化有 `E[RY|X,A]=ρE[Y|X,A]`，由此联合权重 `π(A|X)RY/[μ(A|X)ρ(X,A)]` 才能接回已识别的政策价值。处理交换性、动作支持、记录独立与记录支持是不同条件。

旧 `U12_3MARSequential20261030.mar_reported_score_joint_weight` 与 `mar_visible_score_integral` 已提供真实Option报告、联合权重和实际可见PMF的有限有理模型实例；此处沿用旧证据说明边界，不把它们宣称为任意可积结果的一般MAR定理。若缺失依赖未观察结果、ρ未知或目标格无记录支持，应保留相应未知／兼容范围，不能以高预测置信度代替识别。

## 12.6（第150行）：限定允许集合的有限保守更新规则

固定合成制度J₀与时间t₀、处理及测量版本、同一目标总体。允许集合 `Π_adm(J₀,t₀)` 由独立规范依据给定；不能把“提高行为价值”当作允许集合的定义。明确行为目标 `V_B(h)=E[Σ_a h(a|X)Y(a)]`，Y使用预先固定的真实结果构念。有限候选类F、当前比较政策h₀和排序在评价样本前确定。

`C_B`在本答复中是统计不确定性说明：样本量n、固定类大小M、真实日志与目标支持、加权结果上界W、失败预算δ、同时误差半径r，以及iid／共同law／测量和识别前提。iid有界固定类时可取

\[
r\ge W\sqrt{\log(2M/\delta)/(2n)}.
\]

这个r控制采样误差，不消除无支持格的非识别、不证明交换性或外部记录真实性，也不覆盖部署迁移。若F是看同一评价数据后才筛出的，原固定类界不能原样套用。现有数值核验由 `policyNumericsValid` 与半径验证接口保留；元数据存在不等于这些概率前提已经成立。

本题构造的基础有限更新规则显式固定 `tol=0`，实际plan取 `plan.tolerance=0`；仅在 `F∩Π_adm` 中按已声明顺序找第一个满足

\[
\widehat V(h_0)+r-\mathrm{tol}\le\widehat V(h)-r
\]

的候选；没有这样的候选则不推荐。实际 `MeasuredPolicy20261027.choosePolicy` 执行这个 `find?` 规则，`selected_policy_reads_numeric_bounds_and_permission` 读出成功者属于family与allowed、父政策属于family以及实际数值门槛。它没有声称返回整个候选类的经验最优者。

这里的actual law连接必须明确。设实际单位law为Q，实际测量行是 `rows:Ω₀→PolicyObservation m`，令 `z=observationDatum∘rows`、`Pdatum=Q.map z`。评价样本应iid且各自与这个Pdatum同分布。旧 `MeasuredPolicy20261027.actual_policy_advice_confidence` 给出的两个积分原本在Pdatum上；对可测实际评分先用 `integral_map` 得

\[
\int\operatorname{score}_h(d)\,dP_{datum}(d)
=\int\operatorname{score}_h(z(\omega))\,dQ(\omega).
\]

这里直接应用已独立验证的通用接口 `U12_1CausalPolicyBridge20261030.finite_action_causal_ipw`，不要求有理X质量表或有理潜在结果条件均值表。对实际Q取 `X(ω)=(rows ω).treatment.feature`、`A(ω)=(rows ω).treatment.action`，令 `π_h(a|x)=(policyProbability h x a:ℝ)`，K为这两个实际变量与潜在结果向量所生成的 `actualConditional`。z可测使X、A可测；family的概率表检查给出π_h的可测性、非负性和归一性。仍须具备可测且可积的各臂潜在结果、实际Y与所测label的有效连接、一致性、真实K纤维上的条件独立，以及目标支持。实际测量／消费者来源由原观测链保留，不用来源字段替代这些条件。

具体地，`measurementValid` 给出 `indicator((rows ω).measured.label)=Y(ω)`，真实 `loggingMatches` 在P_X几乎处处成立后，经可测X拉回Q，给出所有动作a的 `loggingMass K (X ω) a=(policyProbability logging (X ω) a:ℝ)`。对每个被比较的h，展开 `policyScore` 与 `actualLoggingScore`，用有理数乘法／除法的实数嵌入及这两个匹配式，逐点得到Q几乎处处的等式

\[
\operatorname{score}_h(z(\omega))
=\frac{\pi_h(A(\omega)\mid X(\omega))}
 {\operatorname{loggingMass}K(X(\omega),A(\omega))}\,Y(\omega)
=\operatorname{actualLoggingScore}_h(\omega).
\]

因此 `integral_map` 之后的实际评分积分，由通用core直接等于 `V_B(h)=E_Q[Σ_aπ_h(a|X)Y(a)]`，其可积性也由core推出。成功选择给父政策和被选政策的family成员资格，支持检查与真实logging匹配给二者所需覆盖，allowed来自独立许可。这里既不使用另造的 `frozenPolicyJointPMF`，也不要求 `massMatches` 或 `potentialMeans`。后两项只在原12.3把题给数值接到有限 `policyValue` 时使用，原12.3的测量推论连接保持不变。

于是同一同时置信事件上，旧定理与这个因果连接给出

\[
V_B(h_0)\le\widehat V(h_0)+r
\le\widehat V(h)-r+\mathrm{tol}
\le V_B(h)+\mathrm{tol}.
\]

该事件概率至少1−δ，条件是已列明的采样及识别前提成立。**本题基础推荐固定tol=0，只保证保守非劣。**既有 `choosePolicy` 定理在tol>0时允许至多tol的退化；该情形不作为本题推荐默认。若要报告“严格提升”，在评价前另固定η>0，并对实际所选候选检查附加门槛 `hatV(h)−r≥hatV(h₀)+r+η`；同一推导才给 `V_B(h)≥V_B(h₀)+η`。未过附加门槛则不推荐为严格提升，也不保证已经搜索所有可能改进的候选。该附加门槛是本题构造的数学规则，不宣称现有运行时已实现相应分支。

独立约束的实际输入是 `PolicyPermission.context/environment/policies/authority` 及其外部依据，支持集是目标使用且真实动作概率正的格子。`PolicyDesignReceipt`保留一致性、交换性、抽样、无干扰和测量来源，但这些SourceRef不是因果事实证明。`advice_consumes_actual_measured_values_and_allowed_policy` 保证实际建议读回所用plan、观测、许可和经验值，不替代外部权限有效性判断。

## 12.6（第152、157行）：三类输出及其实际证据

| 输出语义 | 实际输入及输出 | 所需证据与边界 |
|---|---|---|
| 响应模型变化 | 实际 `PolicyObservation` 经 `measuredFeedback` 成为带scope、事件、feature、外部label的观测；`beginMeasuredRound` 将其交给实际下一轮journal与pending候选准备。 | `feedback_reads_actual_external_label`、`measured_feedback_prepares_from_actual_loaded_and_journal` 读出真实标签与准备输入。准备pending不等于候选已加载；拟合或风险改善也是响应模型证据。 |
| 行为策略建议 | `adviseMeasured` 输入当前Gamma、plan、实际测量行、design及独立permission；成功输出 `PolicyAdvice`，保留chosen、oldEstimate、newEstimate与原许可。 | 使用上一节的支持、置信界和因果解释；实际成功证明为 `advice_consumes_actual_measured_values_and_allowed_policy`。输出是给定规范边界内的行为建议。 |
| 适用法律依据变化 | 必须单独输入适用J,t、规则／解释版本、法律依据及权限来源的变化；记录核定的新依据或列明未核事项。 | 行为学习函数没有由VB改善产生新法律依据的返回分支。缺独立依据时实际接口可返回 `.unknown .authorityUnresolved`，不能把模型候选或PolicyAdvice重命名为已生效规则变更。 |

三类是本题的语义区分，不声称当前接口已有一个统一的三构造返回类型。第三类依据需要独立核定，本文不新增规范写入器。

实际状态上，`MeasuredPolicy20261027.measured_data_update_keeps_rules_loaded_and_budget` 证明测量数据进入准备轮后，service.gamma、已加载对象、learner、checker和records保持原值；它没有因行为经验而改写规则。`Final20261021.RSI.u13_1_noninterference` 进一步给出个人响应参数更新前后规则服务相等。信息层面，下一节的同完整行为／异允许集合反例又排除了从行为价值单独恢复法律依据的可能。故第一类输出即使改善VB，也不能自动成为第三类。

## 12.6（第153行）：同完整行为与收益，允许集合仍可不同

直接复用 `U11_1OriginalInstances20261030.original11_6_same_behavior_different_constraints`。在两个合成制度环境中都使用同一个 `Behavior.m1`：`U~Bernoulli(1/2)`、实际 `A=U`、`Y=A`、干预潜在结果 `Y(a)=a`。因此完整行为模型、实际数据分布、响应和每个政策收益均相同；选动作1相对0的效果都为1。

两环境的外生允许集合分别取 `Π₀={0}`、`Π₁={0,1}`。行为分布没有编码这一规范差异。设恢复器H只读完整行为分布B；因为两环境B相同，H必须输出同一个集合C。若它在两边都正确，就有 `C=Π₀` 且 `C=Π₁`，推出 `Π₀=Π₁`，与动作1在一边允许、另一边不允许矛盾。随机化恢复器使用相同随机种子耦合也有相同输出；不可能在两环境都保证正确。能够区分它们的法律依据输入已超出“只读取行为分布”的信息范围。

前述具名Lean声明提供相同完整模型、正效果及实际允许成员差异。新增短推论 `U12_1OriginalInstances20261030.original12_6_behavior_only_cannot_recover_both` 对 `recover:Behavior.CausalModel→Bool→Prop` 证明：即使把共同完整模型m1交给恢复器，它也不能对两个law环境和所有动作同时等于各自允许谓词，已由 run `41004233670` / job `123895367398` 独立验证。只读行为分布的确定性恢复器是该类型的特例；随机化时按固定随机种子使用相同输入的论证如上。这是信息不可区分性，不是拟合容量不足的猜测。

## 12.6（第154行）：三个有限结果与待核依据

| 条件 | 本题输出 | 与实际接口的连接 |
|---|---|---|
| 真实目标支持、独立许可和识别前提有依据；同一law的置信界及保守门槛成立 | 给出所选允许政策、比较基准、所用行为构念、r／δ／tol及支持范围；tol=0标“保守非劣”，有正裕量才标“严格提升”。 | `choosePolicy=some chosen`与成功的 `adviseMeasured` 读回实际允许成员和估计值。统计保证仍是条件式及高概率式。 |
| 目标使用的某格真实动作概率为零，或缺少足以评价该格的依据 | `UNKNOWN／notIdentified`；保留已识别部分与兼容区间，不用高置信拟合补格。原12.3支持缺口可明确报告[0.15,0.65]。 | 支持／数值检查可阻止选择；当前None还可能来自门槛未过、没有允许候选或数值检查未通过，**None不总等于缺coverage**。 |
| 规范约束或其适用性未明 | 停止法律上具有后果的行为建议；列出具体待核依据，响应描述和模型准备不因此变成法律授权。 | `adviseMeasured`对permission来源、context或environment未满足时返回 `.unknown .authorityUnresolved`；错误码本身不是完整待核清单。 |

例如在合成J₀、t₀、规则版本r₀、机制版本k₀下申请推荐动作1，规范输入尚不能支持时，本题报告的待核清单明确为：

1. 哪一独立规范依据在J₀、t₀和r₀下允许该动作及其处理版本；当前状态未核实。
2. 提供该许可的主体是否具有相应权限，以及许可是否覆盖本目标总体和用途；当前状态未核实。
3. permission.context与当前Gamma、permission.environment与plan.environment是否适用；字段比较可执行，实际适用依据仍未核实。

这份清单属于本题报告内容，不谎称当前 `PolicyAdvice` 已有清单字段。现有函数按其实际检查顺序返回结果；不能由某一个错误码倒推出其他尚未执行的检查已通过。法律依据未定与统计误差较小是不同事实，不相关的高预测置信度不能消去上述未核事项。

## 12.6（第155行）：代理分数提高、原结果下降的有限失败例

固定同一J₀、t₀、目标总体、结果定义和两个可比较动作。原行为目标Y定义为“在预先规定的时间窗内完成达到阈值的真实履行”；日志代理Q只记录“系统中点击完成”。设两个动作的确定性潜在结果为：

| 动作 | 代理Q | 原定义真实结果Y |
|---|---:|---:|
| a₀：依真实履行流程处理 | 0 | 1 |
| a₁：奖励点击完成，减少真实履行 | 1 | 0 |

从恒选a₀更新为恒选a₁，代理均值从0升到1，真实目标均值从1降到0。这里即使无限数据、代理预测零误差、代理均值置信区间极窄，也不能把代理的+1写成原目标的改善。新增短推论 `U12_1OriginalInstances20261030.original12_6_proxy_gain_true_loss` 用Bool二动作、`proxy=Behavior.indicator`、`trueOutcome(a)=Behavior.indicator(!a)` 证明这四个值及代理差值+1、真实结果差值−1，已由 run `41004233670` / job `123895367398` 独立验证；其量词只覆盖这个明确有限反例，不宣称一般代理失败定理，也不借用其他意义的“variance proxy”定理冒充结果。

要发现失败，必须保留独立于“点击完成”日志的原Y测量：使用预先固定的 `MeasurementDictionary` 中的单位、构念、阈值、时间窗、时区和时钟版本，以及实际业务执行后的post和原始记录。在付款履行例中，`BusinessMeasurement20261027.performance_magnitude_is_actual_allocation` 要求测得量来自实际receipt的allocated值及匹配的现金事件；一条完成标记不能代替实际付款量。`measurement_reads_actual_state_and_rows` 保留所用post、dictionary、rows、now及实际总量。

事件是否及时按实际发生时刻occurredAt落入真实窗端点的检查确定，记录还须在本次now已可用；已取得的晚到记录不因recordedAt较晚就被当作迟履行。缺少足以判正的有效记录，且没有完整闭窗依据支持判负时，保留未知；未成熟窗口不能仅凭未见事件判负。具备与实际记录清单匹配的完整闭窗依据时，阈值未达到可以判负，这由 `negative_requires_complete_closed_window` 保留。上述外部记录与闭窗依据仍须真实有效，代码字段不能证明物理真实性。

因此，本例的a₀可由有效付款记录及足额实际分配测为Y=1；a₁在完整关闭的观察窗、完整记录清单和未达履行阈值的实际状态下测为Y=0。“点击完成”的Q另存为代理，不覆盖原Y。模型学习、策略比较与后续监测都应继续读取原Y及其独立证据，才能发现“日志学习成功、真实目标失败”。

## 覆盖与边界

原12.3第119行的因果／代数区分和实际识别连接由本文逐步推导及两项已独立验证的接口对应；第117、119–120行数值与截断复用既有数值声明；第121行实值结果界用纸面条件均值推导及既有兼容端点；第122、124行保留冻结环境、真实分母、迁移和记录机制边界。

原12.6第150、152–155、157行分别由有限保守规则、三类实际输入输出映射、同完整行为／异允许集合与恢复器推论、三结果及具体未核依据、代理反例与独立测量说明对应。本文没有把SourceRef、成功字段比较或置信度当作法律、因果或物理事实，也没有将tol非零的不劣容差改写为无条件提升。

仍不能据此宣称：运行时已有统一三类输出构造或自动生成待核清单；未知现实记录机制、交换性、测量真实性和法律权限已被形式证明；单步冻结价值已成为长期制度效果。本文不扩大到整个部署或验收管理，也不改动既有台账状态。 本包记录的独立模块验证不替代完整权威全链与合并；两者仍待完成。
