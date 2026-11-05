# 原题 15.1：有限改进的三个边界与固定风险秩

状态：`SOURCE_CHANGED_MODULE_AND_RECORD_CHECKS_AND_CI_INDEX_PASS / PR_ACCEPTANCE_PENDING`。独立 changed-module run `42114888158:1` / job `127551793229` 已成功；Artifact changed-module-only-42114888158-1, ID 13454354956。2 own / 0 reused audit targets、4 条 check/axiom 消息，errors=0、sorryAx=0，两项均为 `[propext, Classical.choice, Quot.sound]`；authored warning 0，dependency warnings 29 原样保留。原始输出与精确目标行号见本包 verification.json、module-plan.json、changed-module.log。仅 source 已验，不代表本轮 PR 或正式关账已接受。

冻结 `15_多轮改进验证与能力边界.md` L89：“区分训练损失下降、验证集分数上升、目标分布真实风险下降、对所有合法输入都不退化、以及所有未来版本持续改进。给出至少三个严格不蕴含的有限反例。”

本行对应三个不同的有限不蕴含，不把同一反例换名重复计数：

1. **训练代理损失下降不推出目标风险下降。** 复用已验 `FeedbackLabelSemantics20261027.suggestions_fit_better_but_true_risk_worsens`：固定两点合成 pseudoData 上拟合经验风险降到 0，而相同 trueData 上的精确目标风险恶化。训练标签/损失与目标对象必须分别声明，不能以建议标签代替真实标签。
2. **平均目标风险改善不推出每个旧关键输入不退化。** 复用已验 `ProtectedFeedback20261027.average_improvement_can_harm_protected_point`：两个点权重 9/10、1/10，平均错误 9/10→1/10，关键点错误 0→1。它否定用全局平均改善替代逐保护域/逐点责任。
3. **同一验证样本的准确率严格上升不推出目标风险下降。** 本轮独立已验目标 `U15_1IterationBoundaries20261106.validation_score_rises_while_target_risk_increases` 使用同一 `Fin 6` 域、同一验证集 `{0,1}` 和全零真标签。baseline 只在 x=0 输出 true；selected 由原 `fromProbeScores (probeScores sample)` 实际反馈构造。实际已编译的精确比较是验证准确率 `1−error` 从 1/2 升到 1，而固定六点均匀目标风险从 1/6 升到 2/3。它复用原反馈泄漏定理，补的是同一验证样本上的严格比较，未更换验证集或目标分布。这是有限合成算例，不是现实数据实验。

冻结 L91：“在固定有限模型类和固定目标风险下，给出带容忍ε的单次接纳合同。证明哪些额外条件能推出有限T轮的累计退化界或单调性；若每轮只允许最多ε_t退化，写出实际可得的Σ ε_t界，而不是声称零退化。严格改进在有限可达状态空间中能否无限持续？阐明收敛、停止、达到全局最优不是同一个结论。”

单次实际接纳复用 `ProtectedFeedback20261027.bounds_gate_on_joint_event_preserves_each_risk` 与 `ValidatedFeedbackLoad20261027.actual_loaded_risk_follows_computed_domain_bounds`：在同一预声明类、域、目标/损失和有效共同置信事件上，实际界比较通过，且精确 evaluation/许可/采样支持通过加载门，推出各保护域 `R_next≤R_old+ε`。`known evaluation` 与 `passesBounds=true`、实际 loaded 是不同条件。容忍 ε 可以允许退化；ε=0 才得到相应域的不劣，严格改善还需原 `strict_bounds_prove_strict_improvement` 的严格界比较。有限数据、时间戳或已扣预算本身不证明统计前提。

对于同一固定风险对象，若实际连续轨迹每一步都已具备 `R_(t+1)≤R_t+ε_t`，可实例化原 `Final20261021.Iteration.RiskTrace`，由 `u15_1_finite_cumulative_improvement` 得到有限 T 轮 `R_T≤R_0+Σ ε_t`。不能把这个逐步真实风险前提省略，也不能把 Σ ε_t 改成零；不同域需逐域实例化，统计置信还须另满足 15.2/15.3 的同实验联合预算合同。

本轮独立已验目标 `finite_class_excludes_infinite_strict_risk_decrease` 从固定有限 `models` 和固定实值函数 `risk` 构造风险秩：一个模型的秩是该类中风险严格更低的模型数。每次真实风险严格下降使该计数严格下降，源码连接既有 `ProcedureClosure20261027.strict_rank_excludes_infinite_execution`，推出不存在永远留在该类且每步风险严格下降的无限路径。本轮已取得这两项源目标的独立编译与公理输出；不把此结论扩大到整个服务终止。

该结论只排除固定有限类中无限连续严格下降。若允许相等风险的自循环、拒绝/重放或持续外部输入，整个服务未必停止；若扩大模型类或改变风险/目标，原风险秩合同也不能沿用。停止不证明全局最优，严格改进路径结束只表示其所采用转移没有继续取得严格下降；没有穷尽全类或全局最优证书，就不声明最优。收敛是风险/状态序列的另一性质，不能由两个样本比较自动推出。

15.2/15.3 仅一次追加已审正文到既有 adaptive-validation 证据包；其采样条件、确定性费用、UNKNOWN 和 U00 另账边界保持。source proof 为 `94a4de8b9dce276603714249d576c2cb7ec1a781` / tree `e0ebf8e00bb93b00a5fb28e862584831df835460`；source 通过后的 root 与 clean manifest checkpoint 同为 `e362e3138d650269dc73cd6ab4b7caa8a53da0b5` / tree `ef2e8d1e00f63e98b8a5e68c56ad597318d4c063`，manifest 实际599文件、0个偏离。AA writer单次无Git变化，无额外AA提交。records H/M及完整接受尚未产生；工程、U00、discharges、Step2、mathflip不变。

既有具名定理的实际复用证据来自已接受 PR131 Authority，同树源 pins、逐目标完整类型与公理、原包身份均见 `verification.json` 的 `reused_evidence` 与 `related_record_only`。15.2/15.3未新增源码或独立模块CI，统计前提与真实业务轨迹分开。

本地记录与索引验收：7 项 derived writers 各一次完成（AA单次无Git变化，manifest绑定clean root，余六项正常UTF-8接续），12 项 required checks 均 exit 0，受影响稿件回归为 2 passed in 0.95s；CI index 为 622 runs / 1511 quotes，index tests 为 12 passed in 6.56s，标准 --check exit 0。旧 621 条 metadata 保留，仅新增本轮成功 source run；实际 staging、full/authored diffcheck 结果及官方 raw 尾空格诊断另见 `D:/tmp/original15-1-2-3-records-20261106/index-stage-r1-receipt.json`，不把非零 full check 解释为 PASS。完整 PR 接受仍待完成。
