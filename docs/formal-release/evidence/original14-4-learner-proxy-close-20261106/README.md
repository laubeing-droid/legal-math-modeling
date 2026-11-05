# 原题 14.4：学习器变更与代理指标边界

状态：SOURCE_CHANGED_MODULE_AND_RECORD_CHECKS_AND_CI_INDEX_PASS / PR_ACCEPTANCE_PENDING。本批仅候选数学登记，完整 PR 与合后接受待完成。

冻结 `14_反馈学习与候选更新.md` L107：“将 φ→φ′ 与 θ→θ′ 分开：前者改变如何产生下一候选，后者改变当前预测器。给出保持 E_mech、N及特征接口不变的元更新合同，说明旧候选的验证证据不能自动覆盖φ′未来产生的所有模型。”

现有已验 `AdaptiveRoundLedger20261027.changeRoundLearner` 将 φ 表示为版本和有限 proposal tables：保持固定维数 m，检查每表长度 m、值域 [0,1]、版本推进、无 pending generation、当前 checker 与外部完整许可。`learner_change_keeps_service_budget_and_trusted_root` 保持整个当前 service、checker、records、limit、horizon 与 protectedDomains；因而当前 θ、Gamma 中的规则/机制上下文及固定特征接口不随这一步改变。`changed_learner_is_actual_next_generator` 证明新 proposals 被下一次实际生成消费。固定代码 E_mech 不是该更新的可写对象，外部 catalogue/许可真实性仍是前提。

θ 的变化另经 `ValidatedFeedbackLoad20261027.activate`。`loaded_package_is_actual_written_readback` 绑定实际计算的完整 evaluation、同一 parent/当前 snapshot、sampling/permit、实际写后读回；`replaced_candidate_does_not_reuse_old_permit` 排除给另一 evaluation 复用旧许可。旧单候选或旧固定类的证据只覆盖原精确对象与声明范围，不能自动覆盖 φ′ 尚未产生的全部未来模型。`actual_loaded_risk_follows_computed_domain_bounds` 在有效共同置信前提下给出各保护块新风险 ≤ 旧风险 + tolerance；它既不保证逐点行为相等，也不证明任意新候选风险下降。

冻结 L109：“请在有限模型中展示改进学习器的代理指标（例如训练速度、训练损失）与实际目标风险不一致的反例。提出至少一个可证的有限步保证或一个无法无条件保证的命题；不要声称任意自我修改都能保持单调改进，也不要把所有元更新一律判不可能。”

本轮唯一新连接目标 `U14_4LearnerProxyWitness20261106.learner_proxy_gain_worsens_target_risk` 已通过本轮独立 CI。它复用 `FeedbackLabelSemantics20261027.suggestions_fit_better_but_true_risk_worsens` 的固定两点合成材料，令 before learner 为 `⟨0, []⟩`，after 为 `⟨1, [[1,0]]⟩`；两次均以同一 parent 表 `[0,0]` 加 learner.proposals，调用实际 `fitTable twoPointProtocol binaryLoss ... pseudoData`。

实际已验的精确结论是：两个调用分别返回 known fitted tables `[0,0]` 与 `[1,0]`；拟合经验风险从 1/2 降到 0，而相同 `trueData` 上的目标错误从 1/2 升到 1。这里目标风险是这张固定两点均匀有限表的精确错误率，不是现实总体风险估计；反例不涉及训练速度。源码没有执行 `changeRoundLearner` 的授权转换，没有把 pseudoData 纳入业务 journal，也没有调用 activate 或加载该坏模型。不能把这个纯 fitter 见证记成权限已获批、训练日志已接纳或服务已退化。

可直接复用的有限保证是上述已验元更新 frame、实际新生成消费，以及 `AdaptiveRoundLedger20261027.arbitrary_finite_round_actions_keep_budget`：从初始费用界出发，任意有限动作序列保持 limit 并令累计 charge 不超过它。风险方面只能引用逐保护域、有效置信事件和有限 tolerance 的接纳合同；新见证针对的是“代理拟合损失改善无条件推出目标风险改善”的过强命题。预算不变量不证明统计前提，语法合格不产生法律许可，允许合格有限元更新也不等于允许无限任意自修改。

本包只对应原题 14.4 L107/L109。14.3、14.5 保留各自既有附记与原包证据；工程接线、U00、discharges、Step2、mathflip 不由此注销。本轮源 raw 已验收，root/manifest 实际身份如下；source 独立通过不代表完整 PR 通过。


## 本轮实际独立源与 root/manifest

独立 [run 42106532409](https://github.com/laubeing-droid/legal-math-modeling/actions/runs/42106532409)，attempt 1，job `127522713242` SUCCESS；source `1d21c37f0f955df8701c876b9752932ea856a30d` / tree `b8d4e64e37734dbbcab17d4a981e614931cf0396` / 唯一 parent `687fa0c40da83d5d7de78d5d410c06dda1734eaa`。源 1903 bytes、41 行，SHA `8f2b93559a89577c3a633b6bdb4d5a720dae1335274ca521e4b9cbb60c601181`，blob `ef34da416eeaa4ca49bbb68f611c47768fa0b6f9`。实际1 own / 0 reused audit targets、1 pair / 2消息，0 errors / 0 sorryAx，公理为[propext, Classical.choice, Quot.sound]。证明体复用既有定理不等于新增 reused audit target。authored warning 0、dependency warnings 32（Learning3 / LearningRisk6 / LearningFiniteClass9 / Calibration1 / SelectiveCalibration2 / ProtectedFeedback2 / AdaptiveRoundLedger9），官方原样保留；无失败 source CI 历史，其余7 jobs按mode跳过。

Artifact `changed-module-only-42106532409-1`, ID `13452701481`，ZIP 3020 bytes，SHA `88454c66b95cc3d51c4798c76edcb1576445c811026ecacb2316e4fc2180ceab`。module-plan.json 271 bytes，SHA `e96e640c385f9304087ebbff1254325a76e1eec0bc31d724392fac487d91cad5`；changed-module.log 15953 bytes，SHA `cd0c8145bcd0f46e57bf58b6698f04bba1362d4f6289ded315792f5452cc22f4`。两成员原字节复制，逐目标完整公理输出来自已验 source-target-outputs-r1.json。

source通过后 root `e77e316de68e9a1655e8d1bfbeb28253cd436880` / tree `38a0801dec147e37bb2dcb935c979a64284831e7` 仅增加一条 import，parent为source CP，root blob `ea60a9a15c9d8bbdc3217459a5534644e027d28a`。AA writer单次exit0且无Git差异；metadata checkpoint即此root，无额外AA提交。manifest实际598 files / 0 diverging，绑定该clean root。7项既有derived writers各一次exit0，全部UTF-8读取；没有沿袭旧批driver失败历史。

14.3仅将已核附记追加到[protected-feedback](../protected-feedback-20261027/README.md)，14.5仅追加到[current-context-rollback](../current-context-rollback-20261027/README.md)；原README前缀、verification/raw及复用source pins保持。复用已接受PR131 Authority（精确 run/job/artifact 身份及原始日志见 verification.json），M `4c686359bcf9f3caefce33abe391b7cada467f37` / tree `7d8d6c043039779e8f6f4c4519073e60fcfb7304`，完整源pins、具名实际输出及旧PR证据分别见verification.json和原包；不是本轮source额外targets。

canonical只14.3/14.4/14.5候选COVERED，88/7/2→91/5/1；其余94数学行、105工程行、6cuts与U00整文件保持，U50=50/0/0/124、discharges/Step2/math_flip=false不变。

本地记录与索引验收：7 项 derived writers 各一次完成（AA单次无Git变化，manifest绑定clean root，余六项正常UTF-8接续），12 项 required checks 均 exit 0，受影响稿件回归为 2 passed in 0.95s；CI index 为 621 runs / 1507 quotes，index tests 为 12 passed in 5.21s，标准 --check exit 0。旧 620 条 metadata 保留，仅新增本轮成功 source run；实际 staging、full/authored diffcheck 结果及官方 raw 尾空格诊断另见 `D:/tmp/original14-3-4-5-records-20261106/index-stage-r1-receipt.json`，不把非零 full check 解释为 PASS。完整 PR 接受仍待完成。
