# 原题 13.4 作用域条件估计与持久更新

状态：SOURCE_CHANGED_MODULE_AND_RECORD_CHECKS_AND_CI_INDEX_PASS / PR_ACCEPTANCE_PENDING。本包登记原题13.4 L113/L115，并关联13.5纯归引；候选数学关闭仍待本批完整PR和合后接受。

冻结依据为题单 13.4 L113、L115，补正 S13 L222 和总稿 L643–645。以下 `RSI` 指 `JurisLean.Candidates.Final20261021.RSI`。

## L113 同一数据的两个作用域

对有限数据 D 和声明的作用域成员判据，取 D_s 为 D 中满足该判据的记录。保持原记录顺序，从同一 D_s 取对应的权重和结果两列，再调用 `RSI.conditionalEstimate`。原函数在两列长度不等或出现负权时返回 rejected，正总权重给出 Σwᵢyᵢ/Σwᵢ，零总权重返回具名未知。此处的有限实例用两个布尔标签表示作用域 A、B，分别在同一 D 中取到一行。

| 作用域 | D_s 中的 (w,y) | 加权结果 | 权重有效量 | 不确定性 |
|---|---|---|---|---|
| A | (2,1) | known 1 | 1 | unknown · missingEvidence |
| B | (3,0) | known 0 | 1 | unknown · missingEvidence |

`JurisLean.Candidates.RSIScopedCondition20261106.scoped_estimates_differ_without_changing_persistent_state` 证明两次调用的完整返回记录和状态等式。两次查询使用同一 D 和同一初始 State，实际执行各自的筛样与既有估计。状态分量直接复用 `RSI.u13_2_condition_does_not_train`，两次都返回原 State，因而持久 Θ 的每一项保持相等。D 是本次查询给定的有限记录，两个数值是题给条件统计。

返回合同保留查询作用域、实际选中的样本及其权重、带状态的条件估计、权重有效量及独立的不确定性字段。对非负权且 Σwᵢ>0，至少一项 wᵢ>0，故 Σwᵢ²>0，权重摘要取 Kish 量 (Σwᵢ)²/Σwᵢ²。估计缺失或被拒时，权重有效量为空。Kish 量描述权重集中度。样本的独立有效规模和置信界需要该作用域内的独立抽样及误差条件。本实例的输入没有给这些条件，两个返回的不确定性均为 `unknown .missingEvidence`。

## L113 标签与存储隔离

复用总稿 L643 的共享地址反例。令两个不同标签指向同一可变地址 a，写前两者读到 store(a)=0。经第一个标签原地写入 1 后，第二个标签也读到 1。标签与目录均可不同，地址等式仍成立。该错误实现违反持久个人函数的 frame，排除方法是检查实际引用隔离或证明物理更新精化该函数更新。

## L115 个人 frame 与跨域风险

`RSI.u13_2_personal_frame` 已证明对每个 j≠ℓ，更新 ℓ 后的 personal(j) 等于原值，同时保持 E/N/D。该状态等式不含任何风险不等式。对同一律师的两个经验作用域 A、B，复用 `JurisLean.Candidates.ProtectedFeedback20261027.average_improvement_can_harm_protected_point` 的二点构造。两个作用域的目标均取 false，权重分别 9/10、1/10。更新前预测表为 (1,0)，更新后为 (0,1)。A 的损失 1→0，总风险 9/10→1/10，而 B 的损失 0→1。把两个预测表作为该律师更新前后的候选模型，其余律师的参数沿用上述 frame。状态隔离与跨作用域风险变化分别成立。

上述返回合同及两个例子对应冻结的有限 Cond 与个人状态。真实来源、跨域支持、校准及外部权限由各自合同核验。U00 边 12、13 沿用当前实际消费者合同。

## 实际 source 与复用证据

独立 [changed-module run 42090759153](https://github.com/laubeing-droid/legal-math-modeling/actions/runs/42090759153)，attempt 1，job `127467851347` SUCCESS。source `3c63d57b1cd3f418b42afdd511ac5c713823d7e8` / tree `cd5b06644018f112d1e36fc5d2f71254ee104447` / 唯一parent S130 `2227a1bc7aa4e39d9126b71977e2539d1def201d`，2314 bytes、63行，SHA `afe08b1495985ea0da56d68b389659ed823c68799246d9d8396915de165b4586`，blob `59762d5a5e2110a02a7ec8dcf660457c49090547`。实际1 own / 0 reused targets / 1 pair / 2消息，0 errors / 0 sorryAx，公理为[propext, Classical.choice, Quot.sound]；无失败源码CI历史。其余七个job按mode跳过，不代表本批完整PR通过。FQN、源行号及完整跨行公理输出来自已验收 source-target-outputs-r1.json。

官方 Artifact `changed-module-only-42090759153-1`, ID `13445905788`，ZIP 865 bytes、SHA `334aa24ff93e471635ea625b8fc775d19a1561b529308e957577a7c6651d1e10`。module-plan.json 259 bytes、SHA `ec55a01b1b834e93898d6a4b9da2e546f29e7f0bbdf97e7661a911aea98c8ab6`；changed-module.log 1094 bytes、SHA `1c6d400dd135e9778f1931f9d329eb8e0289a3a836aaff32e9ed3a7a6e1d2e86`，均原字节复制。

原RSI frame及跨域反例复用已接受 [PR130](https://github.com/laubeing-droid/legal-math-modeling/pull/130) Authority，exact M `333aa2e34b58dc21fcae5d603343483a098d7d28` / tree `8a3572c10f469ba1735edc45c3e1b91be2405eca`。lake-clean-build.log L9394–9405给personal_frame（propext）和condition_does_not_train（无公理）；L11975–11986给ProtectedFeedback的二点损失反例（标准三项公理）。原RSI 4175 bytes、SHA `9a5bc5e53c8e4d12a4bc4006d637f063ccf835165f3c3b8f3b5fa11d4fa7ac8e`、blob `b0239a3cb86b91153dc1ec45f228e648f52e6aab`。完整run/job/artifact和逐段实际输出见verification.json；它们不是本轮source额外targets。

source通过后root checkpoint `7235e6aae33b3a91e95f677589c5d0b7033605db` / tree `c427628698e0c99f284744305f07345ddd061fe9`，parent为source CP，仅新增root import，root blob `16e2a7db7c1bb890ce46ba90472acf8570f68973`。AA writer单次exit0且无Git变化，无额外AA checkpoint；manifest实际597 files / 0 diverging，绑定该clean root。source proof、root/manifest与未来records H/M身份分开。manifest进程exit0后，外层driver因默认GBK读取UTF-8停止；实际原收据保留，显式UTF-8接续余五项，未重跑AA或manifest；这不是失败CI。

13.5 L119/L121仅将已核正文追加到[既有U13.4证据包](../u13-4-debt-close-20261030/README.md)。旧独立19目标证据及七源pins保持，PR130 Authority补充实际类型/公理输出。有限准入检查、经验估计、真实母体支持、概率条件和外部适用依据分别保留；两世界反例及规范/描述/预测三分、四来源顺序和各层UNKNOWN按原合同归引，无新13.5 Lean或module CI。旧README物理前缀、verification和raw不改。

D是显式查询数据；完整返回合同中的Kish量仅为权重摘要，不冒充独立有效样本数或置信界。共享地址反例直接归引冻结总稿L643；状态frame不推出跨域预测性能保持。当前U00 edges12/13实际消费者、caller、评级、历史与整文件不变；U50仍50 wiring/0 narrow/0 open/124 bindings，discharges、Step2、math_flip均false。canonical只13.4/13.5候选COVERED，84/10/3→86/9/2，其余95数学行、105工程行、6cuts不变。

本地记录与索引验收：7 项 derived writers 各一次完成（AA单次无Git变化，manifest实际exit0后driver编码诊断保留，其余五项接续），12 项 required checks 均 exit 0，受影响稿件回归为 2 passed in 0.92s；CI index 为 620 runs / 1505 quotes，index tests 为 12 passed in 5.24s，标准 --check exit 0。旧 619 条 metadata 保留，仅新增本轮成功 source run；实际 staging、full/authored diffcheck 结果及官方 raw 尾空格诊断另见 `D:/tmp/original13-4-records-20261106/index-stage-r1-receipt.json`，不把非零 full check 解释为 PASS。完整 PR 接受仍待完成。
