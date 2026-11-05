# U13.3 原欠项独立关债：OPEN 13 → 12

本包仅处理原题 U13.3 的表示迁移风险等式与冷启动不可识别边界。`verification.json` 保留冻结 archive 的原始 residual，并绑定六个具名 Lean 声明、源码和一次独立 changed-module CI run。它不把同模块编译等同于完整 release 验收。

- 风险迁移：已有表示变换逐点等式，加上同一概率测度、同一损失及原题使用域上的逆条件，得到两边积分相等；不增加损失可积性结论。
- 冷启动边界：复用既有双世界同观测反例、空样本实例、未观测输入的两个端点，以及全部 checkpoint 缺失时返回 UNKNOWN 的声明。
- CI: [run 40714963358](https://github.com/laubeing-droid/legal-math-modeling/actions/runs/40714963358), [job 122910040136](https://github.com/laubeing-droid/legal-math-modeling/actions/runs/40714963358/job/122910040136), subject `c4baf6d1dcf81a53cbf1e58abf87e18e4c500711`, SUCCESS. Artifact: `changed-module-only-40714963358-1`. `axiom-audit.raw.txt` 是从该 artifact 中 driver 第39–55行对应的六组真实 `#check` / `#print axioms` 输出提取，保留完整类型续行。

U13.2 的规则更新权限及完整观察/交换关系、U13.4 各 fallback 的适用性/来源/错误处理与原题实例、原题13.5 的 InScope 判据及规范/检索/预测回退消费链仍待核对既有实现和原题实例。本包不关闭这些义务，也不改变其余 OPEN。

全局 `discharges_archived_manuscript_gaps=false`、冻结 `tip_pin`、CAND8 与原题其他范围保持不变。整体放行以最终PR head的ULM、Authority、final-gate和正式证书核验为准；本包仅为独立模块CI/源绑定回执。

## 原题 13.2 更新类型与观察交换 · 2026-11-06

冻结题单 L101、L103 和补正 S13 L220 将个人权重、保持符号定义的表示改码、机制或概念定义变更分列。以下表格是有限提议合同，实际执行许可须由相应主体和证据给出。

| 更新对象 | 能改变的输出 | 保持对象及观察 O | 交换关系和必须重证的性质 | 外部前提 |
|---|---|---|---|---|
| A：固定 E/N，更新 θℓ | 该主体经验预测。合法统计输入 e 改变时，案件判断可变。 | E/N、数据、其他主体参数及未授权写域。规范观察取固定案情 c 与证据 e。 | 固定 c/e 时，G(E,N,c,e) 在更新前后相等，直接使用 `RSI.u13_1_noninterference` 与 `RSI.u13_2_personal_frame`。预测证书覆盖范围、数据条件及经验效果各自核验。 | 个人数据用途、作用域、更新及加载权限。 |
| B：更新材料到特征的 φ，保持符号定义 | 特征编码和内部坐标。 | 独立声明的法律目标观察 o∈O、符号概念定义及固定合同的其他字段。 | 在声明使用域分别满足 `d_o(φ(x))=o(x)` 与 `d′_o(φ′(x))=o(x)`，故两种编码的解码相等。新旧特征值可以不同。每个声称保持的观察都须验其解码关系，风险运输另验实际使用输入及预测头。 | 表示变更权限、受影响观察及使用域的明确声明。 |
| C：更新 E_mech 或概念形式定义 | 合同准许修改的机制输出、概念解释及其依赖的判断。 | O 中明确声明保留的观察和未授权写域。允许改义的观察单列其新定义和版本关系。 | 对每个保留观察在新旧对应状态上重证 `Obs_new(bridge(s))=Obs_old(s)`。重证受影响的类型和语义桥，重新核验依赖新定义的预测。A 的证书以固定 E/N 为前提，C 需用自身的观察与验证合同。 | 机制独立验证、概念或规则变更的独立授权与适用性、发布权限。 |

A 的直接来源是 `JurisLean.Candidates.Final20261021.RSI` 中的实际函数更新与固定输入规则服务。C 的写域参考同模块 `Update` 和 `prepareUpdate` 的规则与机制提议，机制提议的两份 `SourceRef` 分别引用独立验证与授权。共同观察桥的适用前提可复用 `JurisLean.Seams.Representation.obsModel_roundTrip` 的实际往返性及 `representation_observations_preserved` 的忠实表示条件。

B 的一个充分情形是 `φ′=b∘φ`、`d′_o=d_o∘b⁻¹`，其中 b 为给定双射。代入 `RSI.u13_3_representation_transfer` 得到每一声明观察保持。若使用域上只给 `back(b(φ(ω)))=φ(ω)`，`JurisLean.Candidates.U13_3DebtClosureAudit20261028.same_loss_risk_under_used_inverse` 在同一概率测度、同一损失函数和相应的预测头下给出两个积分相等。积分是否代表有限可积的风险，仍由各自的测度与损失条件决定。只给法律观察等式时，另行检查预测头及经验风险。

L103 同一材料的两种处理取冻结 10/7/7 实例中“原余额 10、第一笔实际付款 7”的已给材料。纯重命名时，将“已付款”的旧代码 0 换成新代码 1，并交换两代码的解码，套用上面的双射式即可保持“已付款”观察。若把新代码解码成“已清偿”，则同一材料上的观察已改。第一笔付款后余额仍为 3，直接见 `JurisLean.Candidates.Final20261021.Acceptance.a_u09_continuous_10_7_7`。本实例在数量片段用余额归零表示覆盖到期额的观察，其条件判据见 `JurisLean.Seams.UnifiedQuantLedger.discharged_iff_paid_covered`。于是“存在付款”观察为真，而该数量覆盖观察为假。真实清偿效力仍由外部法律条件决定。

本归引复用 U13.3 的原模块回执及当前已接受的 Authority 原始类型输出。13.2 的新增内容为逐段对应、提议合同及对具名声明的实例化。U00 的实际消费者按原调用合同验收。
