# U13.3 原欠项独立关债：OPEN 13 → 12

本包仅处理原题 U13.3 的表示迁移风险等式与冷启动不可识别边界。`verification.json` 保留冻结 archive 的原始 residual，并绑定六个具名 Lean 声明、源码和一次独立 changed-module CI run。它不把同模块编译等同于完整 release 验收。

- 风险迁移：已有表示变换逐点等式，加上同一概率测度、同一损失及原题使用域上的逆条件，得到两边积分相等；不增加损失可积性结论。
- 冷启动边界：复用既有双世界同观测反例、空样本实例、未观测输入的两个端点，以及全部 checkpoint 缺失时返回 UNKNOWN 的声明。
- CI: [run 40714963358](https://github.com/laubeing-droid/legal-math-modeling/actions/runs/40714963358), [job 122910040136](https://github.com/laubeing-droid/legal-math-modeling/actions/runs/40714963358/job/122910040136), subject `c4baf6d1dcf81a53cbf1e58abf87e18e4c500711`, SUCCESS. Artifact: `changed-module-only-40714963358-1`. `axiom-audit.raw.txt` 是从该 artifact 中 driver 第39–55行对应的六组真实 `#check` / `#print axioms` 输出提取，保留完整类型续行。

U13.2 的规则更新权限及完整观察/交换关系、U13.4 各 fallback 的适用性/来源/错误处理与原题实例、原题13.5 的 InScope 判据及规范/检索/预测回退消费链仍待核对既有实现和原题实例。本包不关闭这些义务，也不改变其余 OPEN。

全局 `discharges_archived_manuscript_gaps=false`、冻结 `tip_pin`、CAND8 与原题其他范围保持不变。整体放行以最终PR head的ULM、Authority、final-gate和正式证书核验为准；本包仅为独立模块CI/源绑定回执。
