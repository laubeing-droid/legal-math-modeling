# 统一法律数学理论：阅读入口

本页把同一 main 中的理论、形式源码、代表性中国法构造和证据连成一条阅读路线，不新增数学定理，也不把仓库整合写成全部理论完成。

## 先读什么

1. **统一的数学问题与边界**：[法律统一数学模型](master-plan/09_法律统一数学模型_20261001.md)。统一指同一法律对象域、分层观测、表示与保义、具名链式推导、非退化、有限过程组合及时间/不确定性保持；接口连通本身不是理论统一。该文是带日期的施工论述，其状态必须结合后续源码及证据阅读。
2. **整体理论叙述**：[中文主论文](../paper/main_cn.md)、[英文主论文](../paper/main.md)及[论文目录](../paper/README.md)。ULM01–ULM16 依次展开请求、结果、类型图、义务、机器、事实证据、Horn 支持、论证构造、攻击击败、Dung 语义、分支查询、程序、域组合、覆盖信任、增量与条件收缩、理论组合。论文中的 FORMALIZED、DERIVED、CONJECTURE 不可互换。
3. **中国法有限表达域的统一实例**：[理论及验收对应](cn-unification/THEORY-20261105.md)、[声明与消费者证据映射](cn-unification/EVIDENCE-20261105.json)。这里把共同对象、九算子、十二项代表制度和八类具名引擎放到同一有序事件历史中；这是有限语言及指定制度域的语义连接，不是任意中国法只换参数的全称定理。
4. **逐条核对真正的数学陈述**：[Lean 源码](../proofs/lean/juris_lean/JurisLean/)、[概念总谱](master-plan/基线/法律概念总谱.md)、[数学规格](full-math/MATHEMATICS_SPEC.md)。具名定义、前提、结论和后续修订比概述优先。
5. **核对该提交的证据**：[发布协议](formal-release/FORMAL_RELEASE_REPORT.md)、[允许的声明](formal-release/ALLOWED_CLAIMS.md)、[禁止的声明](formal-release/FORBIDDEN_CLAIMS.md)。历史绿色只覆盖其准确 subject，不覆盖当前 main。

## 三个层次怎样连接

- **基础与一般理论**：ULM、KernelV3、Hohfeld、候选数学结果及各自具名前提。整合不改变这些定理契约，也不重开或代替原有关债台账。
- **声明片段的理论组合**：Seams 系列提供特定表示、观测、推导及组合关系。已具名的组合结果，不等于对所有真实法律域的全覆盖证明。
- **中国法的实际有界消费**：`JurisLean.CN.Completion20261105` 是该包的聚合入口。`executeCommand` 返回实际 Reply，`runProgram` 传递实际后态，`Runtime.serveLine` 是数学参考 IO 入口；具体源声明和消费者见该包证据映射。计算结果、法律权限、材料准入和决定/拘束彼此区分。

公共法律入口使用 Ready / WorldSemantics。旧 v4 的 truth-pinned compatible 和裸 RuleTicket 保留为历史片段，不再用来认证一般法律步。UNKNOWN 可以是模型明确定义的返回值，但缺少编译、连接或证据不能据此算验收通过。

## 整合与未完成项

本次以 main `60a809ba1760e138019220ae53c59d36b823b0ac` 为底座，合入中国法分支 `3f82db702098d0e4bc5816f09e938a67cb947f2e`；保留双方 Git 历史及主线后续成果。没有用旧分支树替换 main，没有删除历史分支，也没有改动其他仓库。

中国法包中的 HANDOFF、CONSTRUCTION、THEORY 和 EVIDENCE 是原分支的带日期交付记录，其中 MERGE_PENDING、D1 和旧 subject 描述原交付时点。它们保留原交付内容作为来源（产物编号的标签仅作消歧）；当前整合状态以提交拓扑和该提交的新 CI 为准，不能把原分支 changed-module 结果搬作整合后的 full-release 证明。

本轮整理不宣称全部数学目标、全部中国法覆盖、真实材料认证、生产部署或 DeepInfer 适配器已完成。既有未闭合目标、机器反例、条件性结论及外部义务仍然保留。静态台账是源码清点，不是 Lean 验收。

## 历史材料如何读

日期文档、旧候选和失败实验用于追溯，不按分支是否存在决定真假。优先使用同一 subject 的源码、机器可读规格和 GitHub Actions 原始证据；旧稿不能覆盖后续修订。全部目录与证据解释见[文档索引](INDEX.md)。

## 其他分支的成果核对

2026-11-07 对剩余分支进行收束，逐项承接关系见[分支收束记录](handoff/BRANCH_CONVERGENCE_20261107.md)。原有关债模块保持原样，新增结果通过其现有类型、实际测度和策略模型接入：

- `formal/grouped-split-20261027`：原题继续使用 `LearningEventSplit20261027`。保留的 `LearningSplit20261027` 复用同一观测类型，证明 measurement 到 event 解析一致时两个实际分区相等，并用反例明确任意 measurement 分组可能拆开同一 event。旧撤回记录保留其当时含义。
- `formal/original06-finite-examples-20261031`：`U06_OriginalFiniteExamples20261031` 保留二次效用和唯一最优 iff；新增具名连接证明其有限表等于主线 `demoUtilities`，最坏分支值等于主线有限下确界，二次效用的 75/50 由主线 Bernoulli 测度和 cashOutcome 实际算得。现金身份、一般期望效用和共同策略仍使用原有主线模块。
- `paper/cn-walls-20261031`：旧十二制度由当前 CN 的 Rights、InstitutionRules、Institutions 和 EngineConsumers 承接。旧截止证明的相等边界已有 `cut_at_acceptance`、`cut_after_acceptance`；两处 True 占位由实际个别责任投影和分轨保持命题替代。来源提交保留在合并历史。
- `paper/codex-cn-ops-v4-20261101`：全部提交早已合入 main；后续 CN 工作集中在主线。完整九算子生成语义及保义覆盖仍需具名定理，分支收束本身不改变该数学问题的状态。
- `formal/original07-static-close-20261031`：左逆非满射反例见 `Original07_4ObservationInstance20261102.lean`；共同来源语义和数量连接见 `SourceFinalBridgeAudit20261102.lean`；paymentMeaning 与选中行绑定仍在 `U07_3FixedBindingAudit20261029.lean`。主线后续桥接的证据位于 `formal-release/evidence/original07-8-static-source-bridge-close-20261102/`。来源真实性及原 Nat 金额域限制没有因组合而消失。

以上 Lean 文件均位于 `proofs/lean/juris_lean/JurisLean/Candidates/`。这里记录的是源码与目标覆盖核对，不是本轮新 Lean 编译结论。

## 合流兼容性修订

首次全量验证发现源码样式与主线静态门的差异。本次仅将 EngineConsumers 的事件单射检查由 Bool `decide` 条件写法改为同一命题的 Prop 条件，并移除根入口首字节 BOM；未修改定理陈述或冻结的旧 CN 基线。旧 Acceptance 产物以原字节保全，另附清楚标记的诊断前缀去除副本供证据阅读。后续修改仍须准确新 subject 的权威 CI，旧分支的通过不自动沿用。
