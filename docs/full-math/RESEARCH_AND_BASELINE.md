# 来源、当前基线与设计归属

本包把三类内容分开：`plan/original`是已交付材料原文；仓库连接器读取用来确认当前基线和原任务；完整执行次序、补充算法与全量完成合同是本轮项目设计。后者不能冒称原论文已经验证了本项目。

当前固定基线为`1016d69522b436cf8b0314100509c5e1936ca141`。既有七轴证明及CI成果保留。本轮没有下载成功完整仓库快照，旧参考目录不当作当前生产源码；执行者安装时以实际checkout为准，不清空或覆盖已证明模块。

## 本轮实际核对的研究与文档

### BASELINE｜数学仓main及既有证明清单

来源：https://github.com/laubeing-droid/legal-math-modeling/tree/1016d69522b436cf8b0314100509c5e1936ca141

用途：当前仓复用基线，不能覆盖最新已证七轴修订

边界：GitHub connector reads; not a full fresh clone

### PROOF-TARGETS｜原57项数学与经验目标

来源：https://github.com/laubeing-droid/legal-math-modeling/blob/1016d69522b436cf8b0314100509c5e1936ca141/tools/ulm_consolidation/plans/PROOF_TARGETS_57.json

用途：保持原ID、原目标与证明任务，不缩成示例

边界：原始资料保留；不能由复制行为升级完成状态。

### RETAINED｜此前完整施工包与需求原件

来源：plan/original

用途：按原件复制及SHA256登记；旧状态仅作历史，不继承已过期施工终点

边界：原始资料保留；不能由复制行为升级完成状态。

### LEAN｜Validating a Lean Proof

来源：https://lean-lang.org/doc/reference/latest/ValidatingProofs/

用途：区分命题含义、实际编译、公理及可信边界；不能以名称或绿灯替代语义对应

边界：最新文档不表示自动升级项目固定4.30.0；具体接口依固定库源码与CI

### CATALA｜Catala: A Programming Language for the Law

来源：https://arxiv.org/abs/2103.03198

用途：受限规范语言、独立语义与核心编译步骤证明

边界：不证明任意法律自然语言可全自动无误编译

### CAUSAL｜An Automated Approach to Causal Inference in Discrete Settings

来源：https://arxiv.org/abs/2109.13471

用途：离散因果模型到多项式约束及可验证内外界

边界：识别和边界相对因果假设；法律归责另由规范层给出

### CONFORMAL｜A Gentle Introduction to Conformal Prediction and Distribution-Free Uncertainty Quantification

来源：https://arxiv.org/abs/2107.07511

用途：分割保形分数、有限样本分位数和覆盖对象

边界：交换性等条件需要；边际覆盖不等于个案胜率或筛选后覆盖

### CS｜Time-uniform, nonparametric, nonasymptotic confidence sequences

来源：https://arxiv.org/abs/1810.08240

用途：持续检查和平均条件风险的时间一致保证

边界：不保证任意漂移下永久校准；实际过程前提必须证明

### REQ｜Foundations of Requirements Engineering

来源：https://pamelazave.com/fre.html

用途：领域假设、规格、业务需求以及可实现性区分

边界：本包法律业务合同和具体算法是项目适配，不是作者已经为本仓证明

## 引用继承规则

原57项卡、134项和法律族保留各自来源。这里没有重新核验所有法条现行性或所有论文全文。执行者对需要采用的具体定理，应读固定版本原文并记录其前提；对具体法条、证明责任和程序政策，按原法源任务保留审核状态。不得把旧行政诉讼法草案、过期网页或外部skill当现行法。

本包没有增加拓扑斯、量子认知等新研究分支。所有补充服务已确认的统一模型、概率/数值/论证/策略/交付目标。构造类型理论和现有mathlib负责共同表达，求解可以异构，证明与观察必须相连。
