# 给施工Agent：数学仓一次执行到底

你承担的是**完整数学计划的施工执行**，不是方案评审，不是安装包，不是固定本金示例复现。

用户最新指令覆盖此前并行顺序：先在`legal-math-modeling`完成全部数学建设，再准备JC和Harness的改造接入。本轮不改其他仓、不要求其先上线、不新建审批、签章、密钥或多Agent平台。

## 唯一收工线

全部原57目标的数学部分、九个EXT、134项业务需求的形式实例、X01–X10形式部分，以及七个通用根取得所要求的真实证明与验收。`MATH_BUILD_COMPLETE`是唯一数学收工状态；固定七轴例子通过、源码全编译或几个测试绿色都不是。

先完整读取：

1. `MASTER_MATH_COMPLETION.md`。
2. `docs/MATHEMATICS_SPEC.md`。
3. `docs/ALL_TARGETS_EXECUTION.md`、`ALL_EXT_IMPLEMENTATION.md`、`ALL_134_MATH_CONTRACTS.md`。
4. `plan/REQUIREMENTS.json`、`DEFERRED_EXTERNAL.json`、`EXECUTION_ORDER.json`。

然后立即施工，不再先写一份类似评审回给用户。

## 实际动作

在已存在数学仓新建一个工作分支，核对当前主分支和本包来源。已有七轴修复、Rosetta更名及正式CI保留。对比已有声明和算法，能够复用的直接复用，缺的按完整数学规格补齐。

先运行 `APPLY.py --repo <数学仓>` 预览，再`--apply`；这只安装新的执行规范和辅助工具，不替你完成证明。按照README在数学仓装CI差量；既有工作流不能被删掉。已经修改的`tools/full_math/spec/BINDINGS.json`不得被重新安装清空。

内部按依赖连续推进，但**不向用户分批交付、不在某个模块后询问继续**。每个目标同时完成独立语义、具体算法、证明、反例、引用与共同根连接。`GenericKernels.lean`是公用候选，不是用来一键替代全部需求的伪证明。

为每项填写真实绑定并导出约定的`Contracts`与`Acceptance`声明。需求和根的数学内容以本包公式为准；不能把目标改成True、把本应证明的结果移进前提、将输入域缩成演示常量、把开放待审核字段自行填写为真。

本地只跑Python。Lean在GitHub使用原固定4.30工具链。可在同一执行期间反复用changed-module获得编译反馈；这些内部反馈不是本轮最终完成证据。最终必须触发full-release，所有目标在同一次全量环境中接受。

任何失败都读取真实日志、修当前模块并继续；不得删除失败用例、缩小目标或拿别的commit绿色工件拼接。保留所有真实反例。

## 外部事项

不要把E01真实校准样本伪造成数学输入；没有真实数据就是E01-EMPIRICAL未验。把学习、区间、校准、保形和序贯等数学全部做完，并把真实验证运行器交齐，不能因此回避概率数学。真实法源/事实审核同理分账。

JC/Harness生产接线后置，仅交明确的适配契约。不能因为原任务C06/ROOT07提到生产就又拉回两仓并行开发。

## 中断恢复

若宿主会话被迫中断，将精确commit、未完成目标ID、最新报错、正在证明的symbol和下一条命令写入`work/full-math/CONTINUE.md`。恢复后继续，不将它包装成阶段交付。不得仅运行`queue`便结束。

## 唯一最终报告

`MATH_COMPLETION.json`必须来自实际GitHub全量完成门，不能手写。附`EXPORT_CONTRACT.json`、最终commit、实际run链接、全部目标证据和仍单列的外部义务。用户不用再追问下一批施工包。
