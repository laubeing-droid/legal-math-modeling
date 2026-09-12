# 代码复用：不要重建，补齐证明与缺失算法

本包`reference_retained`逐文件保留旧数学实现。它是开发参考，不是最新生产源码快照；安装器不会将它覆盖进仓库。当前仓库已有同功能代码时，以当前代码为实现对象补证明，使用原测试作回归。

| 任务 | 可复用的现有数学参考 |
|---|---|
| 有限规则/树、原子闭包 | `unified_math_v2/unified/arguments.py` |
| 攻击扩展、有限/符号证书 | `unified_math_v2/v21/checker.py`；`reference/core.py` |
| 主体与来源/授权 | `v21/context.py`、`v21/authority.py`、`v21/model_binding.py` |
| 有限BN与VE | `reference/core.py` 的BayesNet、Factor、条件化与归一化 |
| Dirichlet与Beta层级模型 | `reference/core.py`、`unified/win_model.py` |
| PAV与评价/数据隔离 | `unified/win_model.py`；本包新增独立PAV KKT检查参考 |
| 数量、区间、LP、PSD、投影 | `unified/precision.py`、`reference/core.py` |
| 证明责任与阶段 | `unified/burdens.py`、`v21/law_slices.py` |
| 联合样例与源约束 | `v21/joint.py`、`v21/bridge.py` |
| 实际双文件与I0 | 当前仓`tools/business_relations/reference/`、`tools/ulm_repair/` |
| 新增数学参考 | 本包`extended_algorithms.py`：Horn支持反链及独立检查、联合事件概率、投影约化、保形分位数、下注路径、PAV/KKT、有限DP/Bellman检查、共享模型稳健值、有限SCM、有限机制检查 |

这些已有Python函数不是全量Lean证明。源码与当前目标不一致时，先明确算法改动和语义改动，再补对应证明；不得把较弱旧定理贴到更强新代码上。

可以选择“Python产生候选/证书，Lean认证checker验证”的实现路线。这样不必声称Python解释器整体已形式验证，但要证明实际被运行的认证checker与独立语义一致，并保留编码/字节映射的真实边界。对本包要求形式化的字节语法，不能永久以一次常数交叉测试代替。
