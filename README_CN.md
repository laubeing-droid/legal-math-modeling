# Legal Math Modeling

`juris-calculus` 的数学配套仓库。

这个仓库现在不再对外描述成“大量法律 AI 数学实验的合集”，而是明确收口为一个有发布边界的形式化配套仓：

- `formal-core-v1` 已完成仓库级发布封板
- 已发布核心只包括：
  有限单调迭代内核、Dung grounded 不动点层、有限 Horn 闭包层
- Banach 不属于已发布核心，当前只保留为归档研究轨道
- 常量校准、隐私保证、诉讼自动化都不在本仓的已完成声明范围内

## 当前状态

### 已发布事实

- 公共分支模型：仅保留 `master`
- 当前仓库头部：`cde13f0`
- 最近一次 GitHub 全量 clean rebuild 证据提交：`4b415b8`
- Lean 源码守卫结果：
  `0 sorry / 0 admit / 0 custom axiom / 0 theorem : True`
- `AxiomAudit` 已作为 released core 的可复现审计入口保留

### 当前允许的对外口径

有限单调系统、Dung grounded 不动点层、有限 Horn 闭包层已经具备可复现的 Lean 构建结果和可复现的 axiom audit 结果；仓库级 `formal-core-v1` 发布门已关闭。

### 当前不允许的口径

- 整个 `juris-calculus` Python 实现已经被 Lean 完整证明
- Banach 固定点闭环已经完成
- 差分隐私保证已经建立
- 38 个常量已经完成真实数据校准
- 诉讼自动化和研究自动化已经在本仓完成

## 仓库职责边界

本仓负责：

- 形式规格
- Lean 证明工件
- theorem manifest 与 proof ledger
- 建模论文与审计文档
- 机器可核验的发布证据

本仓不负责：

- 生产运行时
- 多任务研究编排
- 诉讼批处理执行

对应运行仓分别是：

- [`juris-calculus`](https://github.com/laubeing-droid/juris-calculus)
- [`deli-autoresearch`](https://github.com/laubeing-droid/deli-autoresearch)

当前跨仓对齐头部：

| 仓库 | 分支 | HEAD |
| --- | --- | --- |
| `legal-math-modeling` | `master` | `cde13f0` |
| `juris-calculus` | `main` | `c18b478` |
| `deli-autoresearch` | `main` | `b35dbb1` |

## 已发布形式化核心

发布核心分成三层：

1. 有限单调迭代通用内核
2. Dung grounded 不动点层
3. 有限 Horn 闭包层

当前计数口径固定为：

- `formal_core_module_theorems = 39`
- `extended_core_theorems = 43`
- `supporting_results = 32`
- `total_kernel_checked_results = 75`

机器可读真相源是：

- [`docs/formal-release/theorem_manifest.json`](docs/formal-release/theorem_manifest.json)

## 公理边界

当前 release boundary 重点审计对象：

1. `FiniteMonotoneSystem.exists_fixpoint_le_card`
2. `FiniteMonotoneSystem.fixed_at_card`
3. `DungAAF.grounded_is_least_fixed_point`
4. `HornSystem.horn_completeness`
5. `HornSystem.horn_result_is_minimal_model`
6. `weightedSupDist_complete`

当前观测到的依赖仅为：

- `propext`
- `Classical.choice`
- `Quot.sound`

已发布核心边界内没有项目自定义 axiom。

## Banach 状态

Banach 不属于 `formal-core-v1`。

当前真实状态：

- Banach 相关工作已归档
- 公共仓库不再保留活跃 Banach 分支
- 当前公开状态是 `UNPROVED_TRACK_B`

当前明确不应宣称：

- Banach 已经闭环
- 加权收缩已在 Lean 中完整证明
- Banach 已经并入 released formal core

归档 tag：

- `archive/banach-track-b-d23e8f2`
- `archive/track-c-prod-f43e273`

## 仓库结构

```text
legal-math-modeling/
├── README.md
├── README_CN.md
├── paper/
├── theory/
├── proofs/
│   ├── engineering_proof_artifacts/
│   ├── strict_proof_baseline/
│   └── lean/juris_lean/
├── verification/
├── data/
└── docs/
    ├── formal-release/
    ├── final-closure/
    ├── audit/
    ├── modeling/
    └── history/
```

关键目录：

- `proofs/lean/juris_lean/`：Lean 形式化工作区
- `docs/formal-release/`：当前发布边界文件
- `docs/final-closure/`：结案与收口摘要
- `docs/audit/`：定理矩阵、proof ledger、反例注册表
- `docs/history/`：早期阶段与过时声明的归档说明

## 推荐阅读顺序

如果你要判断“这个仓库现在到底完成到了哪一步”，按下面顺序读：

1. [`docs/formal-release/FORMAL_RELEASE_REPORT.md`](docs/formal-release/FORMAL_RELEASE_REPORT.md)
2. [`docs/formal-release/FORBIDDEN_CLAIMS.md`](docs/formal-release/FORBIDDEN_CLAIMS.md)
3. [`docs/final-closure/final-report.md`](docs/final-closure/final-report.md)
4. [`docs/audit/theorem_status_matrix.md`](docs/audit/theorem_status_matrix.md)

`docs/history/` 只作为历史归档使用。某些旧文件会记录早期阶段的计数、目标或口径，不代表当前 release claim。

## 快速开始

```bash
git clone https://github.com/laubeing-droid/legal-math-modeling.git
cd legal-math-modeling
pip install -r requirements.txt
python verification/verification_engine.py
cd proofs/lean/juris_lean && lake build
```

如果你只想复核 released formal core：

```bash
cd proofs/lean/juris_lean
lake build
lake build +JurisLean.AxiomAudit
```

## 文档导航

- `paper/main.md`：主论文
- `docs/formal-release/`：当前发布边界与允许声明
- `docs/audit/`：审计链与 theorem ledger
- `docs/history/`：历史阶段归档

## 许可

[CC BY 4.0](LICENSE)
