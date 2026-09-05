# Legal Math Modeling

`legal-math-modeling` 是一个证据范围受限的法律推理形式化规范仓库。Lean 证明的是仓库中明确写出的数学命题，不等于证明整个法律系统、生产运行时或具体法律结论正确。

## 已验证快照

本文档所指向的最新不可变 full-release 证据是 GitHub Actions [run 33946211096](https://github.com/laubeing-droid/legal-math-modeling/actions/runs/33946211096)，attempt 1；subject commit 为 `2a1d33df353a005dffc5d8b95faa591524e2636e`，tree 为 `c7525f767b43c7e8a663a4a9702f64cdea78b979`。

该 run 的 97 个 job 全部成功，内容级证据记录为：

- 证书清单含 91 个 Lean 源模块、452 个 theorem 声明；
- clean build 完成 2,993 个构建任务；
- ULM 全定理审计 145 项、核心组合审计 27 项，仅报告 `propext`、`Classical.choice`、`Quot.sound`；
- Python 测试 131/131 通过；
- 受控 checker 输入变异 46/46 被杀死；
- 跨仓 runtime-refinement fixtures 3/3 通过；
- forbidden claim 命中为 0；
- 证书状态为 `RELEASE_PASS_PENDING_INDEPENDENT_VERIFICATION`，独立验证器 verdict 为 `VERIFIED_PENDING_RELEASE_GATE`，final gate 成功。

这里原样保留证书管线的分阶段状态名。final gate 只闭合该 subject 的 release 管线，不自动覆盖后续 commit。GitHub artifact 有保留期限，run 页面是证据定位点，不是永久存档。

## 模型范围

仓库包括：

- 11 类型的 v1 兼容规范与 48 类型的分层 v2 registry；
- 义务、禁止、许可、构成四种道义模态；
- 合同违约、事实采纳、许可、优先级、翻译、证书与运行时 refinement 的有界契约；
- ULM01–ULM16 Lean 理论及显式公理审计入口；
- Python checker、release 证书生成器、真实受控变异 fixtures 与跨仓 receipt 验证；
- 含公式的[论文全集](paper/README.md)。

## 证据边界

证据分层解释：

1. Lean 源码与 CI elaboration 只支持具名形式命题。
2. Axiom audit 用于披露依赖，本身不替代证明。
3. Python 测试、变异测试和 runtime receipt 只支持各自 fixtures 内的工程行为。
4. 证书与独立验证器把全部证据绑定到同一 subject commit 和 tree。
5. 法律依据、材料完整性、经验有效性以及真实案件结论的正确性，除非另有证据，否则不属于形式证书范围。

UNKNOWN、SKIP、TIMEOUT、UNAVAILABLE、subject 不一致和过期证据一律 fail-closed。

## 验证方式

本地只允许运行 Python 与静态守卫：

```bash
python -m pytest -q -p no:cacheprovider
python scripts/scan_lean_guards.py proofs/lean/juris_lean/JurisLean
```

本仓库禁止在本地运行 Lean、Elan 或 Lake。GitHub Actions 是唯一 Lean 权威：

```bash
gh workflow run lean-build.yml --ref <commit-or-branch> -f mode=full-release
```

不能只看 workflow 绿色。必须核对同一 `head_sha` 的证书 subject/status、verifier verdict、公理输出、claim audit、mutation report、runtime receipt 和 final gate。

## 文档入口

- [文档总索引](docs/INDEX.md)
- [不可变 release 证据](docs/formal-release/FINAL_FORMAL_RELEASE_REPORT.md)
- [release 协议](docs/formal-release/FORMAL_RELEASE_REPORT.md)
- [允许声明](docs/formal-release/ALLOWED_CLAIMS.md)与[禁止声明](docs/formal-release/FORBIDDEN_CLAIMS.md)
- [Canonical schema](docs/spec/canonical_legal_schema.md)
- [DDL minimal core](docs/spec/ddl_minimal_core.md)
- [Horn-to-AAF contract](docs/spec/horn_to_aaf_contract.md)
- [Certificate checker boundary](docs/spec/certificate_checker_boundary.md)
- [公开/私有边界](docs/disclosure/PUBLIC_PRIVATE_BOUNDARY.md)
- [论文全集](paper/README.md)

## 目录

```text
docs/          当前文档、release 证据与有界规范
paper/         已重写的含公式论文与 LaTeX 源文件
proofs/        Lean 源码和工程证明产物
runtime/       机器可读 refinement fixtures
scripts/       审计、证书、变异和 CI 工具
tests/         Python 测试
theory/        可执行 schema 与语义模块
verification/  验证辅助程序
reports/       历史生成报告，不是当前权威
```

本仓库采用 [CC BY 4.0](LICENSE)。引用时必须写明实际使用的 commit，格式见 [CITATION.cff](CITATION.cff)。
