# juris-calculus 全量形式化验证实验运行报告

生成日期：2026-06-09  
Run ID：`20260609-214205-full-suite-all-verification`  
Run 目录：`D:\juris_calculus_verification_runs\07_report\runs\20260609-214205-full-suite-all-verification`  
状态：已执行完整实验套件，包含通过项、反例项、未确认项和项目测试夹具缺失项。

## 1. 基线与环境

已完成最新基线冻结、源码目录快照和依赖检查。

关键产物：

- `D:\juris_calculus_verification_runs\00_baseline\source_tree_hashes.json`
- `D:\juris_calculus_verification_runs\00_baseline\source_snapshot.zip`
- `D:\juris_calculus_verification_runs\00_baseline\source_snapshot.sha256`
- `D:\juris_calculus_verification_runs\00_baseline\dependency_status.json`

## 2. 结果总览

| 门类 | 结果 | 可信度标签 | 证据 |
| --- | --- | --- | --- |
| Python/Hypothesis 性质测试 | PASS，6 passed | `TESTED_PROPERTY` | `01_property_tests/pytest_core_properties_final.log` |
| graph similarity 反例搜索 | FOUND | `REFUTED` for blanket strict-reflexivity claim | `01_property_tests/counterexample_graph_reflexivity.json` |
| Z3 graph range | PASS，反例查询 `unsat` | `SMT_PROVED_FINITE` / abstract real domain | `02_smt_z3/z3_core_checks.log` |
| Z3 finite Galois sanity | PASS，0 violations | `SMT_PROVED_FINITE` / finite enumeration | `02_smt_z3/z3_core_checks.log` |
| CrossHair graph contract | INCONCLUSIVE，Not confirmed | `INCONCLUSIVE` | `03_crosshair/crosshair_graph_similarity.log` |
| TLA+ oscillation guard skeleton | PASS，No error found | `MODEL_CHECKED` / bounded skeleton | `04_tla/tlc_oscillation_guard_final.log` |
| Alloy relation disjoint skeleton | PASS，UNSAT | `MODEL_CHECKED` / bounded Alloy scope | `05_alloy/alloy_relations.log` |
| Lean Galois skeleton | PASS，exit 0 | `LEAN_PROVED_SKELETON` | `06_lean/lean_galois_skeleton_final2.log` |
| Dafny graph range | PASS，1 verified, 0 errors | `SMT_PROVED` for Dafny model | `08_dafny/dafny_graph_similarity_range_final.log` |
| Core py_compile | PASS | `BUILD_CHECK` | `09_project_regression/py_compile_core.log` |
| Project unit tests | PASS，32 passed | `REGRESSION_PASS` | `09_project_regression/pytest_project_unit_tests.log` |
| Project full tests | FAIL at collection | `BLOCKED_BY_MISSING_FIXTURE` | missing `configs/en_US/rules.yaml` |

## 3. 关键发现

### 3.1 graph similarity 严格自反性被反驳

当前实现对空特征集合采取保守语义：`jaccard = 0.0`。因此：

```text
G = (v=1, e=0, features=empty set)
sim(G, G) = 0.4
```

这反驳任何“对所有图输入 `sim(G,G)=1`”的强定理。它不一定是实现 bug，因为这是审计后选择的保守空特征语义；但报告必须避免声明 blanket strict reflexivity。

反例：`01_property_tests/counterexample_graph_reflexivity.json`

### 3.2 CrossHair 未确认

CrossHair 对 graph similarity contract 返回 `Not confirmed`。这不能算失败，也不能算证明，应记录为 `INCONCLUSIVE`。

### 3.3 项目全量 pytest 受缺失配置阻断

命令：

```powershell
python -m pytest tests -q
```

结果：collection 阶段失败，原因：

```text
FileNotFoundError: configs/en_US/rules.yaml
```

单元测试子集通过：`32 passed in 2.12s`。

## 4. 算法与源码改进记录

算法层记录目录：

`D:\juris_calculus_verification_runs\07_report\algorithm_improvements`

源码层记录目录：

`D:\juris_calculus_verification_runs\07_report\source_code_improvements`

本轮未修改 JC 运行源码。实验脚本只写入 run 目录。

## 5. 记录校验

记录完整性校验：

`D:\juris_calculus_verification_runs\07_report\record_validation.json`

当前结果为 `[]`，表示没有发现记录结构问题。

## 6. 下一步建议

1. 补齐或修复 `configs/en_US/rules.yaml`，使项目全量 pytest 可收集。
2. 将 graph similarity 的“空特征自反性不成立”写入 theory 定理降级说明。
3. 将 Lean skeleton 扩展为真正的 finite preorder / powerset Galois connection。
4. 将 TLA+ skeleton 扩展到完整 evaluator 状态机。
5. 对 CrossHair 未确认项改用更简单 contract 或转为 Z3 证明。
