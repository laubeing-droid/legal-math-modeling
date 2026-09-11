# 并入现有GitHub CI，不另设发布权威

本文件是安装/接入说明；本轮未执行以下远端步骤。

## 放置位置（提交前由施工者处理）

- 本包的 `reference/`、`tests/`、`data/`、`ci/` → `tools/business_relations/` 下相应路径。
- `lean/BusinessRelations.lean` → `proofs/lean/juris_lean/JurisLean/BusinessRelations.lean`。
- `lean/Audit.lean` → `proofs/lean/juris_lean/JurisLean/BusinessRelationsAudit.lean`。
- `lean/DECLARATIONS.json` → `tools/business_relations/lean/DECLARATIONS.json`。
- 原根 `JurisLean.lean`增加实际 import，并将新命名空间纳入原编译环境声明审计。
- `evidence/`、`examples/` 为生成输出，不作为证明源码权威；在该工具目录下使用本包.gitignore。

Python参考中的 `context.py` 是V2.1交付稿的精确副本。参考可独立运行；生产接入须进口项目唯一ContextKey，不得长期维护两个可漂移定义。源文件哈希记录在本包evidence/input_binding.json。

## Python

在仓库根运行：

```bash
python -B tools/business_relations/ci/run_reference.py
```

只使用标准库，不需要模型API、真实卷宗、机构密钥或签名。不是胜率训练或模型评测。

## Lean（只在GitHub Actions）

使用既有Lean作业的依赖安装步骤、`lean-toolchain`与`lake-manifest.json`，不另行拉latest mathlib或`lake update`。本轮实际核对工具链为 `leanprover/lean4:v4.30.0`。

下列步骤添加到已有工作流中，紧接其正常依赖准备之后。`STEPS.yml`是步骤片段，不是独立workflow，不声称只拷贝这一文件就拥有完整运行环境。

1. 真实执行Python测试，失败传播。
2. 真实 `lake build JurisLean.BusinessRelations`。
3. 真实执行 `BusinessRelationsAudit.lean` 的 `#print axioms`。
4. 核对16条显式种子的实际公理输出，只允许现有公理集合。
5. 仍须运行项目既有编译环境全声明审计；本包打印清单不是其替代。
6. 将产物放入同一head_sha的原始工件；不得将参考作业绿色升级成JC/法源/真实经验验证通过。

需要另行关闭：栈编译器的Lean精化、Python→Lean输入编解码、源材料→规范解释、日期/字节库可信边界、正式DOCX读回、真实机构来源和其他134项业务实例。源代码中若某通用定理带有局部健全性/覆盖/适当性前提，应给出真正实例，而不是去掉前提名称后宣称已证明全部业务。


## 本轮增量接入
保留原 BusinessRelations.lean 不变；另复制 lean/BusinessRelationsDelta.lean 到
proofs/lean/juris_lean/JurisLean/BusinessRelationsDelta.lean。
Audit.lean 按本目录原安装约定复制为 BusinessRelationsAudit.lean；本轮清单为24项草稿声明。
更新 tools/business_relations/reference/delivery_bundle.py、tests/test_delivery_bundle.py 及 ci/run_reference.py。
已有 workflow 的步骤改为 build 新 Delta 模块；保留全仓编译环境公理检查和原最终门。
不在本地执行 Lean、Elan、Lake。不推定本轮种子能够编译；必须取真实CI结果。
Python 根检查器出现，不表示其端到端 Lean 健全性或生产来源边界已经被证明。
