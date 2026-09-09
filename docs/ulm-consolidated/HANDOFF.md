# 施工Agent启动说明：唯一执行包

你收到的是V2.1至最近有限本金根审查的合并施工包。立即进入具体施工，不再先写一份无新证据的全项目评审。阅读顺序：MASTER_CONSTRUCTION.md → plans/DECISIONS.json → plans/TASKS.json → docs/ROOT_REFINEMENT.md。

## 当前任务

先执行ROOT01–ROOT08：独立JointSem与TaskSat、原始输入I0宿主保存、真实条件栈/枚举/本金checker反射、C/U概率与策略、双文件解析精化、实际根定理、JC/Harness接线和GitHub验收。现有check_business_bundle和JSON回读直接继承，不再按缺失重写。

不删除原T00–24、REV01–09、EXT01–09、57证明目标、134需求及X01–10。根数学施工不等待真实数据或全领域规则全部完成。后续按EXT与M族扩展，不建立另一内核。

## 安装

在待施工仓之外解压完整包。仅本地参考运行不需要仓库：

```bash
python -B tools/verify_package.py
python -B overlays/lmm/tools/ulm_consolidation/scripts/run_all.py --output work/local-reference
```

向真实仓写入前预览：

```bash
python INSTALL.py --role lmm --repo /path/to/legal-math-modeling
python INSTALL.py --role lmm --repo /path/to/legal-math-modeling --apply
python INSTALL.py --role jc --repo /path/to/juris-calculus --apply
python INSTALL.py --role harness --repo /path/to/legal-harness-repo --apply
```

LMM安装含源码/计划/参考CI；JC与Harness当前只安装分仓任务说明，不是假称已提供生产实现。原有未知修改不覆盖：检查差量后明确纳入审查版本，不使用强制覆盖。安装器不联网、不提交、不运行Lean，也不读取密钥。

安装到LMM后：

```bash
python -B tools/ulm_consolidation/scripts/validate_plan.py --repo-root .
python -B tools/ulm_consolidation/scripts/run_all.py --output work/consolidated-python
```

Lean/Elan/Lake只在GitHub Actions。沿用固定Lean4.30.0、mathlib SHA、现有参考workflow路径；普通PR运行。首次workflow_dispatch须文件已在默认分支。不要启动本地Lean来节省步骤。

## 必须保留的具体边界

- JC用jc-harness-local/1，create_local_client等既有入口；无自建密钥、无签章激活总闸。
- I0来自宿主任务确定时的状态，不是生成者输出expected；完整结构比较，不用approved_model_id名称代替来源。
- 原余额R、非负本金C、超付U区分；使用E[C]-E[U]守恒和对应事件，不套E[R]替E[C]。
- 独立Solutions/TaskSol/JointSem/ReadBoth不可用check的展开或已输出数据反定义。
- 完整、部分、外界、最紧、可达、统计覆盖和原生评测成绩分别表达。
- 已撤回空扩展/tee/已有时间分割/Finset等问题只保留防护，不重开。
- 根理论实例化、Python实际对应、真实文件、生产宿主、法律与经验验证分别关闭；定义/导入/计数不算完成。

## 交回结果格式

对每个实际完成的任务给：任务ID、改动文件/函数/定理、独立语义、所用前提、反例、实际命令/退出码、GitHub run与精确提交、保证范围、剩余事项。没运行就写NOT_RUN；测试跳过单列；法律审核和真实数据缺失不编造。当前84条只是源声明库存，不是已编译证明数量。不要改变任务含义来取得PASS。
