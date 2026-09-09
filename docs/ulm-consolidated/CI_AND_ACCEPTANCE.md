# CI与验收：同一证据链，不制造新发布平台

## 本包已给出的可运行路径

本地只能执行Python、静态检查与包安装。完整参考命令：

```bash
python -B overlays/lmm/tools/ulm_consolidation/scripts/run_all.py --output work/local-reference
```

安装到LMM后改为`tools/ulm_consolidation/scripts/run_all.py`。runner保留原算法/测试源，BR脚本在scratch副本中执行，随后读回两文件并收集日志，不覆盖历史证据。数学探针与包装检查分开计数，不称独立法律实例数。

## GitHub Actions

合并到既有`.github/workflows/unified-math-v2-reference.yml`路径。普通pull_request触发；workflow_dispatch首次要求工作流存在默认分支。需要人工派发时可用：

```bash
gh workflow run unified-math-v2-reference.yml --ref YOUR_REVIEWED_BRANCH
```

不要在本机运行任何Lean/Elan/Lake命令。工作流在远端固定Lean v4.30.0和既有mathlib SHA；不`lake update`；不使用pull_request_target执行贡献代码。现有原工作流`lean-build.yml`不由安装器覆盖。

作业：
1. consolidated-python：原V2.1、BR、EXT/业务有限探针及本次保全检查；
2. lean-seeds：编译Consolidated.All，并从编译环境收集对应三个命名空间全部theorem及依赖、公理；核对84个保留源声明；
3. existing-jc-transport：固定JC产物的既有无密钥公共接口冒烟；
4. reference-gate：需要以上真实作业成功，准确匹配HEAD/tree/run/attempt；工件保持分目录，不平铺覆盖。

绿色语义固定为CONSOLIDATED_REFERENCE_CI_NOT_BUSINESS_ROOT_ACCEPTANCE。未完成ROOT06/08时，不存在一个可以诚实产生“根已证明”的快进按钮。本包没有以空theorem、assumed hRoot或硬编码true作替代。

## ROOT08将来怎样关闭

完成ROOT01–07之后，在原正式流水线中实际编译Root.lean；用类型化check确认定理具有已冻结独立语义和实际算法参数，检查依赖中没有隐藏根结论或额外未经接受的公理；运行实现精化和真实双文件/宿主集成。将定理、参数、编译及运行证据绑定同一组LMM/JC/Harness提交。

种子库存检查、All导入、图可达、日志格式测试不是这项验收。checker如果仍依赖Python/JSON/日期库的可信执行，应如实标明TCB及保证等级，不因为Lean里存在镜像算法就标kernelVerified。

## 证据轴及条件依赖

E01/T15仅对“经过真实外部验证的预测”声明必需；不是所有模型内数学证明的开工或接受前提。正式法律规则包需要适用法源与审核；合成业务根没有理由冒称提供了这些。134项逐条关闭，不以样例数/模板数冒充覆盖。

历史记录只读归档。本包的CURRENT_RUN说明本次实际执行与未执行；GitHub真实CI今后生成独立receipt，不修改旧日志伪造连续通过。

## 当前未执行事项

本次未在GitHub触发该工作流，未编译84项源声明，未执行新增JC/Harness生产根，未跑20套模型基准或真实胜率验证。CI YAML和Lean审计程序是已交付源文件，不能据此宣称远端可一次通过。
