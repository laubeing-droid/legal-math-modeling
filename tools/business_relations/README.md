> 来源保留说明：下文为历史证明链正文；其中“16项草稿、55项测试、仅本金文本回读”是较早阶段记录。最新代码已是24项Lean草稿、双文件根参考实现；本包新运行结果见evidence/CURRENT_RUN.json。独立JointSem/ReadBoth根精化仍未完成。当前总要求以docs/ulm-consolidated/MASTER_CONSTRUCTION.md为准。

# 七轴业务关系：双文件总检查器参考增量

这是原有限本金参考包的非破坏修订副本，不是另一套JC生产内核。

本轮Python实测：原55项保留，新增30项，共85项通过。`evidence/reference_result.json`、`python_tests.log`、`reference_run.log`由同一运行生成。

```bash
python -B ci/run_reference.py
```

执行内容：固定合成spec与DecisionInputs → 保存独立请求快照 → 求解 → Analytics → 写两份实际文件 → 重新读取字节 → 统一根检查。

新增：
- `reference/delivery_bundle.py`：输入快照、固定双文件需求、独立JSON读回和统一根检查器。
- `tests/test_delivery_bundle.py`：30项增量测试。
- `lean/BusinessRelationsDelta.lean`：8项超付与clipped余额桥接草稿，原16项原样保留。
- `ci/run_reference.py`：同次证据生成、文件读回失败不报完成。

## 输入边界

`InputSnapshot`必须由宿主在确定任务输入时建立并保存，不能由证书提供方随输出替换。这是内容绑定，不是机构批准、模型训练验证或新增签章。

已有`ContextKey.model_version`复用，不新增重复model_version或approved_model_id。不要求任何新密钥或机构审批才能运行合成/用户假设情景。

## 保证范围

只验证指定有限合成条件模型、精确本金/超付残差/阈值事件/行动格与闭合UTF-8、JSON文件。任意自由文本、DOCX、PDF、法律依据真值、真实预测和JC集成均不在本次已完成范围。

24项Lean声明都是SOURCE_DRAFT_CI_NOT_RUN。实际Python检查器出现不等于Lean根定理已完成；CI步骤见`ci/INTEGRATION.md`。本地不执行Lean、Elan、Lake。

原证据只读保留在`original_evidence/`，其中54/55的不同步已由审查确认，不充当本轮证据。原134项和X01—X10未更改，仍待逐项实例化。
