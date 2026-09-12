# 实现绑定和完成证据

## 1. 两个不同的工作

`Contracts`定义按本包公式要求的命题；`Acceptance`为这些命题提供实际证明。前者不是`check=true`，也不由求解器输出反向定义；后者不能只是定义、假设、计数或测试。

每个目标允许复用多个已有模块；不强制拆成217个源码文件。一个通用定理可服务多个业务需求，但每个需求仍要证明参数和观察映射正确。

`tools/full_math/spec/BINDINGS.json`填写形式如下（只示意字段，不是可以直接宣称已完成的记录）：

```json
{
  "id": "TARGET:F12",
  "theorem": "JurisLean.FullMath.Acceptance.target_F12",
  "contract": "JurisLean.FullMath.Contracts.target_F12",
  "proof_mode": "KERNEL_CONTRACT_PROOF",
  "generality": "PARAMETRIC",
  "formal_scope": "任意结构良好、独立载体完整的有限程序；不是固定两个情景",
  "independent_semantics": "引用具体独立Sol与WF定义",
  "algorithm": "实际枚举器和独立证书检查器的路径及函数",
  "observation_contract": "精确成员与全域覆盖，保留主体和版本",
  "external_assumptions": "具体法律规则适用作为独立准入输入；不含求解器正确这一循环前提",
  "proof_sources": ["proofs/lean/juris_lean/JurisLean/FullMath/Acceptance.lean"],
  "implementation_sources": ["tools/full_math/implementation/finite.py"],
  "test_ids": ["tools/full_math/implementation_tests::test_finite.py::TestFinite::test_arbitrary_domains"],
  "negative_test_ids": ["tools/full_math/implementation_tests::test_finite.py::TestFinite::test_omitted_member"],
  "semantic_links": ["JurisLean.FullMath.Finite.all_inputs_exact"]
}
```

测试ID以实际运行器输出为准。不得手写一个不存在的测试名称。完整实施测试通过pytest运行，兼容其夹具和unittest用例；包内自检仍用unittest。每项测试的实际nodeid保存并加来源目录前缀，不根据正则猜通过数量；原仓pytest门也继续保留。

## 2. 生成器做什么

全部绑定齐全后，生成器为每项目标写出：

```lean
theorem full_math_typecheck_000 : JurisLean.FullMath.Contracts.target_F01 :=
  JurisLean.FullMath.Acceptance.target_F01
```

这由Lean检查精确的预期类型，而不是仅查名字。随后从实际编译环境提取类型、公理和证明依赖。

生成器不创造这些目标的证明。217项缺一项就返回具体缺项，不输出用`axiom`补成的“完整文件”。

## 3. 通用性怎样验

根类型必须对所支持输入参数量化，不得含“输入恰为selectedInput”。正常测试要覆盖不止一个金额、不同争点数量、多个付款、空可行域和不同法律结果类型；反例要覆盖丢情景、错范围、非法行动与文件改写。

机器程序能检查类型赋值、登记、来源与运行完整性；不能仅从定理名判断自然语言需求真的被完整表达。因此，执行者要对Contracts逐项做一次独立上下文核对，重点查：

- `True`或恒假前提让结论空洞；
- 把“checker健全/全部结果完整”作为未实例化的输入前提；
- 改变原独立域，使遗漏对象不再属于目标；
- 以“有限”把连续符号表示排除；
- 把全部输入约束成一个示例；
- 仅合取多个模块的结论而没有共享见证。

这是对当前公式的落实核对，不是要求用户再审批一遍，也不是引入新审查平台。

## 4. 何时真的收工

全量门先核对所有强制ID。随后核对同一commit/tree/run/attempt、全部目标已编译为定理、预期类型通过、依赖到具体语义组件、来源文件与实际测试均在本次证据中。原先已经通过的示例可复用，但不能凭它们直接填满新表。

最终状态由CI计算，不能通过修改`BINDINGS.json.status`决定。对应外部义务将同时出现在回执中，不被数学完成冲掉。

## 统一出口，不再形成七个孤岛

原C07必须作为统一业务语言的总出口：对任务/结果表示的不同构造器分情况，实际调用七个根中相应的算法正确性与观察定理，证明同一输入与中间见证下的总保证。C07的编译依赖必须连接七个根；EXT09实际连接民事、刑事、行政三根。这个依赖检查只防漏接，不能替代对共同见证和不同保证组合的证明。所有业务需求通过对应程序/政策实例进入此出口，不是另起各自独立的正确性定义。
