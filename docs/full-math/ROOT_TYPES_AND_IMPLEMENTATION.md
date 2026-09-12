# 通用根：应当写成什么，不该写成什么

## A. 独立问题类型

```lean
-- 以下为施工接口设计，不是已存在并编译的声明。
structure LegalProblem where
  scope : ContextKey
  carriers : FiniteCarriers
  facts : FactStore
  rules : RuleProgram
  quantities : QuantityProgram
  model : ProbabilityProgram
  decision : DecisionProgram
  requirement : BusinessRequirement

def WF (i : LegalProblem) : Prop :=
  wellTyped i ∧ declaredCarriers i ∧ consistentScopes i ∧ inputsValid i

def Solutions (i : LegalProblem) : Set (JointWitness i) :=
  {w | IndependentBusinessSemantics i w}
```

WF只包含真正的结构、域、模型和来源前提，不包含`∀输出,输出正确`。概率模型有效性包含归一化、对应情景、正分母等；这些可以由输入checker反射取得。

## B. 先证明每一个实际解释器

```lean
theorem guard_reflects : exec (compile g) x = denote g x := ...
theorem argument_generation_exact : ... := ...
theorem extension_membership_reflects : ... := ...
theorem factor_elimination_exact : ... := ...
theorem interval_interpreter_covers : ... := ...
theorem numeric_certificate_sound : ... := ...
theorem burden_interpreter_reflects : ... := ...
theorem action_certificate_sound : ... := ...
theorem bytes_to_observation_refines : ... := ...
```

`...`在这里仅表示文档省略，不得原样当作源码交付。实际每个目标的公式、步骤、数据与反例见数学规格和57项卡。不能将上面九个缺失证明作为最终根的假设后说“组合已经完成”。

## C. 一般有限根必须真正处理任意合法输入

```lean
theorem generic_finite_root (i : LegalProblem) (h : WF i)
    (cert : FiniteCertificate i) (accepted : checkFinite i cert = true) :
    decodedResults cert = Solutions i := ...
```

checkFinite的范围应是对应有限程序片段；`decodedResults`与独立Solutions同一类型。候选全集来自独立carrier证明，不是运行时把found集合叫全集。部分搜索与精确搜索使用不同证书构造器。

## D. 连续/无限结果并不强制枚举

```lean
theorem symbolic_exact_root (i : SupportedSymbolicProblem)
    (rep : SymbolicRep i) (cert : ExactCertificate i rep)
    (h : checkSymbolic i rep cert = true) :
    denoteRep rep = Solutions i := ...
```

SupportedSymbolicProblem应明确支持的线性区间、多面体或符号关系。通用不可能自动求解任意关系，不等于禁止对可证片段精确求解。有限成员测试不能替代集合等价证书。

## E. 统计根不能消掉成功事件

```lean
theorem statistical_composition ... :
  P {data | ActualTarget data ∈ deliveredEnvelope data} ≥ 1 - delta := ...
```

前提包含实际所需交换性、适应性、参数族相容、数据分片等；必须对应实际计算。若系统按结果选择是否展示，另证条件覆盖或只声明联合坏事件界。

## F. 业务根不等于检查结果并列

对同一i、同一见证w，顺次证据与规则输出进入数量，数量和概率进入行动，受保护观察进入文件。三领域根分别实例化公共程序构造器及不同法律政策。

```lean
theorem civil_root (i : CivilProblem) ... : CivilRequirementSatisfied i ... := ...
theorem criminal_root (i : CriminalProblem) ... : CriminalRequirementSatisfied i ... := ...
theorem administrative_root (i : AdministrativeProblem) ... : AdministrativeRequirementSatisfied i ... := ...
```

刑事根不得用修改字段的民事本金根冒充。行政根不得把所有结果挤成同一个布尔标签。每个需求具体性质通过其实际数据构造实例化。

## G. 文书根

```lean
theorem document_delivery_root (i : LegalProblem) (d : ByteArray)
    ... (h : verifyDelivered i d = true) :
    parsedProtectedView d = requiredProtectedView i ... := ...
```

必须先取得字节到闭合语法的解析精化；超出受支持语法的自由语言不能自动受该定理保证。实际DOCX宿主运行后置，但数学仓内支持的字节/结构语法和对应测试这次完成。

## H. 不能满足完成门的替代物

```lean
-- 都不允许用来替换本轮根：
theorem demo : result 1000 300 = 700 := ...
theorem renamedGoal (h : OriginalGoal) : OriginalGoal := h
theorem wholeProgram (h1 : Reflects everything) (h2 : Covers everything) : ... := ...
```

第一条可以作为回归，第二条是重复假设，第三条仅是接口引理。它们只有在全部实际实例化证明已经交付时，才可以作为整个证明结构的一部分。

## 统一出口，不再形成七个孤岛

原C07必须作为统一业务语言的总出口：对任务/结果表示的不同构造器分情况，实际调用七个根中相应的算法正确性与观察定理，证明同一输入与中间见证下的总保证。C07的编译依赖必须连接七个根；EXT09实际连接民事、刑事、行政三根。这个依赖检查只防漏接，不能替代对共同见证和不同保证组合的证明。所有业务需求通过对应程序/政策实例进入此出口，不是另起各自独立的正确性定义。
