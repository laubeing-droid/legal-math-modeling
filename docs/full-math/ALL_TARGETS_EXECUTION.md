# 57项目标：一次性实施卡

这不是后续分批交付目录。执行者从完整清单开工，一直推进到全量门通过。每个原ID保留，已有证明复用，未证部分不得用示范替代。

## F01｜总见证语义与来源类型

**原目标：** Φ(v,c,I,w) 独立定义；每种输出由相应指称解释，而不是由运行status定义。
**当前执行含义：** Φ(v,c,I,w) 独立定义；每种输出由相应指称解释，而不是由运行status定义。
**数学细节：** `MATHEMATICS_SPEC.md` 第1节。
**实现与证明位置：** `proofs/lean/juris_lean/JurisLean/FullMath/Core/BusinessSemantics.lean`；优先复用旧 `unified/contract.py` 与已有ULM定理，不平行重建。

**证明施工：**
1. 将法域、两个时间、争点、阶段、假设、解释政策、单位、模型目标定义为独立类型/索引。
2. 定义规范关系、概率函数、可行域、效用和跨层join谓词；禁止从最终输出反推语义。
3. 列出环境授权/真实数据/法律解释的假设，证明程序只使用声明的索引和来源。
4. 先完成带索引业务输入与见证，再定义全部组件关系。
5. 法域、版本、争点、事实地位和数量类型必须在语义中实际使用；不得仅存在于注释。

**必须导出：** `JurisLean.FullMath.Contracts.target_F01` 与 `JurisLean.FullMath.Acceptance.target_F01`，以Lean赋值检查准确合同类型。
**执行证据：** 当前源文件、实际算法/检查器入口、正常与反例测试、具体类型与依赖、公理审计、同次GitHub运行。
**不能据此收工：** 文件存在、函数返回True、只import、只固定数字、把反射前提交给调用者、把注册范围自行缩小。

## F02｜绑定与不混案

**原目标：** 两个组件可组合 ⇒ request/law/model/scenario/semantic-scope 相同。
**当前执行含义：** 两个组件可组合 ⇒ request/law/model/scenario/semantic-scope 相同。
**数学细节：** `MATHEMATICS_SPEC.md` 第1节。
**实现与证明位置：** `proofs/lean/juris_lean/JurisLean/FullMath/Core/IdentityCodec.lean`；优先复用旧 `unified/contract.py` 与已有ULM定理，不平行重建。

**证明施工：**
1. 证明结构化序列化对被支持规范值的往返一致；JSON字符串拼接不可充当结构单射。
2. 对索引相等证明各投影相同；对任一索引不同构造拒绝分支。
3. 哈希定位额外依赖抗碰撞/来源验证，不能把数学身份简化成未经验证的字符串。
4. 原I0的全内容与命题相符；新任务合法但不可继承旧输入声明。
5. 证明无损编码；哈希只定位；查询输出按同一来源和事件时点绑定。

**必须导出：** `JurisLean.FullMath.Contracts.target_F02` 与 `JurisLean.FullMath.Acceptance.target_F02`，以Lean赋值检查准确合同类型。
**执行证据：** 当前源文件、实际算法/检查器入口、正常与反例测试、具体类型与依赖、公理审计、同次GitHub运行。
**不能据此收工：** 文件存在、函数返回True、只import、只固定数字、把反射前提交给调用者、把注册范围自行缩小。

## F03｜严格前提准入

**原目标：** Prediction/Hypothesis 不可成为无条件 VerifiedPremise。
**当前执行含义：** Prediction/Hypothesis 不可成为无条件 VerifiedPremise。
**数学细节：** `MATHEMATICS_SPEC.md` 第1节。
**实现与证明位置：** `proofs/lean/juris_lean/JurisLean/FullMath/Evidence/Admission.lean`；优先复用旧 `unified/burdens.py` 与已有ULM定理，不平行重建。

**证明施工：**
1. 分离输入类别、用途中权、来源检查、授权确认、争议状态。
2. 枚举所有构造器；证明假设/预测分支不调用严格准入构造器。
3. 证明审核主体在当前法域/争点/阶段确有授权由现有可信适配器提供，非空名字不是授权证明。
4. 采用已有准入对象；为所有来源构造器分情况证明。
5. 机构输入使用范围由外部事实给出；不得以一个字符串被列入白名单代替适用。

**必须导出：** `JurisLean.FullMath.Contracts.target_F03` 与 `JurisLean.FullMath.Acceptance.target_F03`，以Lean赋值检查准确合同类型。
**执行证据：** 当前源文件、实际算法/检查器入口、正常与反例测试、具体类型与依赖、公理审计、同次GitHub运行。
**不能据此收工：** 文件存在、函数返回True、只import、只固定数字、把反射前提交给调用者、把注册范围自行缩小。

## F04｜假设与证据污染不消失

**原目标：** dependencies(conclusion) 包含实际使用的全部假设/来源依赖。
**当前执行含义：** dependencies(conclusion) 包含实际使用的全部假设/来源依赖。
**数学细节：** `MATHEMATICS_SPEC.md` 第2节。
**实现与证明位置：** `proofs/lean/juris_lean/JurisLean/FullMath/Evidence/Provenance.lean`；优先复用旧 `unified/arguments.py; unified/taint.py` 与已有ULM定理，不平行重建。

**证明施工：**
1. 对推导树归纳：叶节点保留origin；规则节点取实际子证明依赖并集。
2. 证明任何展示、转换、金额计算和概率特征保留该依赖投影；不用未读字段污染其他无关结果。
3. 对证据排除/变化求依赖闭包，证明闭包外可复用、闭包内必须失效；循环依赖用有限单调迭代终止。
4. 依赖记录须等于或健全覆盖实际使用子见证；同源副本保留共同事件。
5. 反事实改变未使用内容不得改变纯计算结果，已用来源被排除必须使相应证明失效。

**必须导出：** `JurisLean.FullMath.Contracts.target_F04` 与 `JurisLean.FullMath.Acceptance.target_F04`，以Lean赋值检查准确合同类型。
**执行证据：** 当前源文件、实际算法/检查器入口、正常与反例测试、具体类型与依赖、公理审计、同次GitHub运行。
**不能据此收工：** 文件存在、函数返回True、只import、只固定数字、把反射前提交给调用者、把注册范围自行缩小。

## F05｜有限Horn最小不动点与终止

**原目标：** TH^|A|(∅) 是有限正Horn的最小闭包。
**当前执行含义：** TH^|A|(∅) 是有限正Horn的最小闭包。
**数学细节：** `MATHEMATICS_SPEC.md` 第2节。
**实现与证明位置：** `proofs/lean/juris_lean/JurisLean/FullMath/Logic/HornFixpoint.lean`；优先复用旧 `existing HornFixedPoint; unified/arguments.py` 与已有ULM定理，不平行重建。

**证明施工：**
1. 复用既有TH单调与域包含证明，不重写核心。
2. 证明从底部递增，严格增长增加基数，至多|A|次；证明对任意前不动点的包含关系。
3. 把实际规则/事实编译至该形式对象的映射单独证明，不将固定测试当转换证明。
4. 参考工作队列与数学T迭代双向精化。
5. 载体增大改变输入范围；不能复用只对旧域成立的完整声明。

**必须导出：** `JurisLean.FullMath.Contracts.target_F05` 与 `JurisLean.FullMath.Acceptance.target_F05`，以Lean赋值检查准确合同类型。
**执行证据：** 当前源文件、实际算法/检查器入口、正常与反例测试、具体类型与依赖、公理审计、同次GitHub运行。
**不能据此收工：** 文件存在、函数返回True、只import、只固定数字、把反射前提交给调用者、把注册范围自行缩小。

## F06｜有限高度论证生成健全

**原目标：** a∈Generate_d ⇒ WellFormed(a) ∧ height(a)≤d。
**当前执行含义：** a∈Generate_d ⇒ WellFormed(a) ∧ height(a)≤d。
**数学细节：** `MATHEMATICS_SPEC.md` 第3节。
**实现与证明位置：** `proofs/lean/juris_lean/JurisLean/FullMath/Logic/ArgumentConstruction.lean`；优先复用旧 `unified/arguments.py` 与已有ULM定理，不平行重建。

**证明施工：**
1. 独立定义有来源叶、合法规则节点、子结论与前提匹配及上下文一致性。
2. 按生成深度归纳；规则笛卡儿子组合逐个应用归纳假设。
3. 保留同结论不同支持树，证明依赖并集及子论证集合正确。
4. 按生成深度证明每个孩子已合法，规则前提与孩子结论逐个对齐。
5. 不同支持树与同结论必须分离。

**必须导出：** `JurisLean.FullMath.Contracts.target_F06` 与 `JurisLean.FullMath.Acceptance.target_F06`，以Lean赋值检查准确合同类型。
**执行证据：** 当前源文件、实际算法/检查器入口、正常与反例测试、具体类型与依赖、公理审计、同次GitHub运行。
**不能据此收工：** 文件存在、函数返回True、只import、只固定数字、把反射前提交给调用者、把注册范围自行缩小。

## F07｜有限高度论证生成完备

**原目标：** WellFormed(a) ∧ height(a)≤d ⇒ a∈Generate_d。
**当前执行含义：** WellFormed(a) ∧ height(a)≤d ⇒ a∈Generate_d。
**数学细节：** `MATHEMATICS_SPEC.md` 第3节。
**实现与证明位置：** `proofs/lean/juris_lean/JurisLean/FullMath/Logic/ArgumentConstruction.lean`；优先复用旧 `unified/arguments.py` 与已有ULM定理，不平行重建。

**证明施工：**
1. 对独立语法中的树结构归纳，而不是对Generate输出归纳。
2. 由每个孩子高度≤d-1和归纳假设，证明完整规则组合包含该树。
3. 证明所有叶/规则ID覆盖所声明有限载体；完整性仅限此d，不升级到无界论证。
4. 从独立WellFormed树出发结构归纳，不能对生成表归纳后声称完备。
5. 预算不是语义深度；预算未足只影响pending。

**必须导出：** `JurisLean.FullMath.Contracts.target_F07` 与 `JurisLean.FullMath.Acceptance.target_F07`，以Lean赋值检查准确合同类型。
**执行证据：** 当前源文件、实际算法/检查器入口、正常与反例测试、具体类型与依赖、公理审计、同次GitHub运行。
**不能据此收工：** 文件存在、函数返回True、只import、只固定数字、把反射前提交给调用者、把注册范围自行缩小。

## F08｜循环与身份的边界

**原目标：** 无根循环不能产生支持；有根循环的原子稳定不意味着论证树稳定。
**当前执行含义：** 无根循环不能产生支持；有根循环的原子稳定不意味着论证树稳定。
**数学细节：** `MATHEMATICS_SPEC.md` 第3节。
**实现与证明位置：** `proofs/lean/juris_lean/JurisLean/FullMath/Logic/ArgumentIdentity.lean`；优先复用旧 `unified/arguments.py` 与已有ULM定理，不平行重建。

**证明施工：**
1. 构造无初始叶的a↔b反例并证明各生成层为空。
2. 构造有叶的a↔b，证明不同深度树有不同结构身份而结论可能相同。
3. 本轮不用未经证明的循环商化；未来压缩必须证明子论证攻击、优先与假设可观察量的合同余关系。
4. 保留无根与有根循环两个不同反例。
5. 任何图压缩必须给足以保持攻击/优先/来源的映射定理，不能只保原子。

**必须导出：** `JurisLean.FullMath.Contracts.target_F08` 与 `JurisLean.FullMath.Acceptance.target_F08`，以Lean赋值检查准确合同类型。
**执行证据：** 当前源文件、实际算法/检查器入口、正常与反例测试、具体类型与依赖、公理审计、同次GitHub运行。
**不能据此收工：** 文件存在、函数返回True、只import、只固定数字、把反射前提交给调用者、把注册范围自行缩小。

## F09｜攻击/击败编译双向对应

**原目标：** D_impl(a,b) ↔ DefeatSpec(v,c,a,b)。
**当前执行含义：** D_impl(a,b) ↔ DefeatSpec(v,c,a,b)。
**数学细节：** `MATHEMATICS_SPEC.md` 第3节。
**实现与证明位置：** `proofs/lean/juris_lean/JurisLean/FullMath/Logic/AttackCompilation.lean`；优先复用旧 `unified/arguments.py; JC argumentation.py target` 与已有ULM定理，不平行重建。

**证明施工：**
1. 分别归纳反驳、前提攻击、规则攻击和子论证提升的构造规则。
2. 逐边证明源、目标、依据与优先政策合法；证明所有规范上有效的攻击均被枚举。
3. 注册政策只处理允许的冲突；未知政策保留未决义务，不能静默删边；禁止仅按结论合并攻击端点。
4. 一条边的源/目标/原因/作用域均可追踪。
5. 对边生成各构造做反射，不通过结果图自身定义DefeatSpec。

**必须导出：** `JurisLean.FullMath.Contracts.target_F09` 与 `JurisLean.FullMath.Acceptance.target_F09`，以Lean赋值检查准确合同类型。
**执行证据：** 当前源文件、实际算法/检查器入口、正常与反例测试、具体类型与依赖、公理审计、同次GitHub运行。
**不能据此收工：** 文件存在、函数返回True、只import、只固定数字、把反射前提交给调用者、把注册范围自行缩小。

## F10｜扩展成员判定反射

**原目标：** member_b(profile,e)=true ↔ SatisfiesProfile(AF,profile,e)。
**当前执行含义：** member_b(profile,e)=true ↔ SatisfiesProfile(AF,profile,e)。
**数学细节：** `MATHEMATICS_SPEC.md` 第3节。
**实现与证明位置：** `proofs/lean/juris_lean/JurisLean/FullMath/Logic/ExtensionProfiles.lean`；优先复用旧 `reference/unified_reference.py; reference/core.py; JC checker target` 与已有ULM定理，不平行重建。

**证明施工：**
1. 分别证明无冲突、防御、可容许、特征函数反射。
2. grounded用既有最小不动点；complete增加可容许约束；stable检查集合内→外；preferred检查所有严格可容许超集。
3. 小域用两个独立参考实现比较全512个三节点图；这只作反例检验，普遍反射仍以Lean证明。
4. 四种profile必须分别证明，stable保持内部攻击外部的方向。
5. 强合理性需在具体profile前提下证明，不能合并不同扩展。

**必须导出：** `JurisLean.FullMath.Contracts.target_F10` 与 `JurisLean.FullMath.Acceptance.target_F10`，以Lean赋值检查准确合同类型。
**执行证据：** 当前源文件、实际算法/检查器入口、正常与反例测试、具体类型与依赖、公理审计、同次GitHub运行。
**不能据此收工：** 文件存在、函数返回True、只import、只固定数字、把反射前提交给调用者、把注册范围自行缩小。

## F11｜扫描部分健全

**原目标：** S_found ⊆ Solutions。
**当前执行含义：** S_found ⊆ Solutions。
**数学细节：** `MATHEMATICS_SPEC.md` 第3节。
**实现与证明位置：** `proofs/lean/juris_lean/JurisLean/FullMath/Representation/FiniteCertificates.lean`；优先复用旧 `unified/contract.py` 与已有ULM定理，不平行重建。

**证明施工：**
1. 对实际递归扫描预算归纳。
2. 每个加入结果的元素保留候选成员和布尔判定真见证，再应用独立成员反射。
3. UNKNOWN留在pending；完整范围未枚举不影响已证明成员的健全性。
4. 实际未处理项独立保留；对每个accepted成员应用反射。
5. 孤立扫描接口引理不能代具体checker。

**必须导出：** `JurisLean.FullMath.Contracts.target_F11` 与 `JurisLean.FullMath.Acceptance.target_F11`，以Lean赋值检查准确合同类型。
**执行证据：** 当前源文件、实际算法/检查器入口、正常与反例测试、具体类型与依赖、公理审计、同次GitHub运行。
**不能据此收工：** 文件存在、函数返回True、只import、只固定数字、把反射前提交给调用者、把注册范围自行缩小。

## F12｜扫描完整性

**原目标：** CompleteCheck ⇒ S_out = Solutions。
**当前执行含义：** CompleteCheck ⇒ S_out = Solutions。
**数学细节：** `MATHEMATICS_SPEC.md` 第3节。
**实现与证明位置：** `proofs/lean/juris_lean/JurisLean/FullMath/Representation/FiniteCertificates.lean`；优先复用旧 `unified/contract.py` 与已有ULM定理，不平行重建。

**证明施工：**
1. 独立证明载体覆盖，不把generated-list命名当覆盖。
2. 证明完整扫描等于完整筛选；用成员反射与覆盖双向包含。
3. 检查实际运行A/R/U分割、未决集合为空及范围未变，才能构造Complete。
4. 有限域集合覆盖与扫描覆盖分开。
5. 连续表示经独立等价证书可以Exact；不要恢复有限点限制。

**必须导出：** `JurisLean.FullMath.Contracts.target_F12` 与 `JurisLean.FullMath.Acceptance.target_F12`，以Lean赋值检查准确合同类型。
**执行证据：** 当前源文件、实际算法/检查器入口、正常与反例测试、具体类型与依赖、公理审计、同次GitHub运行。
**不能据此收工：** 文件存在、函数返回True、只import、只固定数字、把反射前提交给调用者、把注册范围自行缩小。

## F13｜空值与查询聚合安全

**原目标：** 未找到解≠无解≠{∅}；不完整扩展族不能证明全称查询。
**当前执行含义：** 未找到解≠无解≠{∅}；不完整扩展族不能证明全称查询。
**数学细节：** `MATHEMATICS_SPEC.md` 第3节。
**实现与证明位置：** `proofs/lean/juris_lean/JurisLean/FullMath/Logic/QueryAggregation.lean`；优先复用旧 `existing ULM11; tests/test_unified_reference.py` 与已有ULM定理，不平行重建。

**证明施工：**
1. 用三环stable、单点自攻击grounded构造区分样例。
2. 存在式命题可以由真实成员见证建立；全称支持需完整族或独立全称证书。
3. 无扩展、求解不完整和程序排除维持不同类型，不靠自然语言掩盖。
4. 无扩展不假造空扩展，无计算结果不假造零值。
5. 全称结论要求完整族或独立证书，不能用未发现反例。

**必须导出：** `JurisLean.FullMath.Contracts.target_F13` 与 `JurisLean.FullMath.Acceptance.target_F13`，以Lean赋值检查准确合同类型。
**执行证据：** 当前源文件、实际算法/检查器入口、正常与反例测试、具体类型与依赖、公理审计、同次GitHub运行。
**不能据此收工：** 文件存在、函数返回True、只import、只固定数字、把反射前提交给调用者、把注册范围自行缩小。

## F14｜增量实现精化

**原目标：** I_child(delta)=FullRecompute(new_subject)。
**当前执行含义：** I_child(delta)=FullRecompute(new_subject)。
**数学细节：** `MATHEMATICS_SPEC.md` 第2节。
**实现与证明位置：** `proofs/lean/juris_lean/JurisLean/FullMath/Evidence/Withdrawal.lean`；优先复用旧 `JC incremental.py integration task` 与已有ULM定理，不平行重建。

**证明施工：**
1. 只复用满足add-only前提且主体/规则语义一致的父闭包。
2. 为工作队列证明已处理规则、未处理前提、累计闭包的循环不变量；队列空推出新闭包最小性。
3. 删除、改写、证据失效、解释和域变化走全量；证明缓存失效不会借旧证书签新主体。
4. 删除/撤回可用已证全量重算实现正确功能，不强制实现复杂增量优化。
5. 若采用缓存，必须证明缓存等价新输入的全量结果。

**必须导出：** `JurisLean.FullMath.Contracts.target_F14` 与 `JurisLean.FullMath.Acceptance.target_F14`，以Lean赋值检查准确合同类型。
**执行证据：** 当前源文件、实际算法/检查器入口、正常与反例测试、具体类型与依赖、公理审计、同次GitHub运行。
**不能据此收工：** 文件存在、函数返回True、只import、只固定数字、把反射前提交给调用者、把注册范围自行缩小。

## P01｜有限贝叶斯网络归一化

**原目标：** ∀x P(x)≥0 且 ΣxP(x)=1。
**当前执行含义：** ∀x P(x)≥0 且 ΣxP(x)=1。
**数学细节：** `MATHEMATICS_SPEC.md` 第8节。
**实现与证明位置：** `proofs/lean/juris_lean/JurisLean/FullMath/Probability/FiniteBN.lean`；优先复用旧 `reference/core.py / BayesNet` 与已有ULM定理，不平行重建。

**证明施工：**
1. 校验有限状态集、拓扑顺序、父节点键及每行CPT非负和为1。
2. 从最后节点逆序求和，消去其条件概率行，重复至空网络。
3. 将有理参数嵌入实数概率测度时证明非负和归一化保持。
4. 按MATHEMATICS_SPEC相应章节的独立对象、算法不变量和证明路线完成。
5. 实际计算函数、输入校验和类型边界同时接入通用根；不得只登记字段。

**必须导出：** `JurisLean.FullMath.Contracts.target_P01` 与 `JurisLean.FullMath.Acceptance.target_P01`，以Lean赋值检查准确合同类型。
**执行证据：** 当前源文件、实际算法/检查器入口、正常与反例测试、具体类型与依赖、公理审计、同次GitHub运行。
**不能据此收工：** 文件存在、函数返回True、只import、只固定数字、把反射前提交给调用者、把注册范围自行缩小。

## P02｜后验与零证据质量

**原目标：** Z>0 ⇒ posterior归一；Z=0 ⇒不兼容而非假设概率为0。
**当前执行含义：** Z>0 ⇒ posterior归一；Z=0 ⇒不兼容而非假设概率为0。
**数学细节：** `MATHEMATICS_SPEC.md` 第8节。
**实现与证明位置：** `proofs/lean/juris_lean/JurisLean/FullMath/Probability/Conditioning.lean`；优先复用旧 `reference/core.py` 与已有ULM定理，不平行重建。

**证明施工：**
1. 用有限加权求和证明质量非负，正Z定义归一化。
2. 用sum_div证明总和1；检查不同目标状态的边缘和等式。
3. 对零Z不调用除法并返回模型不兼容类型，不能用Lean的totalized division掩盖非法条件化。
4. 按MATHEMATICS_SPEC相应章节的独立对象、算法不变量和证明路线完成。
5. 实际计算函数、输入校验和类型边界同时接入通用根；不得只登记字段。

**必须导出：** `JurisLean.FullMath.Contracts.target_P02` 与 `JurisLean.FullMath.Acceptance.target_P02`，以Lean赋值检查准确合同类型。
**执行证据：** 当前源文件、实际算法/检查器入口、正常与反例测试、具体类型与依赖、公理审计、同次GitHub运行。
**不能据此收工：** 文件存在、函数返回True、只import、只固定数字、把反射前提交给调用者、把注册范围自行缩小。

## P03｜变量消去精确性

**原目标：** VE(query,e)=Enumerate(query,e)。
**当前执行含义：** VE(query,e)=Enumerate(query,e)。
**数学细节：** `MATHEMATICS_SPEC.md` 第8节。
**实现与证明位置：** `proofs/lean/juris_lean/JurisLean/FullMath/Probability/VariableElimination.lean`；优先复用旧 `reference/core.py / enumerate_query and eliminate_query` 与已有ULM定理，不平行重建。

**证明施工：**
1. 定义每步factor乘积求和的未消元变量不变量。
2. 证明只含所消变量的因子收集完整，有限求和分配可提出不依赖该变量的因子。
3. 对消元列表归纳并证明剩余目标归一化一致；factor键/作用域错误须被拒绝。
4. 实现因子乘积、求和消元并证明域/顺序不变量。
5. 引用同一source的多个Observation不是独立采样。

**必须导出：** `JurisLean.FullMath.Contracts.target_P03` 与 `JurisLean.FullMath.Acceptance.target_P03`，以Lean赋值检查准确合同类型。
**执行证据：** 当前源文件、实际算法/检查器入口、正常与反例测试、具体类型与依赖、公理审计、同次GitHub运行。
**不能据此收工：** 文件存在、函数返回True、只import、只固定数字、把反射前提交给调用者、把注册范围自行缩小。

## P04｜证据身份与依赖

**原目标：** 同一Observation重复提交不重复更新；排除证据的派生特征不能残留。
**当前执行含义：** 同一Observation重复提交不重复更新；排除证据的派生特征不能残留。
**数学细节：** `MATHEMATICS_SPEC.md` 第8节。
**实现与证明位置：** `proofs/lean/juris_lean/JurisLean/FullMath/Probability/ObservationIdentity.lean`；优先复用旧 `reference/core.py; unified/model_basis.py; unified/taint.py` 与已有ULM定理，不平行重建。

**证明施工：**
1. 按观测身份去重且矛盾值拒绝；不同ID不自动构成统计独立。
2. 在网络中表示同源、共同潜因等明确依赖；条件独立须来自模型而非乘法习惯。
3. 使用F04依赖闭包重新构造可接受模型输入，证明排除敏感证据后的计算不再依赖它。
4. 按MATHEMATICS_SPEC相应章节的独立对象、算法不变量和证明路线完成。
5. 实际计算函数、输入校验和类型边界同时接入通用根；不得只登记字段。

**必须导出：** `JurisLean.FullMath.Contracts.target_P04` 与 `JurisLean.FullMath.Acceptance.target_P04`，以Lean赋值检查准确合同类型。
**执行证据：** 当前源文件、实际算法/检查器入口、正常与反例测试、具体类型与依赖、公理审计、同次GitHub运行。
**不能据此收工：** 文件存在、函数返回True、只import、只固定数字、把反射前提交给调用者、把注册范围自行缩小。

## P05｜Dirichlet更新

**原目标：** α+n 后验及其预测均值满足选定多项似然。
**当前执行含义：** α+n 后验及其预测均值满足选定多项似然。
**数学细节：** `MATHEMATICS_SPEC.md` 第8节。
**实现与证明位置：** `proofs/lean/juris_lean/JurisLean/FullMath/Probability/DirichletPosterior.lean`；优先复用旧 `reference/core.py / dirichlet_predictive` 与已有ULM定理，不平行重建。

**证明施工：**
1. 明示条件多项/独立采样假设和正先验。
2. 将先验密度与似然相乘，合并指数，验证正规化常数比值。
3. 证明预测积分/有限统计量公式；隐变量或选择偏差不是简单计数更新的自动保证。
4. 按MATHEMATICS_SPEC相应章节的独立对象、算法不变量和证明路线完成。
5. 实际计算函数、输入校验和类型边界同时接入通用根；不得只登记字段。

**必须导出：** `JurisLean.FullMath.Contracts.target_P05` 与 `JurisLean.FullMath.Acceptance.target_P05`，以Lean赋值检查准确合同类型。
**执行证据：** 当前源文件、实际算法/检查器入口、正常与反例测试、具体类型与依赖、公理审计、同次GitHub运行。
**不能据此收工：** 文件存在、函数返回True、只import、只固定数字、把反射前提交给调用者、把注册范围自行缩小。

## P06｜层级胜率学习实际使用数据

**原目标：** 有限超先验权重 ∝ π_h∏g B(α_h+w_g,β_h+l_g)/B(α_h,β_h)。
**当前执行含义：** 有限超先验权重 ∝ π_h∏g B(α_h+w_g,β_h+l_g)/B(α_h,β_h)。
**数学细节：** `MATHEMATICS_SPEC.md` 第8节。
**实现与证明位置：** `proofs/lean/juris_lean/JurisLean/FullMath/Probability/HierarchicalPrediction.lean`；优先复用旧 `unified/win_model.py / fit` 与已有ULM定理，不平行重建。

**证明施工：**
1. 对每组Beta先验积分Bernoulli似然；组合数如省略须证明其不依赖h并在归一化抵消。
2. 将Beta比值变为上升阶乘，证明参考有理算法与公式相等。
3. 归一化超后验；证明新组/已有组预测公式；测试改变标签确实改变后验。
4. 按MATHEMATICS_SPEC相应章节的独立对象、算法不变量和证明路线完成。
5. 实际计算函数、输入校验和类型边界同时接入通用根；不得只登记字段。

**必须导出：** `JurisLean.FullMath.Contracts.target_P06` 与 `JurisLean.FullMath.Acceptance.target_P06`，以Lean赋值检查准确合同类型。
**执行证据：** 当前源文件、实际算法/检查器入口、正常与反例测试、具体类型与依赖、公理审计、同次GitHub运行。
**不能据此收工：** 文件存在、函数返回True、只import、只固定数字、把反射前提交给调用者、把注册范围自行缩小。

## P07｜模型平均与竞争模型界

**原目标：** 模型平均更新用证据边际；稳健界覆盖每个保留模型。
**当前执行含义：** 模型平均更新用证据边际；稳健界覆盖每个保留模型。
**数学细节：** `MATHEMATICS_SPEC.md` 第8节。
**实现与证明位置：** `proofs/lean/juris_lean/JurisLean/FullMath/Probability/ModelFamilies.lean`；优先复用旧 `unified/model_basis.py; reference/core.py` 与已有ULM定理，不平行重建。

**证明施工：**
1. 证明联合变量(model,state)上的Bayes更新后得到π_mZ_m正规化。
2. 对有限模型逐个求值，最小最大界用成员论证证明覆盖。
3. 零似然模型在稳健全集与模型平均中的不同处置分别标明，不静默换声明。
4. 按MATHEMATICS_SPEC相应章节的独立对象、算法不变量和证明路线完成。
5. 实际计算函数、输入校验和类型边界同时接入通用根；不得只登记字段。

**必须导出：** `JurisLean.FullMath.Contracts.target_P07` 与 `JurisLean.FullMath.Acceptance.target_P07`，以Lean赋值检查准确合同类型。
**执行证据：** 当前源文件、实际算法/检查器入口、正常与反例测试、具体类型与依赖、公理审计、同次GitHub运行。
**不能据此收工：** 文件存在、函数返回True、只import、只固定数字、把反射前提交给调用者、把注册范围自行缩小。

## P08｜后验误设外界

**原目标：** (1-ε)l ≤ P*(H) ≤ (1-ε)u+ε。
**当前执行含义：** (1-ε)l ≤ P*(H) ≤ (1-ε)u+ε。
**数学细节：** `MATHEMATICS_SPEC.md` 第8节。
**实现与证明位置：** `proofs/lean/juris_lean/JurisLean/FullMath/Probability/Misspecification.lean`；优先复用旧 `unified/contract.py` 与已有ULM定理，不平行重建。

**证明施工：**
1. 先明确污染发生在证据条件化之后。
2. 用0≤Q(H)≤1、0≤ε≤1及乘法单调性分别证明上下界。
3. 给出罕见证据放大先验污染的反例，禁止将同一ε跨条件化搬用。
4. 按MATHEMATICS_SPEC相应章节的独立对象、算法不变量和证明路线完成。
5. 实际计算函数、输入校验和类型边界同时接入通用根；不得只登记字段。

**必须导出：** `JurisLean.FullMath.Contracts.target_P08` 与 `JurisLean.FullMath.Acceptance.target_P08`，以Lean赋值检查准确合同类型。
**执行证据：** 当前源文件、实际算法/检查器入口、正常与反例测试、具体类型与依赖、公理审计、同次GitHub运行。
**不能据此收工：** 文件存在、函数返回True、只import、只固定数字、把反射前提交给调用者、把注册范围自行缩小。

## P09｜部分概率质量界

**原目标：** 已知a,b和剩余质量≤r ⇒ a/(a+b+r) ≤ p ≤ (a+r)/(a+b+r)。
**当前执行含义：** 已知a,b和剩余质量≤r ⇒ a/(a+b+r) ≤ p ≤ (a+r)/(a+b+r)。
**数学细节：** `MATHEMATICS_SPEC.md` 第8节。
**实现与证明位置：** `proofs/lean/juris_lean/JurisLean/FullMath/Probability/PartialMass.lean`；优先复用旧 `unified/contract.py / partial_mass_enclosure` 与已有ULM定理，不平行重建。

**证明施工：**
1. 设未算的事件/非事件质量u,v≥0,u+v≤r，写出p=(a+u)/(a+b+u+v)。
2. 在分母正条件下交叉相乘证明上下界；零质量分支单独处理。
3. 剩余r须由覆盖分块/因子界证明；只是剩余状态数不能当概率质量。
4. 按MATHEMATICS_SPEC相应章节的独立对象、算法不变量和证明路线完成。
5. 实际计算函数、输入校验和类型边界同时接入通用根；不得只登记字段。

**必须导出：** `JurisLean.FullMath.Contracts.target_P09` 与 `JurisLean.FullMath.Acceptance.target_P09`，以Lean赋值检查准确合同类型。
**执行证据：** 当前源文件、实际算法/检查器入口、正常与反例测试、具体类型与依赖、公理审计、同次GitHub运行。
**不能据此收工：** 文件存在、函数返回True、只import、只固定数字、把反射前提交给调用者、把注册范围自行缩小。

## P10｜潜在成功率可信区间

**原目标：** 精确Beta混合CDF括界 ⇒ 模型内后验质量至少1-δ。
**当前执行含义：** 精确Beta混合CDF括界 ⇒ 模型内后验质量至少1-δ。
**数学细节：** `MATHEMATICS_SPEC.md` 第8节。
**实现与证明位置：** `proofs/lean/juris_lean/JurisLean/FullMath/Probability/PosteriorIntervals.lean`；优先复用旧 `unified/win_model.py / latent_rate_interval` 与已有ULM定理，不平行重建。

**证明施工：**
1. 整数a,b时证明BetaCDF等于二项尾和；一般参数用已证矩/不等式外包，不伪造精确分位数。
2. 用CDF单调性维持二分区间；下端CDF≤δ/2，上端CDF≥1-δ/2。
3. 明确该概率对象为原始潜在参数，不是下一件案件命中率或校准后频率保证。
4. CDF端点采用保守方向；保留精确分位数不可用状态。
5. 后验区间覆盖潜在模型参数，不是新个案胜率的保证。

**必须导出：** `JurisLean.FullMath.Contracts.target_P10` 与 `JurisLean.FullMath.Acceptance.target_P10`，以Lean赋值检查准确合同类型。
**执行证据：** 当前源文件、实际算法/检查器入口、正常与反例测试、具体类型与依赖、公理审计、同次GitHub运行。
**不能据此收工：** 文件存在、函数返回True、只import、只固定数字、把反射前提交给调用者、把注册范围自行缩小。

## P11｜胜率目标和无泄漏分割

**原目标：** 所有训练/校准/测试行具有同一目标；cluster不跨区；特征与标签时间顺序正确。
**当前执行含义：** 所有训练/校准/测试行具有同一目标；cluster不跨区；特征与标签时间顺序正确。
**数学细节：** `MATHEMATICS_SPEC.md` 第9节。
**实现与证明位置：** `proofs/lean/juris_lean/JurisLean/FullMath/Statistics/DatasetSplits.lean`；优先复用旧 `unified/win_model.py / validate_splits` 与已有ULM定理，不平行重建。

**证明施工：**
1. 定义目标元组并禁止跨当事人/审级/救济/时点标签混合。
2. 对集合交集和时间最大最小值证明分割无已声明的泄漏；语义上的事后信息仍需特征审核。
3. 证明修改测试标签不改变训练模型或校准器；独立测试只计算成绩。
4. 按MATHEMATICS_SPEC相应章节的独立对象、算法不变量和证明路线完成。
5. 实际计算函数、输入校验和类型边界同时接入通用根；不得只登记字段。

**必须导出：** `JurisLean.FullMath.Contracts.target_P11` 与 `JurisLean.FullMath.Acceptance.target_P11`，以Lean赋值检查准确合同类型。
**执行证据：** 当前源文件、实际算法/检查器入口、正常与反例测试、具体类型与依赖、公理审计、同次GitHub运行。
**不能据此收工：** 文件存在、函数返回True、只import、只固定数字、把反射前提交给调用者、把注册范围自行缩小。

## P12｜Brier严格适当与评价实现

**原目标：** E(q-Y)^2-E(p-Y)^2=(q-p)^2≥0。
**当前执行含义：** E(q-Y)^2-E(p-Y)^2=(q-p)^2≥0。
**数学细节：** `MATHEMATICS_SPEC.md` 第9节。
**实现与证明位置：** `proofs/lean/juris_lean/JurisLean/FullMath/Statistics/ProperScores.lean`；优先复用旧 `unified/win_model.py / evaluate` 与已有ULM定理，不平行重建。

**证明施工：**
1. 对Bernoulli两点展开平方并作环恒等式。
2. 平方非负推出p处最小；相等条件推出q=p。
3. 实现计算持出数据样本平均，log-loss如裁剪明确ε；不把适当性定理当模型已经校准。
4. 按MATHEMATICS_SPEC相应章节的独立对象、算法不变量和证明路线完成。
5. 实际计算函数、输入校验和类型边界同时接入通用根；不得只登记字段。

**必须导出：** `JurisLean.FullMath.Contracts.target_P12` 与 `JurisLean.FullMath.Acceptance.target_P12`，以Lean赋值检查准确合同类型。
**执行证据：** 当前源文件、实际算法/检查器入口、正常与反例测试、具体类型与依赖、公理审计、同次GitHub运行。
**不能据此收工：** 文件存在、函数返回True、只import、只固定数字、把反射前提交给调用者、把注册范围自行缩小。

## P13｜PAV校准算法最优性

**原目标：** PAV解达到加权平方损失在单调序列上的最小值。
**当前执行含义：** PAV解达到加权平方损失在单调序列上的最小值。
**数学细节：** `MATHEMATICS_SPEC.md` 第9节。
**实现与证明位置：** `proofs/lean/juris_lean/JurisLean/FullMath/Statistics/IsotonicCalibration.lean`；优先复用旧 `unified/win_model.py / calibrate` 与已有ULM定理，不平行重建。

**证明施工：**
1. 同分数先合并，证明固定块最优常值为加权均值。
2. 相邻倒序块合并不排除任何比当前更优的单调解，使用交换论证或KKT的充分条件。
3. 维护块有序与加权统计量；结束时建立全局最优证书，而不只测试单调性。
4. 算法之外给独立梯度/互补证书，以严格凸性证唯一最优。
5. 同分score先聚合，不让排序细节赋不同校准值。

**必须导出：** `JurisLean.FullMath.Contracts.target_P13` 与 `JurisLean.FullMath.Acceptance.target_P13`，以Lean赋值检查准确合同类型。
**执行证据：** 当前源文件、实际算法/检查器入口、正常与反例测试、具体类型与依赖、公理审计、同次GitHub运行。
**不能据此收工：** 文件存在、函数返回True、只import、只固定数字、把反射前提交给调用者、把注册范围自行缩小。

## E01｜真实胜率外部适用评估

**原目标：** 具名数据/目标/群体/时段的预注册验收；不是对未来一切案件的数学保证。
**当前执行含义：** Prove the evaluation/holdout/claim-policy algorithms and implement the real evaluation runner; actual named-cohort validation remains E01-EMPIRICAL and is never closed by synthetic data or the math-only completion receipt.
**数学细节：** `MATHEMATICS_SPEC.md` 第9节。
**实现与证明位置：** `proofs/lean/juris_lean/JurisLean/FullMath/Statistics/ValidationContract.lean`；优先复用旧 `unified/win_model.py; private data workflow` 与已有ULM定理，不平行重建。

**证明施工：**
1. 用真实来源裁判和预测时可用材料构建cluster化数据；记录缺失/公布选择/标签争议。
2. 锁定开发集阈值与模型选择，单次持出评估Brier、log-loss、可靠性、分层与时间漂移。
3. 对未经测量群体或明显漂移给出未校准/范围外标记；合成样例永不能关闭此任务。
4. 数学部分：完成指标、划分、无回流和经验声明判定的定理及运行器。
5. 原真实数据验收以E01-EMPIRICAL保留；没有真实数据不可改标VALIDATED；数学完成回执明确不替代它。

**必须导出：** `JurisLean.FullMath.Contracts.target_E01` 与 `JurisLean.FullMath.Acceptance.target_E01`，以Lean赋值检查准确合同类型。
**执行证据：** 当前源文件、实际算法/检查器入口、正常与反例测试、具体类型与依赖、公理审计、同次GitHub运行。
**不能据此收工：** 文件存在、函数返回True、只import、只固定数字、把反射前提交给调用者、把注册范围自行缩小。

## N01｜单位、来源、舍入解释器

**原目标：** 每个算术表达式的结果具有声明单位/计算口径与精确指称。
**当前执行含义：** 每个算术表达式的结果具有声明单位/计算口径与精确指称。
**数学细节：** `MATHEMATICS_SPEC.md` 第5节。
**实现与证明位置：** `proofs/lean/juris_lean/JurisLean/FullMath/Quantity/TypedArithmeticLedgerCalendar.lean`；优先复用旧 `unified/precision.py; existing ULM13` 与已有ULM定理，不平行重建。

**证明施工：**
1. 按表达式结构归纳，禁止不同币种/期间/债务项目无转换相加。
2. 为显式单位转换证明数值与计量语义保持，月不能统一换30天。
3. 对舍入指定位置/模式和误差界；不在每步隐式浮点化。
4. 按MATHEMATICS_SPEC相应章节的独立对象、算法不变量和证明路线完成。
5. 实际计算函数、输入校验和类型边界同时接入通用根；不得只登记字段。

**必须导出：** `JurisLean.FullMath.Contracts.target_N01` 与 `JurisLean.FullMath.Acceptance.target_N01`，以Lean赋值检查准确合同类型。
**执行证据：** 当前源文件、实际算法/检查器入口、正常与反例测试、具体类型与依赖、公理审计、同次GitHub运行。
**不能据此收工：** 文件存在、函数返回True、只import、只固定数字、把反射前提交给调用者、把注册范围自行缩小。

## N02｜区间解释健全

**原目标：** Eval(e,x)∈IntervalEval(e,X) 对所有x∈X成立。
**当前执行含义：** Eval(e,x)∈IntervalEval(e,X) 对所有x∈X成立。
**数学细节：** `MATHEMATICS_SPEC.md` 第6节。
**实现与证明位置：** `proofs/lean/juris_lean/JurisLean/FullMath/Quantity/IntervalInterpreter.lean`；优先复用旧 `reference/core.py / Interval` 与已有ULM定理，不平行重建。

**证明施工：**
1. 叶子由输入区间，逐步证明加减/四端点乘法。
2. 除法仅分母区间远离0；舍入用外向舍入误差。
3. 同变量依赖可能导致过宽，只报告外包界不声称端点一定可达。
4. 按MATHEMATICS_SPEC相应章节的独立对象、算法不变量和证明路线完成。
5. 实际计算函数、输入校验和类型边界同时接入通用根；不得只登记字段。

**必须导出：** `JurisLean.FullMath.Contracts.target_N02` 与 `JurisLean.FullMath.Acceptance.target_N02`，以Lean赋值检查准确合同类型。
**执行证据：** 当前源文件、实际算法/检查器入口、正常与反例测试、具体类型与依赖、公理审计、同次GitHub运行。
**不能据此收工：** 文件存在、函数返回True、只import、只固定数字、把反射前提交给调用者、把注册范围自行缩小。

## N03｜法律可行域

**原目标：** 被称为legal-feasible的候选逐一满足已准入C(v,c,f,y)。
**当前执行含义：** 被称为legal-feasible的候选逐一满足已准入C(v,c,f,y)。
**数学细节：** `MATHEMATICS_SPEC.md` 第6节。
**实现与证明位置：** `proofs/lean/juris_lean/JurisLean/FullMath/Optimization/FeasibleRelations.lean`；优先复用旧 `unified/precision.py / optimize_finite; production constraint compiler task` 与已有ULM定理，不平行重建。

**证明施工：**
1. 从请求/规则/例外构造独立约束AST，并保留政策来源。
2. 候选检查器直接验证所有硬约束；不能让目标惩罚替代硬条件。
3. 对依赖未知法律评价的约束保留条件性或未决，不直接用数值最优替代审核。
4. 按MATHEMATICS_SPEC相应章节的独立对象、算法不变量和证明路线完成。
5. 实际计算函数、输入校验和类型边界同时接入通用根；不得只登记字段。

**必须导出：** `JurisLean.FullMath.Contracts.target_N03` 与 `JurisLean.FullMath.Acceptance.target_N03`，以Lean赋值检查准确合同类型。
**执行证据：** 当前源文件、实际算法/检查器入口、正常与反例测试、具体类型与依赖、公理审计、同次GitHub运行。
**不能据此收工：** 文件存在、函数返回True、只import、只固定数字、把反射前提交给调用者、把注册范围自行缩小。

## N04｜部分端点不得冒充全界

**原目标：** minS≤minFound；maxFound≤maxS；Found跨度可能漏真实端点。
**当前执行含义：** minS≤minFound；maxFound≤maxS；Found跨度可能漏真实端点。
**数学细节：** `MATHEMATICS_SPEC.md` 第6节。
**实现与证明位置：** `proofs/lean/juris_lean/JurisLean/FullMath/Optimization/PartialExtrema.lean`；优先复用旧 `unified/contract.py` 与已有ULM定理，不平行重建。

**证明施工：**
1. 用子集关系证明两个单调方向。
2. 保留{20,30}⊆{0,20,30,100}反例，证明20–30不是全体外包络。
3. 显示类型区分observed-span、certified-envelope、exact-extrema；空集合不报0。
4. 按MATHEMATICS_SPEC相应章节的独立对象、算法不变量和证明路线完成。
5. 实际计算函数、输入校验和类型边界同时接入通用根；不得只登记字段。

**必须导出：** `JurisLean.FullMath.Contracts.target_N04` 与 `JurisLean.FullMath.Acceptance.target_N04`，以Lean赋值检查准确合同类型。
**执行证据：** 当前源文件、实际算法/检查器入口、正常与反例测试、具体类型与依赖、公理审计、同次GitHub运行。
**不能据此收工：** 文件存在、函数返回True、只import、只固定数字、把反射前提交给调用者、把注册范围自行缩小。

## N05｜LP对偶最优证书

**原目标：** 原可行、对偶可行、目标相等 ⇒ 全局最优。
**当前执行含义：** 原可行、对偶可行、目标相等 ⇒ 全局最优。
**数学细节：** `MATHEMATICS_SPEC.md` 第6节。
**实现与证明位置：** `proofs/lean/juris_lean/JurisLean/FullMath/Optimization/LinearCertificates.lean`；优先复用旧 `unified/precision.py / verify_min_lp_optimum; retained legacy max checker` 与已有ULM定理，不平行重建。

**证明施工：**
1. 固定不等号约定，逐维利用非负乘子推出弱对偶。
2. 任何可行候选目标≥对偶值，证书候选达到该值，因此最优。
3. 有理运算复核所有矩阵、目标与约束绑定；浮点求解器只能提议证书。
4. 按MATHEMATICS_SPEC相应章节的独立对象、算法不变量和证明路线完成。
5. 实际计算函数、输入校验和类型边界同时接入通用根；不得只登记字段。

**必须导出：** `JurisLean.FullMath.Contracts.target_N05` 与 `JurisLean.FullMath.Acceptance.target_N05`，以Lean赋值检查准确合同类型。
**执行证据：** 当前源文件、实际算法/检查器入口、正常与反例测试、具体类型与依赖、公理审计、同次GitHub运行。
**不能据此收工：** 文件存在、函数返回True、只import、只固定数字、把反射前提交给调用者、把注册范围自行缩小。

## N06｜凸性见证和KKT充分性

**原目标：** 凸目标+凸可行域+有效KKT条件 ⇒ 全局最小。
**当前执行含义：** 凸目标+凸可行域+有效KKT条件 ⇒ 全局最小。
**数学细节：** `MATHEMATICS_SPEC.md` 第6节。
**实现与证明位置：** `proofs/lean/juris_lean/JurisLean/FullMath/Optimization/ConvexCertificates.lean`；优先复用旧 `unified/precision.py / verify_ldl_psd; planned complete convex/KKT checker` 与已有ULM定理，不平行重建。

**证明施工：**
1. 用允许语法归纳证明凸性；二次式以精确PSD分解验证。
2. 利用凸次梯度下界及对偶可行、互补性证明候选不劣于任意可行点。
3. 必要性/乘子存在性单列Slater等条件；整数约束不能伪装凸集。
4. 按MATHEMATICS_SPEC相应章节的独立对象、算法不变量和证明路线完成。
5. 实际计算函数、输入校验和类型边界同时接入通用根；不得只登记字段。

**必须导出：** `JurisLean.FullMath.Contracts.target_N06` 与 `JurisLean.FullMath.Acceptance.target_N06`，以Lean赋值检查准确合同类型。
**执行证据：** 当前源文件、实际算法/检查器入口、正常与反例测试、具体类型与依赖、公理审计、同次GitHub运行。
**不能据此收工：** 文件存在、函数返回True、只import、只固定数字、把反射前提交给调用者、把注册范围自行缩小。

## N07｜有界整数完整性与分支定界

**原目标：** 每个剪枝有有效下界；全部叶覆盖关闭后才允许全局最优声明。
**当前执行含义：** 每个剪枝有有效下界；全部叶覆盖关闭后才允许全局最优声明。
**数学细节：** `MATHEMATICS_SPEC.md` 第6节。
**实现与证明位置：** `proofs/lean/juris_lean/JurisLean/FullMath/Optimization/IntegerCertificates.lean`；优先复用旧 `unified/precision.py / finite reference; branch-and-bound production target` 与已有ULM定理，不平行重建。

**证明施工：**
1. 第一版对声明整数域穷举建立候选覆盖。
2. 分支约束互补覆盖父节点整数点，松弛包含子域，对偶下界不超过真实子域最优。
3. 证明剪去不可能改进incumbent的节点安全；开放节点存在时只报上下界/gap，不报complete。
4. 求一个最优值与枚举全部最优解须采用不同等值剪枝规则。
5. 开放节点存在时给outer/gap，不根据incumbent跨度冒称完备。

**必须导出：** `JurisLean.FullMath.Contracts.target_N07` 与 `JurisLean.FullMath.Acceptance.target_N07`，以Lean赋值检查准确合同类型。
**执行证据：** 当前源文件、实际算法/检查器入口、正常与反例测试、具体类型与依赖、公理审计、同次GitHub运行。
**不能据此收工：** 文件存在、函数返回True、只import、只固定数字、把反射前提交给调用者、把注册范围自行缩小。

## N08｜指定投影算子真正压缩

**原目标：** 0<ηa<2 ⇒ Lip(T)≤|1-ηa|<1。
**当前执行含义：** 0<ηa<2 ⇒ Lip(T)≤|1-ηa|<1。
**数学细节：** `MATHEMATICS_SPEC.md` 第7节。
**实现与证明位置：** `proofs/lean/juris_lean/JurisLean/FullMath/Optimization/ProjectedContraction.lean`；优先复用旧 `unified/precision.py / QuadraticContraction` 与已有ULM定理，不平行重建。

**证明施工：**
1. 将仿射步差值化为(1-ηa)(x-y)，证明绝对值因子。
2. 对闭区间投影按位置分类证明非扩张。
3. 合成得到k；在实例输入上检查a,η,l,u和算子结构，不接受任意legal_score函数口头声明压缩。
4. 按MATHEMATICS_SPEC相应章节的独立对象、算法不变量和证明路线完成。
5. 实际计算函数、输入校验和类型边界同时接入通用根；不得只登记字段。

**必须导出：** `JurisLean.FullMath.Contracts.target_N08` 与 `JurisLean.FullMath.Acceptance.target_N08`，以Lean赋值检查准确合同类型。
**执行证据：** 当前源文件、实际算法/检查器入口、正常与反例测试、具体类型与依赖、公理审计、同次GitHub运行。
**不能据此收工：** 文件存在、函数返回True、只import、只固定数字、把反射前提交给调用者、把注册范围自行缩小。

## N09｜Banach存在、唯一、收敛及残差

**原目标：** 指定实数闭区间上的T有唯一固定点，|x-x*|≤|x-Tx|/(1-k)。
**当前执行含义：** 指定实数闭区间上的T有唯一固定点，|x-x*|≤|x-Tx|/(1-k)。
**数学细节：** `MATHEMATICS_SPEC.md` 第7节。
**实现与证明位置：** `proofs/lean/juris_lean/JurisLean/FullMath/Optimization/BanachBounds.lean`；优先复用旧 `existing ULM15 Banach; unified/precision.py` 与已有ULM定理，不平行重建。

**证明施工：**
1. 证明闭区间非空且是完备实数空间的闭子集，T自映射。
2. 把N08压缩见证交给固定mathlib Banach接口；用三角不等式及压缩关系推出残差界。
3. 证明有理实现嵌入实数及误差界，不能称Q完备；外包半径用精确或外向计算。
4. 必须在实数闭区间子类型内取得完备性和self-map。
5. 求解误差与显示舍入误差分别传播。

**必须导出：** `JurisLean.FullMath.Contracts.target_N09` 与 `JurisLean.FullMath.Acceptance.target_N09`，以Lean赋值检查准确合同类型。
**执行证据：** 当前源文件、实际算法/检查器入口、正常与反例测试、具体类型与依赖、公理审计、同次GitHub运行。
**不能据此收工：** 文件存在、函数返回True、只import、只固定数字、把反射前提交给调用者、把注册范围自行缩小。

## N10｜固定点与优化目标一致

**原目标：** x*=clip(-b/a) 满足变分不等式，因此最小化指定二次目标。
**当前执行含义：** x*=clip(-b/a) 满足变分不等式，因此最小化指定二次目标。
**数学细节：** `MATHEMATICS_SPEC.md` 第7节。
**实现与证明位置：** `proofs/lean/juris_lean/JurisLean/FullMath/Optimization/QuadraticEquivalence.lean`；优先复用旧 `unified/precision.py` 与已有ULM定理，不平行重建。

**证明施工：**
1. 分别处理无约束最优点在区间内、左侧、右侧的三种情况。
2. 证明固定点且(ax*+b)(y-x*)≥0对所有可行y成立。
3. 用二次差值分解及a>0得到最小性/唯一性，不泛推所有法律裁量。
4. 按MATHEMATICS_SPEC相应章节的独立对象、算法不变量和证明路线完成。
5. 实际计算函数、输入校验和类型边界同时接入通用根；不得只登记字段。

**必须导出：** `JurisLean.FullMath.Contracts.target_N10` 与 `JurisLean.FullMath.Acceptance.target_N10`，以Lean赋值检查准确合同类型。
**执行证据：** 当前源文件、实际算法/检查器入口、正常与反例测试、具体类型与依赖、公理审计、同次GitHub运行。
**不能据此收工：** 文件存在、函数返回True、只import、只固定数字、把反射前提交给调用者、把注册范围自行缩小。

## B01｜领域无关的争点型证明责任

**原目标：** 证明对象、提出责任、说服责任、标准、阶段、主体和后果均有明确来源。
**当前执行含义：** 证明对象、提出责任、说服责任、标准、阶段、主体和后果均有明确来源。
**数学细节：** `MATHEMATICS_SPEC.md` 第10节。
**实现与证明位置：** `proofs/lean/juris_lean/JurisLean/FullMath/Law/BurdenLanguage.lean`；优先复用旧 `unified/burdens.py; fixtures/burden_profiles.json` 与已有ULM定理，不平行重建。

**证明施工：**
1. 定义分离字段，逐条准入法律政策，不把字符串来源当法条已正确解释。
2. 构造普通/特殊/例外的明确选择关系；冲突无政策时返回未决而非选最高数字。
3. 实体失败与程序裁定构造器分开，逐阶段核对适用范围。
4. 按MATHEMATICS_SPEC相应章节的独立对象、算法不变量和证明路线完成。
5. 实际计算函数、输入校验和类型边界同时接入通用根；不得只登记字段。

**必须导出：** `JurisLean.FullMath.Contracts.target_B01` 与 `JurisLean.FullMath.Acceptance.target_B01`，以Lean赋值检查准确合同类型。
**执行证据：** 当前源文件、实际算法/检查器入口、正常与反例测试、具体类型与依赖、公理审计、同次GitHub运行。
**不能据此收工：** 文件存在、函数返回True、只import、只固定数字、把反射前提交给调用者、把注册范围自行缩小。

## B02｜就绪判断与未知事实

**原目标：** 不完整评估⇒pending；已完成未证明⇒声明的不利效果而非历史否定。
**当前执行含义：** 不完整评估⇒pending；已完成未证明⇒声明的不利效果而非历史否定。
**数学细节：** `MATHEMATICS_SPEC.md` 第10节。
**实现与证明位置：** `proofs/lean/juris_lean/JurisLean/FullMath/Law/ProceduralReadiness.lean`；优先复用旧 `unified/burdens.py` 与已有ULM定理，不平行重建。

**证明施工：**
1. 枚举stageReady/assessmentComplete/authorityValid；任一false时无终局效果。
2. 用独立事实状态承载原finding；输出法律后果不修改finding。
3. 律师条件意见不得成为法院判决，假设finding使用不同构造器且保留assumptionID。
4. 按MATHEMATICS_SPEC相应章节的独立对象、算法不变量和证明路线完成。
5. 实际计算函数、输入校验和类型边界同时接入通用根；不得只登记字段。

**必须导出：** `JurisLean.FullMath.Contracts.target_B02` 与 `JurisLean.FullMath.Acceptance.target_B02`，以Lean赋值检查准确合同类型。
**执行证据：** 当前源文件、实际算法/检查器入口、正常与反例测试、具体类型与依赖、公理审计、同次GitHub运行。
**不能据此收工：** 文件存在、函数返回True、只import、只固定数字、把反射前提交给调用者、把注册范围自行缩小。

## B03｜推定、免证、反证、举证妨碍

**原目标：** 每个特殊机制仅对其指定争点和法律后果生效。
**当前执行含义：** 每个特殊机制仅对其指定争点和法律后果生效。
**数学细节：** `MATHEMATICS_SPEC.md` 第10节。
**实现与证明位置：** `proofs/lean/juris_lean/JurisLean/FullMath/Law/PresumptionsExclusion.lean`；优先复用旧 `domain rule-pack implementation target` 与已有ULM定理，不平行重建。

**证明施工：**
1. 分别列触发事实、提出材料义务、反证标准、可适用阶段和适用例外。
2. 证明取消/推翻推定只使该支持失效，不直接肯定所有相反命题。
3. 举证妨碍的后果由所选法源确定；证据无合法性不只降低概率，可能必须排除。
4. 按MATHEMATICS_SPEC相应章节的独立对象、算法不变量和证明路线完成。
5. 实际计算函数、输入校验和类型边界同时接入通用根；不得只登记字段。

**必须导出：** `JurisLean.FullMath.Contracts.target_B03` 与 `JurisLean.FullMath.Acceptance.target_B03`，以Lean赋值检查准确合同类型。
**执行证据：** 当前源文件、实际算法/检查器入口、正常与反例测试、具体类型与依赖、公理审计、同次GitHub运行。
**不能据此收工：** 文件存在、函数返回True、只import、只固定数字、把反射前提交给调用者、把注册范围自行缩小。

## B04｜民商与专门民事族完整分配

**原目标：** 在具名业务范围内，每个产生/消灭/抗辩/例外争点有且仅有解释后的责任政策。
**当前执行含义：** 在具名业务范围内，每个产生/消灭/抗辩/例外争点有且仅有解释后的责任政策。
**数学细节：** `MATHEMATICS_SPEC.md` 第10节。
**实现与证明位置：** `proofs/lean/juris_lean/JurisLean/FullMath/Law/CivilFamilies.lean`；优先复用旧 `B01–B22 issue templates; domain tasks` 与已有ULM定理，不平行重建。

**证明施工：**
1. 合同、物权、侵权、婚姻继承、劳动、公司、IP、金融等各自展开规范清单。
2. 对source_scope中的requiredSlots逐项比对，验证不是根据现有实现倒造需求全集。
3. 用真实/人工独立法律基准以及逐要素对照反例验证，不用LLM自造自判取代。
4. 全部14法律族中属民商的模型逐一编译，关联原134条实例，不只编号模板。
5. 法源审核结论作为明确输入，未审核不能冒称法律真值。

**必须导出：** `JurisLean.FullMath.Contracts.target_B04` 与 `JurisLean.FullMath.Acceptance.target_B04`，以Lean赋值检查准确合同类型。
**执行证据：** 当前源文件、实际算法/检查器入口、正常与反例测试、具体类型与依赖、公理审计、同次GitHub运行。
**不能据此收工：** 文件存在、函数返回True、只import、只固定数字、把反射前提交给调用者、把注册范围自行缩小。

## B05｜刑事责任链与证据排除

**原目标：** 定罪、量刑、合法性审查、自诉/公诉/特别程序使用各自政策。
**当前执行含义：** 定罪、量刑、合法性审查、自诉/公诉/特别程序使用各自政策。
**数学细节：** `MATHEMATICS_SPEC.md` 第10节。
**实现与证明位置：** `proofs/lean/juris_lean/JurisLean/FullMath/Law/CriminalFamilies.lean`；优先复用旧 `B23–B26 issue templates; criminal rule-pack task` 与已有ULM定理，不平行重建。

**证明施工：**
1. 罪刑法定、选定教义结构、构成与阻却事项定义为独立模型选择，不能借类比新增罪名。
2. 证明非法证据排除传递至全部依赖；综合剩余证据再评价，各定罪/量刑事实均有独立争点。
3. 证据不足法律后果只在法定就绪时点，软件超时不变成无罪判决；特别程序标准不复制定罪阈值。
4. 控方证明义务、阻却事由、非法证据、量刑和不同程序不是同一个布尔字段。
5. 逐被告主体、证据及其后果互不串用；不能用民事款项换姓名。

**必须导出：** `JurisLean.FullMath.Contracts.target_B05` 与 `JurisLean.FullMath.Acceptance.target_B05`，以Lean赋值检查准确合同类型。
**执行证据：** 当前源文件、实际算法/检查器入口、正常与反例测试、具体类型与依赖、公理审计、同次GitHub运行。
**不能据此收工：** 文件存在、函数返回True、只import、只固定数字、把反射前提交给调用者、把注册范围自行缩小。

## B06｜行政/复议/赔偿/程序专门链

**原目标：** 不同证明对象、机关、阶段、实体与程序后果不得串用。
**当前执行含义：** 不同证明对象、机关、阶段、实体与程序后果不得串用。
**数学细节：** `MATHEMATICS_SPEC.md` 第10节。
**实现与证明位置：** `proofs/lean/juris_lean/JurisLean/FullMath/Law/AdministrativeFamilies.lean`；优先复用旧 `B27–B37 templates; public/procedural rule-pack tasks` 与已有ULM定理，不平行重建。

**证明施工：**
1. 分别编译行政行为合法性、履责申请、损害与被告造成证明不能等规则。
2. 复议包含合法性/适当性，赔偿与仲裁按各自机构和规则，不把所有案件都变成民诉。
3. 2026新法新解释作用域与案件时点一致；具体未覆盖条目产生具名义务。
4. 行政审查对象、权限、程序、责任例外与救济种类具体化。
5. 复议、赔偿、执行和仲裁相关族均保留，不被单一撤销例子代替。

**必须导出：** `JurisLean.FullMath.Contracts.target_B06` 与 `JurisLean.FullMath.Acceptance.target_B06`，以Lean赋值检查准确合同类型。
**执行证据：** 当前源文件、实际算法/检查器入口、正常与反例测试、具体类型与依赖、公理审计、同次GitHub运行。
**不能据此收工：** 文件存在、函数返回True、只import、只固定数字、把反射前提交给调用者、把注册范围自行缩小。

## B07｜法源时间与语义覆盖

**原目标：** 法律覆盖complete相对于独立requiredSlots、例外和时间政策成立。
**当前执行含义：** 法律覆盖complete相对于独立requiredSlots、例外和时间政策成立。
**数学细节：** `MATHEMATICS_SPEC.md` 第10节。
**实现与证明位置：** `proofs/lean/juris_lean/JurisLean/FullMath/Law/TemporalCoverage.lean`；优先复用旧 `coverage registry production task` 与已有ULM定理，不平行重建。

**证明施工：**
1. 冻结公布/施行/废止、事件/处理时点与过渡规范；不使用最后抓取时间判定适用。
2. 对每个requiredSlot证明有准入解释或显式不适用见证；未知不能当不适用。
3. 证明规则版本变化使旧依赖缓存失效，证书不能跨法源/解释版本升级。
4. 按MATHEMATICS_SPEC相应章节的独立对象、算法不变量和证明路线完成。
5. 实际计算函数、输入校验和类型边界同时接入通用根；不得只登记字段。

**必须导出：** `JurisLean.FullMath.Contracts.target_B07` 与 `JurisLean.FullMath.Acceptance.target_B07`，以Lean赋值检查准确合同类型。
**执行证据：** 当前源文件、实际算法/检查器入口、正常与反例测试、具体类型与依赖、公理审计、同次GitHub运行。
**不能据此收工：** 文件存在、函数返回True、只import、只固定数字、把反射前提交给调用者、把注册范围自行缩小。

## G01｜效用与合法行动集

**原目标：** 策略优化只在LegalAction集合内，成本/概率/目标含明确来源。
**当前执行含义：** 策略优化只在LegalAction集合内，成本/概率/目标含明确来源。
**数学细节：** `MATHEMATICS_SPEC.md` 第12节。
**实现与证明位置：** `proofs/lean/juris_lean/JurisLean/FullMath/Decision/LegalUtility.lean`；优先复用旧 `reference/core.py mechanism and utility functions` 与已有ULM定理，不平行重建。

**证明施工：**
1. 区分法院可判集合、合法谈判集合、客户偏好。
2. 逐行动验证法律约束及依赖条件，收益不能抵消硬法律禁止。
3. 行为改变分布时显式建模，观察条件概率不能直接当干预效果。
4. 按MATHEMATICS_SPEC相应章节的独立对象、算法不变量和证明路线完成。
5. 实际计算函数、输入校验和类型边界同时接入通用根；不得只登记字段。

**必须导出：** `JurisLean.FullMath.Contracts.target_G01` 与 `JurisLean.FullMath.Acceptance.target_G01`，以Lean赋值检查准确合同类型。
**执行证据：** 当前源文件、实际算法/检查器入口、正常与反例测试、具体类型与依赖、公理审计、同次GitHub运行。
**不能据此收工：** 文件存在、函数返回True、只import、只固定数字、把反射前提交给调用者、把注册范围自行缩小。

## G02｜毛信息价值非负与净值

**原目标：** 固定模型且允许忽略信息 ⇒ VOI≥0；VOI-cost可为负。
**当前执行含义：** 固定模型且允许忽略信息 ⇒ VOI≥0；VOI-cost可为负。
**数学细节：** `MATHEMATICS_SPEC.md` 第12节。
**实现与证明位置：** `proofs/lean/juris_lean/JurisLean/FullMath/Decision/InformationValue.lean`；优先复用旧 `reference/core.py / information_value` 与已有ULM定理，不平行重建。

**证明施工：**
1. 取无信息最优行动a*，对每个观测z证明有信息max至少达到继续a*的期望。
2. 有限求和及全期望公式回到无信息值。
3. 考虑获取成功概率/合法性/成本另计，不将毛值非负扩展为取证必赚。
4. 按MATHEMATICS_SPEC相应章节的独立对象、算法不变量和证明路线完成。
5. 实际计算函数、输入校验和类型边界同时接入通用根；不得只登记字段。

**必须导出：** `JurisLean.FullMath.Contracts.target_G02` 与 `JurisLean.FullMath.Acceptance.target_G02`，以Lean赋值检查准确合同类型。
**执行证据：** 当前源文件、实际算法/检查器入口、正常与反例测试、具体类型与依赖、公理审计、同次GitHub运行。
**不能据此收工：** 文件存在、函数返回True、只import、只固定数字、把反射前提交给调用者、把注册范围自行缩小。

## G03｜和解个体理性与合法性

**原目标：** 合法交集中的s满足双方诉讼外部选项；不存在交集单独报告。
**当前执行含义：** 合法交集中的s满足双方诉讼外部选项；不存在交集单独报告。
**数学细节：** `MATHEMATICS_SPEC.md` 第12节。
**实现与证明位置：** `proofs/lean/juris_lean/JurisLean/FullMath/Decision/Bargaining.lean`；优先复用旧 `reference/core.py / settlement_bounds` 与已有ULM定理，不平行重建。

**证明施工：**
1. 用双方各自主观期望与两类成本推导L、U，不假定双方有同一概率。
2. 证明s∈[L,U]等价双方线性IR；再与LegalAction求交。
3. 风险厌恶/履行不确定时改效用而非继续线性公式；有约束不擅自使用中点。
4. 按MATHEMATICS_SPEC相应章节的独立对象、算法不变量和证明路线完成。
5. 实际计算函数、输入校验和类型边界同时接入通用根；不得只登记字段。

**必须导出：** `JurisLean.FullMath.Contracts.target_G03` 与 `JurisLean.FullMath.Acceptance.target_G03`，以Lean赋值检查准确合同类型。
**执行证据：** 当前源文件、实际算法/检查器入口、正常与反例测试、具体类型与依赖、公理审计、同次GitHub运行。
**不能据此收工：** 文件存在、函数返回True、只import、只固定数字、把反射前提交给调用者、把注册范围自行缩小。

## G04｜有限DSIC/BIC、参与与预算

**原目标：** 全类型报告组合上的不等式都成立才通过相应机制标签。
**当前执行含义：** 全类型报告组合上的不等式都成立才通过相应机制标签。
**数学细节：** `MATHEMATICS_SPEC.md` 第12节。
**实现与证明位置：** `proofs/lean/juris_lean/JurisLean/FullMath/Decision/IncentiveCompatibility.lean`；优先复用旧 `reference/core.py / verify_mechanism` 与已有ULM定理，不平行重建。

**证明施工：**
1. 枚举真实类型、误报和他人类型，逐一计算同一真实类型效用。
2. DSIC逐点，BIC使用具名正概率条件分布；证明枚举覆盖和判定反射。
3. 合法结果、IR、预算平衡单独检查后组合；不宣称同时获得未证明的完全效率。
4. 按MATHEMATICS_SPEC相应章节的独立对象、算法不变量和证明路线完成。
5. 实际计算函数、输入校验和类型边界同时接入通用根；不得只登记字段。

**必须导出：** `JurisLean.FullMath.Contracts.target_G04` 与 `JurisLean.FullMath.Acceptance.target_G04`，以Lean赋值检查准确合同类型。
**执行证据：** 当前源文件、实际算法/检查器入口、正常与反例测试、具体类型与依赖、公理审计、同次GitHub运行。
**不能据此收工：** 文件存在、函数返回True、只import、只固定数字、把反射前提交给调用者、把注册范围自行缩小。

## G05｜均衡/策略近似误差

**原目标：** maximum regret≤ε ⇒ 在声明有限游戏上的ε均衡。
**当前执行含义：** maximum regret≤ε ⇒ 在声明有限游戏上的ε均衡。
**数学细节：** `MATHEMATICS_SPEC.md` 第12节。
**实现与证明位置：** `proofs/lean/juris_lean/JurisLean/FullMath/Decision/RegretCertificates.lean`；优先复用旧 `reference/core.py / nash_regrets` 与已有ULM定理，不平行重建。

**证明施工：**
1. 完整枚举单方偏离，按固定对手策略计算收益差。
2. 精确有理数或外向数值界验证所有差值≤ε。
3. 若只搜索部分偏离，不得以当前最大regret充当全局上界；将未搜索部分纳入外包。
4. 按MATHEMATICS_SPEC相应章节的独立对象、算法不变量和证明路线完成。
5. 实际计算函数、输入校验和类型边界同时接入通用根；不得只登记字段。

**必须导出：** `JurisLean.FullMath.Contracts.target_G05` 与 `JurisLean.FullMath.Acceptance.target_G05`，以Lean赋值检查准确合同类型。
**执行证据：** 当前源文件、实际算法/检查器入口、正常与反例测试、具体类型与依赖、公理审计、同次GitHub运行。
**不能据此收工：** 文件存在、函数返回True、只import、只固定数字、把反射前提交给调用者、把注册范围自行缩小。

## C01｜关系组合健全/完备

**原目标：** 局部关系包含/相等通过共同见证关联后在总关系中保持。
**当前执行含义：** 局部关系包含/相等通过共同见证关联后在总关系中保持。
**数学细节：** `MATHEMATICS_SPEC.md` 第14节。
**实现与证明位置：** `proofs/lean/juris_lean/JurisLean/FullMath/Composition/SharedRelations.lean`；优先复用旧 `unified/contract.py / relation_join` 与已有ULM定理，不平行重建。

**证明施工：**
1. 对两步用存在见证消去/引入证明包含或双向包含。
2. 证明结合律，再对管线长度归纳。
3. 实例化每一接口的反射/依赖条件，不能仅在抽象变量上证明后直接宣布整个JC精化。
4. 按MATHEMATICS_SPEC相应章节的独立对象、算法不变量和证明路线完成。
5. 实际计算函数、输入校验和类型边界同时接入通用根；不得只登记字段。

**必须导出：** `JurisLean.FullMath.Contracts.target_C01` 与 `JurisLean.FullMath.Acceptance.target_C01`，以Lean赋值检查准确合同类型。
**执行证据：** 当前源文件、实际算法/检查器入口、正常与反例测试、具体类型与依赖、公理审计、同次GitHub运行。
**不能据此收工：** 文件存在、函数返回True、只import、只固定数字、把反射前提交给调用者、把注册范围自行缩小。

## C02｜外包络组合

**原目标：** Ti(γi(ai))⊆γi+1(Ti# ai) ⇒ 全管线外包正确。
**当前执行含义：** Ti(γi(ai))⊆γi+1(Ti# ai) ⇒ 全管线外包正确。
**数学细节：** `MATHEMATICS_SPEC.md` 第14节。
**实现与证明位置：** `proofs/lean/juris_lean/JurisLean/FullMath/Composition/AbstractProducts.lean`；优先复用旧 `unified/contract.py` 与已有ULM定理，不平行重建。

**证明施工：**
1. 用具体状态在当前γ内的归纳不变量。
2. 应用各模块外包变换健全性，再绑定同一模型/假设及公共参数。
3. 保留输入间相关性；按各局部独立极值拼出来的端点未必可达，只声明覆盖。
4. 按MATHEMATICS_SPEC相应章节的独立对象、算法不变量和证明路线完成。
5. 实际计算函数、输入校验和类型边界同时接入通用根；不得只登记字段。

**必须导出：** `JurisLean.FullMath.Contracts.target_C02` 与 `JurisLean.FullMath.Acceptance.target_C02`，以Lean赋值检查准确合同类型。
**执行证据：** 当前源文件、实际算法/检查器入口、正常与反例测试、具体类型与依赖、公理审计、同次GitHub运行。
**不能据此收工：** 文件存在、函数返回True、只import、只固定数字、把反射前提交给调用者、把注册范围自行缩小。

## C03｜情景法律集合→概率/金额桥

**原目标：** Σx px min/max_{y∈Sx} 指示函数提供允许事件概率外界。
**当前执行含义：** Σx px min/max_{y∈Sx} 指示函数提供允许事件概率外界。
**数学细节：** `MATHEMATICS_SPEC.md` 第14节。
**实现与证明位置：** `proofs/lean/juris_lean/JurisLean/FullMath/Composition/LegalProbability.lean`；优先复用旧 `reference/core.py / scenario_event_bounds` 与已有ULM定理，不平行重建。

**证明施工：**
1. 对每个实际选择yx∈Sx应用min/max界。
2. 非负权重求和保持不等式。
3. 若要声明精确端点，证明联合选择可行/跨情景矩形性；缺情景概率质量用P09，不重归一化遮蔽。
4. 按MATHEMATICS_SPEC相应章节的独立对象、算法不变量和证明路线完成。
5. 实际计算函数、输入校验和类型边界同时接入通用根；不得只登记字段。

**必须导出：** `JurisLean.FullMath.Contracts.target_C03` 与 `JurisLean.FullMath.Acceptance.target_C03`，以Lean赋值检查准确合同类型。
**执行证据：** 当前源文件、实际算法/检查器入口、正常与反例测试、具体类型与依赖、公理审计、同次GitHub运行。
**不能据此收工：** 文件存在、函数返回True、只import、只固定数字、把反射前提交给调用者、把注册范围自行缩小。

## C04｜具体规范—概率—金额—策略联合实例

**原目标：** 两个付款情景的完整集合、胜率1-p、期望D-pC与和解IR在一个定理中成立。
**当前执行含义：** For every well-formed supported payment instance: exact scenario relation, clipped balance C, overpayment U, event law, expectation and lawful bargaining are linked by one input; E[C]-E[U]=P-sum(q_j P(A_j)), not E[C]=P-sum(q_j P(A_j)) without no-overpay premise.
**数学细节：** `MATHEMATICS_SPEC.md` 第14节。
**实现与证明位置：** `proofs/lean/juris_lean/JurisLean/FullMath/Composition/ParametricDebtDecision.lean`；优先复用旧 `unified/pipeline.py` 与已有ULM定理，不平行重建。

**证明施工：**
1. 完整枚举Bool情景并证明独立金额谓词覆盖。
2. 在D-C<T≤D条件下代入目标指示函数，证明pwin=1-p与期望恒等式。
3. 把同语境下金额/预测接IR选择，整条结论由实质局部引理组合，不由一个假设Φ全真得出。
4. 将原due-p*paid的本金期望写法修成E[C]-E[U]守恒；无超付前提才可化简。
5. 对任意合法参数和有限付款集合证明；单例1000/300不能关闭。

**必须导出：** `JurisLean.FullMath.Contracts.target_C04` 与 `JurisLean.FullMath.Acceptance.target_C04`，以Lean赋值检查准确合同类型。
**执行证据：** 当前源文件、实际算法/检查器入口、正常与反例测试、具体类型与依赖、公理审计、同次GitHub运行。
**不能据此收工：** 文件存在、函数返回True、只import、只固定数字、把反射前提交给调用者、把注册范围自行缩小。

## C05｜全领域条件链与假设隔离

**原目标：** 每个注册领域的条件后果保持原假设ID，不生成正式事实或法院行为。
**当前执行含义：** 每个注册领域的条件后果保持原假设ID，不生成正式事实或法院行为。
**数学细节：** `MATHEMATICS_SPEC.md` 第14节。
**实现与证明位置：** `proofs/lean/juris_lean/JurisLean/FullMath/Composition/MultiDomain.lean`；优先复用旧 `unified/pipeline.py / all_fields_demo` 与已有ULM定理，不平行重建。

**证明施工：**
1. 共用B01/B02引擎，领域差异只由已选具名政策输入。
2. 对37模板分别跑成功、未证、未就绪、角色错误、版本错误的分支。
3. 实际领域完整性仍需B04/B05/B06的规则包，不把模板运行数说成法律覆盖率。
4. 按MATHEMATICS_SPEC相应章节的独立对象、算法不变量和证明路线完成。
5. 实际计算函数、输入校验和类型边界同时接入通用根；不得只登记字段。

**必须导出：** `JurisLean.FullMath.Contracts.target_C05` 与 `JurisLean.FullMath.Acceptance.target_C05`，以Lean赋值检查准确合同类型。
**执行证据：** 当前源文件、实际算法/检查器入口、正常与反例测试、具体类型与依赖、公理审计、同次GitHub运行。
**不能据此收工：** 文件存在、函数返回True、只import、只固定数字、把反射前提交给调用者、把注册范围自行缩小。

## C06｜实际JC实现—独立checker—规格对应

**原目标：** checker接受本次运行见证 ⇒ 属于该版本独立Solutions。
**当前执行含义：** Within LMM, prove the generic executable certified checker/contract and reference witness mapping. Real JC public-entry and Harness custody adapters are separately tracked as deferred production obligations; do not call original C06 fully deployed.
**数学细节：** `MATHEMATICS_SPEC.md` 第14节。
**实现与证明位置：** `proofs/lean/juris_lean/JurisLean/FullMath/Composition/CertifiedCheckerExecution.lean`；优先复用旧 `JC production task; not completed in this package` 与已有ULM定理，不平行重建。

**证明施工：**
1. 将真实Application公共入口的输入/中间工件翻译至形式对象，证明解析与绑定保持。
2. 独立checker不得调用主求解器来验证其结果，逐步验证规则/攻击/扩展/数值/模型证书。
3. 对每个运行转换证明向前模拟；成功终态输出满足规范，所有open义务继续保留；多入口语义一致。
4. 本轮在LMM完成可执行认证checker的普遍健全、证书输入与语义对应。
5. JC真实公开入口的绑定列入C06-PRODUCTION，按用户要求后置；不把数学层等同生产部署。

**必须导出：** `JurisLean.FullMath.Contracts.target_C06` 与 `JurisLean.FullMath.Acceptance.target_C06`，以Lean赋值检查准确合同类型。
**执行证据：** 当前源文件、实际算法/检查器入口、正常与反例测试、具体类型与依赖、公理审计、同次GitHub运行。
**不能据此收工：** 文件存在、函数返回True、只import、只固定数字、把反射前提交给调用者、把注册范围自行缩小。

## C07｜统一总正确性与声明降级

**原目标：** Complete⇒等式；Partial⇒子集；Envelope⇒全称外包；无经验核验不发经验标签。
**当前执行含义：** Complete⇒等式；Partial⇒子集；Envelope⇒全称外包；无经验核验不发经验标签。
**数学细节：** `MATHEMATICS_SPEC.md` 第14节。
**实现与证明位置：** `proofs/lean/juris_lean/JurisLean/FullMath/Composition/UniversalBusinessRoot.lean`；优先复用旧 `unified/contract.py / validate_claim_level` 与已有ULM定理，不平行重建。

**证明施工：**
1. 把C06的每个实质反射引理实例化到联合见证Φ，闭合全链存在中间值。
2. 完整性要求各所有分支、候选覆盖、模型/政策范围都无未决；任一局部partial不能被展示升级。
3. 数学/法律/经验三类证据不同字段；注册表依赖可达只检查遗漏，不替代此组合证明。
4. 根从共享输入出发串联实际模块；不是把完成标签合取。
5. 模式分型：Exact等式、Inner包含、Outer外包、统计事件及δ不丢；业务输出与检查器验证的观察一致。

**必须导出：** `JurisLean.FullMath.Contracts.target_C07` 与 `JurisLean.FullMath.Acceptance.target_C07`，以Lean赋值检查准确合同类型。
**执行证据：** 当前源文件、实际算法/检查器入口、正常与反例测试、具体类型与依赖、公理审计、同次GitHub运行。
**不能据此收工：** 文件存在、函数返回True、只import、只固定数字、把反射前提交给调用者、把注册范围自行缩小。
