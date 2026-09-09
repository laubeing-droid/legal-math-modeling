# 当前主线：有限本金业务端到端根精化

此文是任务细化，不是已完成证明。实际参考根：`tools/business_relations/reference/delivery_bundle.py::check_business_bundle`。已有代码直接复用；不重复新增“approved_model_id”，不机械补DecidableEq，不修改rawBalance定理使它假装等于clipped余额。

## 1. 独立对象和量词

冻结业务Q为`SYNTHETIC_EXACT_PRINCIPAL_ANALYTICS_TWO_FILES/1`；已选I0=(spec,m,Q)，m定义权重、阈值、成本及允许格，来源为明确合成输入。未来扩展任意Q时须另定义答案类型及语义，不能把Q开放成自选回调。

定义有限命题集合A、已知事实F、共同条件Γ、带来源的付款集合Pmt；不得从result提取A或从已找到世界定义Ω。

Ω(I0)={ξ:A→Bool | ξ扩张F ∧ ξ⊨Γ}。

W是一张无重复世界的业务结果关系，每个行o携带ξ、主体/债项/源版本及(Cξ,Uξ)。Worlds(W)=Ω(I0)。

JointSem_principal(I0,W)独立要求：
1. 当前任务和所有行的语义身份一致；来源跨度、观察时点及声明参数与I0一致。
2. 每笔付款只能用于其绑定债项，按ξ中相应认定条件计入；Rξ=P−Σq_j1_Aj(ξ)。
3. Cξ,Uξ≥0，CξUξ=0，Cξ−Uξ=Rξ。
4. m对Ω恰好给出非负归一化权重；重复、缺项、外来世界均不能默默丢弃或重归一化。
5. Analytics.expected=Σpξ Cξ，超付期望=Σpξ Uξ；阈值概率=Σpξ1_{Cξ≥t}。
6. 在本固定共同信念模型中l=μC−cP+sP,u=μC+cD−sD，eligible=A_L∩[l,u]。所选格成员或空值遵守任务规则。
7. 条件、模型地位、数值对象及完成范围保持；不把超付残差说成现实返还权已成立。

TaskSat_Q(W,m)独立要求当前任务应完成的内容，不仅是字段存在。Q要求精确全部情景及Analytics，因此部分结果可返回参考诊断，但不能接受为这项完整业务完成。

Protected_Q按上述独立对象生成抽象受保护记录，不调用现有renderer。定义ReadText和ReadJSON的受限文法与解析语义；ReadBoth(d1,d2)是两份实际字节的联合读回结果。

## 2. 固定总式

WF(I0) ∧ CheckBusinessBundle(I0,π,d1,d2)=accept ⇒
∃W, Worlds(W)=Ω(I0) ∧ JointSem_principal(I0,W) ∧
TaskSat_Q(W,m) ∧ ReadBoth(d1,d2)=Protected_Q(W,m)。

这一式允许明确的参数条件，但不能在WF中直接写入根结论，也不能用`check==true`定义JointSem。

## 3. 从现有函数到定理的具体分工

| 现有代码/数据 | 拟证明目标 | 不能替代它的现有结果 |
|---|---|---|
| context.py / canonical_json | 受支持结构的无损编解码；输入键和数值域映射到Lean | 字段个数一致、hash相同 |
| delivery_bundle.snapshot_inputs | 输入选定时内容快照忠实；宿主取源不由生成者控制 | 一个字符串叫approved_model_id |
| compile/execute / denote | 真栈执行与独立条件含义对应 | 只有eval递归语义反射 |
| solver_worlds/checker_worlds | 两种枚举各与独立Ω健全且覆盖 | 两算法在几个例子上一致 |
| business.check | 实际检查接受→逐世界守恒互补、覆盖和模式要求 | 输入格式正确、重复调用solver |
| derive/check_analytics | 独立求和与目标事件、允许格及已选m对应 | 原始残差E[R]的代数定理 |
| verify_document | 本金文本语法、解释、完整覆盖及不多说 | 文件存在、renderer能生成 |
| verify_calculation_json | 实际JSON解析/类型重建/重复键与数值拒绝→Analytics语义 | 内存Analytics通过 |
| check_business_bundle | 在同一I0下抽出共同W并建立TaskSat及ReadBoth等式 | 三个检查函数为true的合取 |

## 4. 推荐Lean文件落点（待施工，不提供伪完成空体）

复用`JurisLean.BusinessRelations`与`BusinessRelationsDelta`。新增具体业务子目录可采用：
- `JurisLean/BusinessRoot/Semantics.lean`：WF、Ω、JointSem、TaskSat、Protected的独立语义。
- `InputCodec.lean`：当前Context/有理数/日期/结构的表示及refinement。
- `GuardMachine.lean`：真正栈编译/执行的归纳证明。
- `PrincipalChecker.lean`：枚举/唯一余额/实际结果checker反射。
- `Analytics.lean`：多世界C/U、阈值与行动格，调用已存8条草稿的适用实例。
- `ArtifactParser.lean`：两文件受限语法、解析及受保护记录。
- `Root.lean`：一条实际端到端根定理；先用具体函数而非高阶任意predicate。

Lean中另写一个镜像算法不自动证明Python。必须明确选择并完成：可检查执行见证＋已证独立checker、受限程序翻译/验证、或代码生成后唯一运行实现。既有交叉测试可以继续提供工程证据，但不能标kernelVerified。采用哪条路径应在ROOT03/05记录，并说明Python、字节/JSON库和宿主I0来源的TCB边界。

## 5. 根接受的最小证据

每次关闭ROOT06/08，至少同时核对：
- 固定独立语义与Q的版本，不借更窄新Q悄悄完成旧任务；
- 实际根声明的完整类型，输入/输出函数确实是该次实现；
- 各局部健全性、覆盖和解析前提已实例化；定义/证明依赖不隐藏根命题；
- GitHub编译、公理环境报告、主体commit/tree/run/attempt一致；
- 来源/模型/文件扰动反例与真实两文件回读；
- 运行实现的保证级别（crossCheckOnly、证明检查器或已证生成代码）如实声明；
- 宿主既有MatterStore/CAS选定I0，外部生成结果不能选择expected。

声明数量、imports、graph reachability只检查遗漏，不满足上述条件。当前`Consolidated.All`只是导入文件，不能作为Root.lean的替身。

## 6. 有限数学样本固定

超付：P=100,q=300,p=2/5；E[R]=-20,E[C]=60,E[U]=80，且P(C≥0)=1、P(R≥0)=3/5。

主例：P=1000,q=300,p=2/5；μC=880，阈值800事件概率3/5；成本(100,60,10,10)得[790,930]，允许格{600,850,1100}得唯一eligible=850；860虽处于区间内但不在允许格。所有参数均为合成，不声称真实胜率或法定和解许可。

两份文件须共同读取：正文正确JSON错、JSON正确正文无条件化、同版本m整体替换、pending伪完整、两个来源快照混用均拒绝。

## 7. 保持其他任务不被吞掉

有限本金根完成不关闭D001–134、全领域规则、完整DOCX显示语义、真实胜率或任何外部审批。它提供可复用的根模式与精化资产。后续每项需求继续按M族/七轴映射实例化，不把本例当成所有法律问题的抽象代表已经全证。
