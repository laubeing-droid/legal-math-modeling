# 可执行法律推理的可组合保证：一种受发布边界约束的形式架构

Laupinco

## Abstract

**FORMALIZED.** This article presents a compositional architecture for executable legal reasoning organized around sixteen Unified Legal Modules, ULM01–16. The checked boundary includes request and context carriers, fail-closed outcomes, request-bound typed graphs, proof obligations, machine-run identity, admitted-versus-assumed premise dependencies, finite Horn closure, well-founded support arguments, typed attacks and policy-resolved defeats, Dung semantics, branch-sensitive queries, request-bound procedure results, exact rational expressions indexed by dimension, non-escalating trust and assurance, add-only Horn refinement, conditional Banach results, and four concrete composition instances. Separate supporting files formalize selected temporal, receipt, and taint predicates. These declarations validate only their stated fields and hypotheses; they do not authenticate sources, determine who possesses real-world authority, or manufacture substantive legal correctness.

**DERIVED.** Release assurance is evaluated against a fixed subject, source tree, workflow run, staged certificate states, controlled mutations, and cross-repository refinement receipts. For the reported release boundary, 97 jobs succeeded, including a 91-module matrix, while the clean-build log reported 2,993 completed jobs. The axiom audit enumerated 145 declarations for the complete ULM scope and 27 declarations for the core composition scope, with no project-specific axioms beyond `propext`, `Classical.choice`, and `Quot.sound`. Forty-six of forty-six controlled mutations were killed, and three named cross-repository fixtures produced passing refinement receipts. These finite observations support a bounded release claim, not universal legal correctness, probabilistic calibration, or refinement for all inputs. A worked fictional case demonstrates end-to-end traceability from request identity to human receipt and release evidence.

Keywords: executable legal reasoning; compositional assurance; formal methods; argumentation; provenance; release boundary; human authorization

## 中文摘要

**FORMALIZED.** 本文提出由ULM01—16构成的可执行法律推理形式架构，覆盖请求与上下文载体、失败封闭结果、请求绑定的类型图、证明义务、机器运行身份、采信与假设前提依赖、有限Horn闭包、良基支持论证、类型化攻击与政策解析击败、Dung语义、分支查询、请求绑定的程序结果、按量纲索引的精确有理数表达式、信任与保证不升级、Horn只增量精化、带明确前提的Banach结果及四个具体组合实例。其他支持文件形式化了有限的时间、回执与污染谓词。这些声明只验证明示字段和前提，不认证来源，不决定现实中的权限归属，也不生成实体法律正确性。

**DERIVED.** 在固定subject、tree与运行编号的发布边界内，97个作业成功，其中包括91模块矩阵，clean build日志报告2993个completed jobs；145个全量ULM声明与27个核心组合声明完成公理审计，未见项目自定义公理。46/46个受控变异被杀死，三个命名夹具形成通过的跨仓精化回执。上述证据支持有限发布保证，但不推出全输入正确性、概率校准、隐私保证、解释质量或法律责任归属。

关键词：可执行法律推理；可组合保证；形式方法；法律论证；来源追踪；发布边界；人工授权

## 1 引言

**CONJECTURE.** 可执行法律推理的主要困难并非把更多法律概念编码为对象，而是说明不同对象之间的保证怎样组合、组合后仍能观察到什么，以及软件发布证据究竟约束哪个版本。若请求、事实、规则、论证、程序、金额和裁决回执分别通过测试，却缺少跨层不变量，局部成功仍可能在接口处产生不可见的语义漂移。

**DERIVED.** 法律推理系统至少面对三种不能相互替代的正确性。第一是形式正确性，即定义和定理在给定前提下成立；第二是执行一致性，即实际程序与形式接口在命名输入上产生一致观测；第三是实体法律正确性，即事实认定、规范解释和裁量具有适当法律依据。前两者可以提供第三者所需的审计条件，却不能单独推出第三者。

**CONJECTURE.** 既有法律论证研究解释了可废止推理、攻击关系与制度因素 [@Dung1995; @PrakkenSartor1997; @ModgilPrakken2013]，形式验证研究提供了程序不变量、模型检查和交互式证明技术 [@Hoare1969; @Pnueli1977; @ClarkeEtAl1986; @DeMouraUllrich2021]。然而，从法律输入到发布证书的端到端组合边界仍常被拆散报告，导致“已证明”“已测试”和“可发布”在工程叙述中被不当地互换。

**DERIVED.** 本文的贡献是给出一个受发布边界约束的组合框架：ULM01—15提供各自的具体结构与选定不变量，ULM16汇总四个具体组合实例；论文再据此组织证据账本，区分形式化、推导和猜想。本文不把软件执行包装为法律裁决，也不把有限变异结果包装为普遍正确性定理。

## 2 相关工作与缺失的保证边界

**DERIVED.** Dung框架以抽象攻击关系刻画可接受性，后续工作引入偏好、价值与结构化论证 [@Dung1995; @BenchCapon2003; @BenchCaponSartor2003; @ModgilPrakken2013]。案例推理和规则例外研究进一步表明，法律结论通常依赖争点、相似性选择和可废止前提 [@RisslandAshley1987; @Horty2011; @Reiter1980; @AntoniouEtAl2001]。这些理论适于描述推理关系，但不会自动绑定某次请求、某批事实来源或某次软件运行。

**DERIVED.** Horn逻辑、Tarski不动点和抽象解释为闭包及近似正确性提供了成熟基础 [@Horn1951; @Tarski1955; @CousotCousot1977]。规范逻辑则讨论义务、许可及输入输出关系 [@VonWright1951; @MakinsonVanDerTorre2000]。缺口不在逻辑表达力本身，而在工程系统能否证明规则闭包使用了预期的有限载体，并将其结果无损地交给后续论证与程序模块。

**CONJECTURE.** 贝叶斯网络和证据概率模型可用于表达不确定性 [@FentonNeilLagnado2013; @VlekEtAl2015; @FentonNeilBerger2016; @TaroniEtAl2014]，解释方法研究则提出局部代理、反事实和可解释性分类 [@RibeiroEtAl2016; @Lipton2018; @GuidottiEtAl2018; @WachterEtAl2018]。本文不形式化概率校准、类比强度或解释质量；这些量若进入实现，只能作为经验字段，并不得静默升级为规范结论。

**CONJECTURE.** 差分隐私及其组合理论具有严格数学定义 [@DworkEtAl2006; @NissimEtAl2007; @DworkRoth2014; @AbadiEtAl2016]，人工智能责任与产品责任则依赖制度规范和事实判断 [@Hacker2023; @BuitenEtAl2021; @EU2024AIAct; @EU2024ProductLiability]。本架构既不声称实现差分隐私，也不从模型输出推导责任主体；其缺失的保证边界被显式保留，而非由形式化外观掩盖。

## 3 方法：模型、论断与组合条件

### 3.1 类型化保证接口

**DERIVED.** 为便于论文分析，本文把每个模块接口写成输入类型、输出类型、前提、保证与可观察量的五元组，并把证据等级视为不允许无证升级的报告纪律。这个五元组和证据等级偏序不是仓库中的统一Lean数据类型；真正的形式结论来自各模块的具体结构与定理。

\[
\mathcal E=\{\bot,\mathsf{Conjecture},\mathsf{Derived},\mathsf{Formalized}\},
\qquad
\bot\preceq\mathsf{Conjecture}\preceq\mathsf{Derived}\preceq\mathsf{Formalized}.
\tag{1}
\]

**DERIVED.** `Formalized`只覆盖固定Lean源码中实际定义或定理的范围；`Derived`覆盖由证据产物、公式和已述前提推出的结论；`Conjecture`覆盖经验、规范、概率与尚未证明的主张。该纪律阻止测试通过被改写成定理，也阻止定理在未满足法律前提时被改写成法律意见。

### 3.2 威胁模型

**CONJECTURE.** 威胁主体包括无意的适配器错误、过期规则输入、来源丢失、权限误配、运行与源码错绑、测试对实现缺陷的不敏感，以及将经验评分解释为法律效力的报告者。本文不假设恶意攻击者已经突破编译器、Git对象模型、托管平台或Lean可信计算基；供应链攻击、密钥泄露和宿主机入侵因缺乏证据而不在证明范围内。

**DERIVED.** 可观察风险集中在四条边界：外部法律输入进入核心、模块之间变换、人工裁决回流、发布证据绑定。系统因此采取边界验证和内部类型信任：只有外部请求、文件、权限回执及发布材料接受必要校验，内部函数不层层重复防御。

### 3.3 有限载体证明策略

**FORMALIZED.** ULM07—10针对固定有限规则、事实和论证集合证明闭包终止与语义存在性。有限载体允许把集合运算降为可判定枚举，但“对给定有限载体成立”不等同于“对任意现实法律体系完备”。

**DERIVED.** 这一策略把证明目标限制为可复核对象：规则集、节点集、攻击集和分支键必须显式出现。新增规则或论证节点会形成新的证明实例，不得援引旧载体上的结论直接覆盖新载体。

### 3.4 法律输入独立前提

**DERIVED.** 仓库把若干关键法律条件拆成独立字段或前提，例如请求与版本、事实采信状态、击败政策、证明标准和请求绑定的裁决权限。它没有一个统一结构覆盖法律资格、地域效力、裁量政策与所有时效规则，也没有通用定理拒绝每一种现实法律缺陷。可证明的只是各具体构造在明示前提下不会把机器建议自动转化为裁决结果。

**CONJECTURE.** 这一边界符合可操作的责任分配：模型可以提出候选结构，验证门决定结构是否满足，形式内核处理已声明关系，获授权的人类或制度承担法律判断。何者应获授权、怎样分配最终责任仍是规范和制度问题，而非Lean可判定命题。

### 3.5 论断纪律

**DERIVED.** 本文按“对象—前提—证据—边界”记录论断。若某个结论缺少其所需前提，则结果不是弱化为模糊成功，而是进入失败封闭结果；若证据仅覆盖三个夹具，则分母保持为三，不扩写为“跨仓精化已普遍证明”。

## 4 ULM01–04

### 4.1 ULM01：请求标识与normal form

**FORMALIZED.** ULM01中的上下文键由`caseScope`、`runScope`、`scenario`、`baseVersion`和`subjectVersion`组成；请求键再加入`profile`、`query`与`mappingVersion`。良构条件只断言运行范围所属案件与上下文案件相同。源码没有另设主体、时间、载荷摘要或模式字段，也没有把文本相似定义为请求同一。

\[
\begin{aligned}
\operatorname{ContextKey}&=(caseScope,runScope,scenario,baseVersion,subjectVersion),\\
\operatorname{RequestKey}&=(context,profile,query,mappingVersion),\\
\operatorname{WellFormed}(r)&\iff r.context.runScope.caseScope=r.context.caseScope.
\end{aligned}
\tag{2}
\]

**FORMALIZED.** `NormalForm`是一个记录类型，包含请求键、有限事实集、有限规则集和活动领域集。ULM01并没有定义规范化函数、幂等定理或请求等价关系；若未来加入序列化规范化，必须另行定义并证明其保持哪些观察量。

\[
\operatorname{NormalForm}=(request,facts,rules,activeDomains),
\qquad facts,rules,activeDomains\text{ 均为有限集}.
\tag{3}
\]

### 4.2 ULM02：失败封闭结果

**FORMALIZED.** ULM02的结果类型有`complete`、携带非空开放义务的`partialResult`和携带`FailureCore`的`failure`三种构造。源码不把“权限不足”或“类型冲突”硬编码为专门失败标签；这些原因若出现，只能进入`FailureCore.reason`或外部约定。`Outcome.map`保持partial与failure构造，不把它们升级为complete。

\[
\operatorname{Outcome}(\alpha)=
\mathsf{complete}(\alpha)\;\uplus\;
\mathsf{partialResult}(\alpha,O,O\neq\varnothing)\;\uplus\;
\mathsf{failure}(FailureCore),
\quad
map_f(\mathsf{failure}(e))=\mathsf{failure}(e).
\tag{4}
\]

### 4.3 ULM03：类型化转换图

**FORMALIZED.** ULM03定义有限`TypedGraph`，其中节点带`NodeKind`，边带`EdgeKind`、请求、源节点集、目标节点集和声明集。类型化体现为有限枚举标签与载体成员关系；源码没有为每个节点配置依赖类型化的输入输出类型，也没有证明下式所写的通用类型等式。

\[
G=(request,nodes,edges),\qquad
\operatorname{EdgeWF}(G,e)\Rightarrow
e.request=G.request\land e.src\subseteq G.nodes\land e.tgt\subseteq G.nodes.
\tag{5}
\]

\[
\operatorname{LocalTransition}(G,s,t)\Rightarrow
t.request=s.request,
\qquad
\operatorname{applyEdge}(e,s).active=s.active\cup e.tgt.
\tag{6}
\]

**DERIVED.** 式（6）只证明一次局部边应用保持请求并增加声明目标，不证明任意外部模块的输入输出类型已经匹配，也不证明边的法律语义正确。更强的组合接口是论文设计目标，而不是ULM03现成定理。

### 4.4 ULM04：证明义务

**FORMALIZED.** ULM04根据边种类与声明生成`ObligationKind`有限集，并无条件插入`typeSafety`，从而证明每条边的所需义务非空。源码没有为每条边统一定义`Pre/Post/Inv/Fail`四元组；义务含义由另行给出的`goal : ProofSubject → Prop`解释。

\[
\mathcal O(e)=\{\mathsf{typeSafety}\}\cup
\operatorname{toFinset}\!\left(
\operatorname{flatMap}(\operatorname{obligationsForClaim},
\operatorname{baselineClaims}(e.kind)\mathbin{+\!+}e.claims)
\right),
\qquad \mathcal O(e)\neq\varnothing.
\tag{7}
\]

**FORMALIZED.** verifier的soundness是单向含义：接受蕴含相应义务在给定语义中成立；拒绝不必证明对象错误，可能只是证据不足。

\[
\operatorname{VerifierSound}(goal,v)\land\operatorname{Sat}(v,s)
\Rightarrow
s.obligation\in\mathcal O(s.edge)\land goal(s).
\tag{8}
\]

## 5 ULM05–07

### 5.1 ULM05：机器执行保持身份

**FORMALIZED.** ULM05把机器建模为`running RunConfig`或`halted SemResult`，并证明单步`Step`与有限运行`Run`保持`RequestKey`。源码没有“产生新请求并记录父子关系”的转移；任何新请求工作流都属于形式模型之外的扩展。

\[
\langle s_i,r\rangle
\xrightarrow{\;m_i\;}
\langle s_{i+1},r\rangle,
\qquad
\operatorname{request}(s_i)=\operatorname{request}(s_{i+1}).
\tag{9}
\]

**DERIVED.** 身份保持解决的是“该结果属于哪个请求”，而非“结果是否符合法律”。它使缓存、重试和并行执行可被审计，也使错误地复用另一主体结果成为可检测的接口违例。

### 5.2 ULM06：事实provenance与taint

**FORMALIZED.** ULM06区分`FactAssessment`、`EvidenceToken`、`AssumptionWitness`与`PremiseToken`。证据令牌记录证据标识、事实、`SourceLocator`和请求；前提来源只有`admitted`与`assumed`两类，假设依赖以有限标识集显式保留。它不记录获取时间、规范化变换、签名者、有效区间或通用taint字段。

\[
\operatorname{EvidenceToken}=(evidenceId,fact,source,request),
\qquad
\operatorname{PremiseOrigin}=\mathsf{admitted}(a)\uplus\mathsf{assumed}(w).
\tag{10}
\]

\[
\operatorname{dependencies}(p)=
\begin{cases}
\varnothing,&p.origin=\mathsf{admitted}(a),\\
\{w.assumptionId\},&p.origin=\mathsf{assumed}(w).
\end{cases}
\tag{11}
\]

**DERIVED.** 来源定位与前提类别并非真实性定理。它们回答“哪个令牌声称来自何处、该前提是采信还是假设”，却不证明来源真实或采信决定正确。更丰富的转换链、时间与签署信息必须由外部证据模式提供；通用taint传播则属于独立的`TaintNoninterference.lean`，不能倒填进ULM06结构。

### 5.3 ULM07：有限Horn closure

**FORMALIZED.** 对有限事实载体\(F\)和有限Horn规则集\(R\)，立即后继算子只增加满足前件的后件。闭包通过从种子事实出发迭代至不动点取得 [@Horn1951; @Tarski1955]。

\[
T_R(X)=X\cup
\{\,b\mid(a_1\land\cdots\land a_n\to b)\in R,\;
\{a_1,\ldots,a_n\}\subseteq X\,\}.
\tag{12}
\]

\[
\operatorname{Cl}_R(F_0)=
\operatorname{lfp}_{X\supseteq F_0}T_R(X)
=
\bigcup_{k=0}^{|F|}T_R^k(F_0).
\tag{13}
\]

**DERIVED.** 有限性给出终止上界，单调性给出最小闭包，却不保证规则选择正确、法条解释适当或事实完整。带污染的前提即使在语法上满足Horn规则，其结论仍继承污染，不能因进入闭包而“洗净”。

## 6 ULM08–10

### 6.1 ULM08：canonical arguments

**FORMALIZED.** `CanonicalArgument`由请求、结论、基础前提有限集与支持超边有限集组成。有限集消除存储顺序与重复，但源码没有最小支持定理、独立分支字段或执行canonicalization的排序函数。`ArgumentWF`要求请求一致、节点可得、依赖不擦除、支持边非空且可达，并以`WellFounded (SupportDependsOn a)`约束具体推导。

\[
\operatorname{CanonicalArgument}(a)=
\langle a.request,a.conclusion,a.basePremises,a.supportEdges\rangle .
\tag{14}
\]

\[
\operatorname{ArgumentWF}(a)\Rightarrow
\operatorname{WellFounded}(\operatorname{SupportDependsOn}(a))
\land
\forall e\in a.supportEdges,\ e.premises\neq\varnothing.
\tag{15}
\]

**DERIVED.** 当前良构条件排除悬空和循环的具体支持图，但不保证支持集最小。若应用需要最小理由，必须另行定义删除任一基础前提后的不可推导性，并证明或验证该性质；现实裁判是否接受论证仍是独立问题。

### 6.2 ULM09：typed attacks与policy-resolved defeats

**FORMALIZED.** 攻击种类枚举包括`rebut`、`undermine`、`undercut`、`exceptionAttack`、`authorityAttack`、`scopeAttack`和`procedureAttack`。当前统一`AttackWF`只要求见证字符串非空且攻击者与目标请求相同；源码没有针对每种攻击分别定义实质法律条件。

\[
\operatorname{AttackWF}(a)\iff
a.witness\neq\epsilon\land a.attacker.request=a.target.request.
\tag{16}
\]

**FORMALIZED.** 击败由外部提供的`DefeatPolicy.succeeds : TypedAttackV1 → Bool`筛选已验证攻击。Lean只证明进入结果的击败存在一个良构来源攻击且政策返回true；并未证明该布尔政策实际比较了权威、时间、规则优先级或程序状态，这些含义必须由政策供应者另证 [@PrakkenSartor1997]。

\[
(A,B)\in\operatorname{resolveDefeat}(I,\pi)
\iff\exists a\in I.attacks:\
\pi.succeeds(a)=\mathsf{true}\land a.attacker=A\land a.target=B.
\tag{17}
\]

### 6.3 ULM10：Dung语义

**FORMALIZED.** ULM10的有限抽象论证框架直接绑定一个请求；其论证集合与policy-resolved defeats均受该请求约束 [@Dung1995]。

\[
AF=(r,\mathcal A,\mathcal D),\qquad
\forall A\in\mathcal A:\ A.request=r,
\quad
\forall(A,B)\in\mathcal D:\ A,B\in\mathcal A.
\tag{18}
\]

**FORMALIZED.** 令\(\Gamma_{AF}\)为接受所有被集合防御之论证的特征函数，则grounded extension为其最小不动点。

\[
\operatorname{Gr}(AF)=\operatorname{lfp}(\Gamma_{AF}),
\qquad
\Gamma_{AF}(S)=
\{A\in\mathcal A\mid\forall B(B\mathcal D A\Rightarrow
\exists C\in S,\;C\mathcal D B)\}.
\tag{19}
\]

**FORMALIZED.** 仓库把admissible定义为无冲突且防御集合内每一论证；complete extension则是admissible的特征函数不动点。

\[
\operatorname{Complete}(S)\iff
\operatorname{Admissible}_{AF}(S)\land
\Gamma_{AF}(S)=S.
\tag{20}
\]

\[
\operatorname{Preferred}_{AF}(S)\iff
\operatorname{Admissible}_{AF}(S)\land
\forall T\,
\bigl(\operatorname{Admissible}_{AF}(T)\land S\subseteq T
\Rightarrow T\subseteq S\bigr).
\tag{21}
\]

\[
\operatorname{Stable}(S)\iff
\operatorname{ConflictFree}(S)\land
\forall A\in\mathcal A,\ A\notin S\Rightarrow
\exists B\in S:\;B\mathcal D A.
\tag{22}
\]

**DERIVED.** grounded、complete、preferred和stable语义回答不同接受问题；stable extension可能不存在。因此，系统必须输出所用语义及extension集合，而不能只输出一个无来源的“胜诉概率”或单一布尔值。

## 7 ULM11–12

### 7.1 ULM11：branch-sensitive queries

**FORMALIZED.** ULM11的`ScenarioKey`只包含请求与假设有限集；`SemanticBranchKey`再包含语义profile与一个具体extension。事实快照、规则版本、攻击政策和程序阶段并非该结构字段。形式定理证明两个`SemanticBranchKey`不等的制品不能作为一个法律结果组合。

\[
b=\left(
\operatorname{ScenarioKey}(request,assumptions),
profile,extension
\right),
\qquad b_x\neq b_y\Rightarrow\neg\operatorname{Composable}(x,y).
\tag{23}
\]

**FORMALIZED.** 对语义\(\sigma\)产生的extension集合\(\operatorname{Ext}_{\sigma}(AF_b)\)，怀疑式查询要求结论在全部extension中成立，轻信式查询只要求至少一个extension支持。

\[
\begin{aligned}
\operatorname{Skept}_\sigma(q,b)
&\iff\forall E\in\operatorname{Ext}_\sigma(AF_b),\;
\exists A\in E:\operatorname{concl}(A)=q,\\
\operatorname{Cred}_\sigma(q,b)
&\iff\exists E\in\operatorname{Ext}_\sigma(AF_b),\;
\exists A\in E:\operatorname{concl}(A)=q.
\end{aligned}
\tag{24}
\]

**DERIVED.** 当extension集合为空或输入不足时，查询应返回`Undetermined`及原因。尤其对stable语义，不能把“不存在stable extension”解释为对所有命题的怀疑式支持。

### 7.2 ULM12：procedure及裁决权限

**FORMALIZED.** ULM12定义有限程序阶段及`applyProcedureCause`，该函数把阶段改为原因对应的目标阶段并保持`normativeMarker`。它不是带前置状态、角色、时间窗与回执守卫的完整状态机。裁决部分另有请求索引的`ValidatedAdjudicationAuthority`，检查争点、成功/失败结果的请求、非空reviewer及非程序性结果。

\[
\operatorname{applyProcedureCause}(c,s).stage=c.targetStage,
\qquad
\operatorname{applyProcedureCause}(c,s).normativeMarker=s.normativeMarker.
\tag{25}
\]

\[
\operatorname{ValidFor}(a,r)\Rightarrow
a.rule.issue=r.query\land a.reviewer\neq\epsilon\land
a.rule.successConsequence.request=r\land a.rule.failureConsequence.request=r.
\tag{26}
\]

**DERIVED.** 式（26）使算法语义与请求绑定的裁决输入保持分离。`adjudicate`在authority缺失时返回`pendingLegalJudgment`，但该authority对象不是外部身份认证或法律授权证明，也不使用`HumanResearchReceipt`。谁有现实权限、其判断是否有效，仍须由制度输入确定。

## 8 ULM13

**FORMALIZED.** ULM13以`Dimension`索引`ExactExpr`，量纲包括scalar、带货币字符串的money、带单位的duration及带basis字符串的rate。`lit/add/sub/scale`只在同一量纲索引内构造，值域是有理数。源码没有一般量纲指数乘法。

\[
\begin{aligned}
Dimension&=scalar\mid money(currency)\mid duration(unit)\mid rate(basis),\\
ExactExpr(d)&::=lit_d(q)\mid add(x,y)\mid sub(x,y)\mid scale(q,x).
\end{aligned}
\tag{27}
\]

**FORMALIZED.** 同一`Dimension`的表达式可作加减和有理数缩放，`eval_eq_denote`及`exact_execution_matches_denotation`证明递归执行等于独立递归指称。不同量纲的相加在类型上无法构造；源码并未实现汇率、最小货币单位或基准转换失败分支。

\[
\operatorname{eval}(add(x,y))=\operatorname{eval}(x)+\operatorname{eval}(y),
\qquad
\operatorname{executeExact}(e)=\mathsf{complete}(\operatorname{denote}(e)).
\tag{28}
\]

**CONJECTURE.** 下列分段利息、日历计日与舍入模型是法律计算应用的候选扩展，不在ULM13当前构造或定理中。它必须把期间、日历、利率、计息基数和舍入政策作为外部输入，核心不得自行选择适用率。

\[
I=\sum_{j=1}^{m}
P_j\cdot r_j\cdot
\frac{\operatorname{days}_{C_j}[a_j,b_j)}
{\operatorname{basis}_{C_j}}.
\tag{29}
\]

\[
\operatorname{Payable}=
\operatorname{Round}_{\kappa,s}(P+I-C),
\qquad
\kappa\notin\mathcal K\Rightarrow
\mathsf{Undetermined}(\mathsf{MissingRoundingPolicy}).
\tag{30}
\]

**DERIVED.** 式（29）和式（30）只是论文级候选公式，不是已经证明的计算关系。当前Lean只能表达同一量纲内的有理数表达式及其指称正确性。适用本金、起算日、利率上限、抵扣顺序和舍入规则必须由有效法律输入确定；软件不得以默认浮点或经验惯例填补这些法律空缺。

## 9 ULM14

**FORMALIZED.** ULM14不用加权比例表示coverage。`CoverageStatus`直接保存开放义务和不适用证据；`IsComplete`只在开放义务为空时成立。`SemanticCoverage`另以`actual = expected`记录对冻结extension集合的精确覆盖。

\[
\operatorname{CoverageStatus}=(openObligations,notApplicable),
\qquad
\operatorname{IsComplete}(c)\iff c.openObligations=\varnothing.
\tag{31}
\]

**FORMALIZED.** 五维`TrustVector`按`source/text/fact/proof/authority`逐坐标取最小值，形式定理只证明两输入meet不高于任一输入。对任意依赖图做全局fold是自然派生用法，但不是此模块单独陈述的定理。

\[
\operatorname{TrustLE}(a.meet(b),a)\land
\operatorname{TrustLE}(a.meet(b),b).
\tag{32}
\]

\[
\operatorname{combineCoverage}(a,b).openObligations
=a.openObligations\cup b.openObligations,
\tag{33}
\]

\[
\operatorname{combineAssurance}(a,b)=\mathsf{some}(c)
\Rightarrow a.scope=b.scope=c.scope,
\quad
a.spec=\mathsf{openObligations}\Rightarrow c.spec=\mathsf{openObligations}.
\tag{34}
\]

**DERIVED.** ULM14的核心是不升级并保留缺口：覆盖状态不替代信任，信任不替代verifier soundness，形式证明也不替代发布绑定。模块还分别合并spec、implementation、runCheck、legal input和引用集合；多个弱证据可以提高故障定位能力，却不能仅凭数量变成高等级证明。

## 10 ULM15

**FORMALIZED.** ULM15的add-only定理只覆盖有限Horn系统：`HornAddDelta`增加事实和规则并保持同一有限宇宙，旧立即后继与有界闭包包含于扩展系统对应结果。它没有定义对义务、映射、回执、证书、失败或来源账本的统一只增关系。

\[
sys.initialFacts\subseteq extendHorn(sys,\Delta).initialFacts,
\qquad
sys.rules\subseteq extendHorn(sys,\Delta).rules,
\qquad
Cl(sys)\subseteq Cl(extendHorn(sys,\Delta)).
\tag{35}
\]

**FORMALIZED.** `EmpiricalArtifact`只含`normativeSolutions`、一个有理数`score`和字符串`label`；`attachEmpirical`的定理仅证明附加分数后规范解集合不变。它没有概率、校准、相似度、类比强度或解释质量的专门字段，也没有覆盖“每个规范状态转移”的一般不干扰定理。

\[
\operatorname{attachEmpirical}(S,u).normativeSolutions=S,
\qquad
\operatorname{deviationScore}(w,f)=\sum_i w_i f_i.
\tag{36}
\]

**CONJECTURE.** 将概率、校准、相似度、类比强度或解释质量接入这个通用score槽位，需要分别定义其语义、数据与验证条件。只读附着定理不能证明这些分数有效，也不能推出任何法律结论。

**FORMALIZED.** 仅当度量空间完备且精化算子满足明确压缩常数时，才适用Banach不动点结论 [@Banach1922]。

\[
(X,d)\text{ complete}\land
\exists q\in[0,1)\;\forall x,y,\;
d(Tx,Ty)\le q\,d(x,y).
\tag{37}
\]

\[
\exists!x^\ast\in X:T(x^\ast)=x^\ast,
\qquad
d(T^n x,x^\ast)\le
\frac{q^n}{1-q}d(Tx,x).
\tag{38}
\]

**DERIVED.** 若未证明完备性、度量适当性和统一压缩常数，式（38）不得被引用。代码迭代“看似收敛”、测试误差下降或有限样本稳定，都不构成Banach前提的替代证据。

## 11 ULM16

**FORMALIZED.** ULM16不是完整流水线组合器，而是汇总四类具体实例：信任meet不升级、两段`Preserves`组合、满足明确精化关系的Horn增量实现等于子系统全量重算，以及`Outcome.map`不把failure转换为成功。源码明确否认这些实例已经关闭所有TheorySpec家族或Python实现精化。

\[
\begin{aligned}
COMP_{C01}&:\ TrustLE(a.meet(b),a)\land TrustLE(a.meet(b),b),\\
COMP_{C03}&:\ IncrementalCorrect(impl)\Rightarrow impl(\Delta)=childFullRecompute(\Delta),\\
COMP_{C04}&:\ map_f(failure(e))=failure(e).
\end{aligned}
\tag{39}
\]

**FORMALIZED.** `COMP_C02_observation_preservation`对任意类型和观察函数证明：若第一段与第二段分别保持同一个观察域，则函数组合也保持。定理没有预先选择请求、结果、来源、分支、金额、回执或发布绑定作为观察字段，更没有出现外部实现与规范的通用`Refines`关系。

\[
\operatorname{Preserves}(obs_A,obs_B,f)\land
\operatorname{Preserves}(obs_B,obs_C,g)
\Rightarrow
\operatorname{Preserves}(obs_A,obs_C,g\circ f).
\tag{40}
\]

**DERIVED.** 观测相等只相对于调用者实际提供的观察函数成立。若应用希望覆盖规则版本、舍入政策、污染标签或发布绑定，就必须逐项定义观察函数并提供两段保持前提；ULM16不会自动把这些字段纳入定理。发布前冻结观察面因此是工程要求，而非已完成的全字段证明。

## 12 时间、权限与人工回执

**FORMALIZED.** `ReceiptAuthority.lean`定义四级`AuthorityLevel`、五类`ArtifactKind`与最低等级表；`canIssue`只比较数值rank。`AuthorityReceipt`虽然记录subject、caseScope和issuer，但当前`receiptValid`只检查目标rank恰比来源rank高一，并不验证这些记录字段、地域或有效期间。

\[
\operatorname{canIssue}(l,k)\iff rank(l)\ge rank(requiredLevel(k)),
\qquad
\operatorname{receiptValid}(r)\iff rank(r.to)=rank(r.from)+1.
\tag{41}
\]

**FORMALIZED.** `HumanResearchReceipt`记录taskId、inputDigest、reviewer、action、issuedDay、expiryDay与revoked。`receiptBindsTask`只检查taskId和inputDigest；`receiptCurrentlyValid`只检查时间窗和撤销标志。它没有role、RequestKey、branch、decision或signed material字段，也不认证reviewer或证明行动发生。

\[
\begin{aligned}
\operatorname{receiptBindsTask}(\rho,t,d)&\iff \rho.taskId=t\land\rho.inputDigest=d,\\
\operatorname{receiptCurrentlyValid}(\rho,now)&\iff
\rho.issuedDay\le now\le\rho.expiryDay\land\neg\rho.revoked.
\end{aligned}
\tag{42}
\]

**FORMALIZED.** `TaintNoninterference.lean`把`stageOutput`定义为输入列表taint的fold，并证明首个tainted输入使该特定输出tainted，重复或多数输入不能洗白。它没有“授权签字”“格式转换”“高权限角色”或“新证据解除污染”的通用定理。

\[
x.taint=\mathsf{tainted}\Rightarrow
\operatorname{stageOutput}(x::xs,c).taint=\mathsf{tainted},
\qquad
\operatorname{taintOfInputs}(x::xs)=\operatorname{taintOfInputs}(x::x::xs).
\tag{43}
\]

**DERIVED.** 更完整的制度工作流还应分别验证外部身份、现实权限、事项范围、请求与分支、签署材料及解除污染依据；这些不是式（41）—（43）已经证明的内容。即使记录满足现有字段等式，也不代表行动真实发生、签署者具有现实权限或决定内容实体合法。

## 13 受subject约束的发布保证

**DERIVED.** 报告所述发布对象的subject SHA固定为`2a1d33df353a005dffc5d8b95faa591524e2636e`。发布结论只对这一提交成立。

\[
\operatorname{ReleaseSubject}(c)\iff
c=\texttt{2a1d33df353a005dffc5d8b95faa591524e2636e}.
\tag{44}
\]

**DERIVED.** 与该subject绑定的tree为`c7525f767b43c7e8a663a4a9702f64cdea78b979`。相同提交说明文字、不同tree或未提交工作区均不属于该证据边界。

\[
\operatorname{ReleaseTree}(t)\iff
t=\texttt{c7525f767b43c7e8a663a4a9702f64cdea78b979}.
\tag{45}
\]

**DERIVED.** GitHub Actions运行编号为`33946211096`；有效发布判断要求subject、tree与run三者同时绑定，而不是分别存在。

\[
\operatorname{BoundRun}(r,c,t)\iff
r=33946211096\land
\operatorname{ReleaseSubject}(c)\land
\operatorname{ReleaseTree}(t).
\tag{46}
\]

**DERIVED.** 证书生成时的阶段内容状态为`RELEASE_PASS_PENDING_INDEPENDENT_VERIFICATION`，独立报告状态为`VERIFIED_PENDING_RELEASE_GATE`，随后同一run的final gate成功。pending反映管线时序，而非最终仍未决；但不得回写证书JSON，把其阶段状态伪称为`RELEASE_PASS`。

\[
\begin{aligned}
&\mathsf{RELEASE\_PASS\_PENDING\_INDEPENDENT\_VERIFICATION}\\
&\quad\prec
\mathsf{VERIFIED\_PENDING\_RELEASE\_GATE}
\prec
\mathsf{FINAL\_GATE\_PASSED}.
\end{aligned}
\tag{47}
\]

## 14 真实变异证据与跨仓refinement receipts

**DERIVED.** 固定run中97个作业成功，其中91个属于模块矩阵；clean build日志另报告2993个completed jobs。前者是工作流作业计数，后者是构建系统内部完成项，二者分母和语义不同，不应相加为“3090项测试”。

\[
J_{\mathrm{success}}=97,\qquad
J_{\mathrm{matrix}}=91,\qquad
J_{\mathrm{cleanBuildCompleted}}=2993.
\tag{48}
\]

**DERIVED.** 全量ULM公理审计枚举145个声明，核心组合审计枚举27个声明；审计未发现项目自定义公理，依赖仅为`propext`、`Classical.choice`与`Quot.sound`，这些属于Lean及其经典推理边界 [@DeMouraUllrich2021; @Mathlib2020]。

\[
A_{\mathrm{ULM}}=145,\quad
A_{\mathrm{core}}=27,\quad
A_{\mathrm{custom}}=\varnothing,\quad
A_{\mathrm{kernel}}=
\{\mathsf{propext},\mathsf{Classical.choice},\mathsf{Quot.sound}\}.
\tag{49}
\]

**DERIVED.** 真实受控mutation为46/46 killed。其含义是测试与验证器拒绝了该有限变异集合中的每个变体，不是对所有可能缺陷或所有输入的普遍正确性证明。

\[
\operatorname{MutationScore}(M_{46})=
\frac{|\{m\in M_{46}\mid\operatorname{killed}(m)\}|}{|M_{46}|}
=\frac{46}{46}=1,
\qquad |M_{46}|=46.
\tag{50}
\]

**DERIVED.** juris-calculus真实运行生成三个跨仓refinement receipts并全部通过。其JC短前缀为`c79e03b`，build id为`github-actions:33946211096:1`；证据只覆盖三个命名夹具的追踪与结果一致。

\[
R_{\mathrm{named}}=\{\rho_1,\rho_2,\rho_3\},\qquad
\sum_{\rho\in R_{\mathrm{named}}}
\mathbf 1[\operatorname{pass}(\rho)]=3.
\tag{51}
\]

\[
\operatorname{CrossRepoBind}(\rho_i)\iff
\operatorname{jcPrefix}(\rho_i)=\texttt{c79e03b}
\land
\operatorname{buildId}(\rho_i)=
\texttt{github-actions:33946211096:1}
\land
\operatorname{traceEq}(\rho_i)
\land
\operatorname{resultEq}(\rho_i).
\tag{52}
\]

**DERIVED.** 三份回执不能推出\(\forall x\)的跨仓精化定理。它们排除了三个命名执行路径上的特定不一致，为适配器与发布绑定提供经验反证能力；未命名输入、未覆盖分支及未来版本仍须新证据。

## 15 完整案例

**CONJECTURE.** 设虚构请求\(r^\ast\)询问某地商铺租赁中，承租人是否应支付一笔逾期款及按外部政策计算的利息。本案例只展示架构如何追踪对象，不构成法律意见，也不预设任何现实法域的法条、利率或裁判结论。

**DERIVED.** 本案例把虚构案件范围、运行范围、场景、版本、语义profile、查询与映射版本装入ULM01现有字段；基准时点、请求类型和载荷摘要若需要，必须由外部应用另行编码并纳入其观察函数。ULM01本身不执行日期、货币或字段顺序规范化。

**DERIVED.** ULM06可把三项虚构事实分别登记为带`SourceLocator`与请求的证据令牌，并把未采信材料保留为assumed前提依赖。有效期、转换链与更丰富的来源审计须存于外部证据层；若应用另用`FormalInput`表示污染，则只能按`TaintNoninterference`的特定`stageOutput`规则传播，不能声称ULM06自动完成全链路污染追踪。

**DERIVED.** ULM07使用虚构规则：有效债务且到期且未清偿推出“存在待处理给付请求”；有效抵扣事实推出减少本金。闭包只在固定事实与规则载体上计算。应用层随后构造ULM08良基支持论证\(A_1\)，以\(\{f_1,f_2,f_3\}\)为基础前提并记录支持超边；当前源码不证明该集合最小。

**DERIVED.** 对方提出\(A_2\)，主张付款记录足以清偿；另有\(A_3\)攻击\(A_2\)的来源完整性。ULM09把\(A_2\)对\(A_1\)标为rebut，把\(A_3\)对\(A_2\)标为undermine，并由外部提供的证据政策决定何者构成defeat。ULM10分别计算grounded及preferred extensions，不把二者混成单一答案。

**DERIVED.** ULM11在分支\(b_1\)上执行怀疑式查询。若“存在待处理给付请求”只进入部分preferred extensions，则输出credulous而非skeptical；若stable extension不存在，则返回语义状态而非真值。新增核验过的付款凭证会形成\(b_2\)，不覆盖\(b_1\)的历史记录。

**DERIVED.** 应用层可把虚构程序的外部状态映射到ULM12有限阶段，并提供对该请求满足`AdjudicationAuthority.ValidFor`的对象。现有谓词只核对请求、争点、非空reviewer和非程序性结果，不验证现实中的时点、事项权限或身份；这些必须由外部制度层另行审查。

**DERIVED.** 应用层以虚构参数演示：本金100000.00元、抵扣20000.00元、计息本金80000.00元，分两期间按外部政策计算。ULM13可核验同一量纲内的有理数加减缩放，但当前没有分段计日、利率乘法或舍入实现；这些步骤及参数来源都只是论文级候选扩展。

**DERIVED.** ULM14可对输入信任向量取meet并保留开放义务。ULM15只证明新增Horn事实和规则时旧闭包包含于新闭包，不会把来源核验或回执写入通用只增账本。若应用希望比较请求、事实、论证、分支、金额与回执，必须分别定义观察函数并提供ULM16 `Preserves`前提；这些观察面并非现成的全链路定理。

**DERIVED.** 为压缩案例账本，以下九个谓词分别表示前文已说明的请求保持、来源闭合、Horn支持、论证规范化、分支绑定、程序授权、精确计算、人工回执绑定和发布绑定检查；每个谓词都显式作用于同一案例记录\(r^\ast\)，并不新增Lean定理。

\[
\begin{aligned}
\operatorname{CaseOK}(r^\ast)\iff{}&
\operatorname{RidPreserved}(r^\ast)\land
\operatorname{ProvClosed}(r^\ast)\land
\operatorname{HornSupported}(r^\ast)\land
\operatorname{ArgCanonical}(r^\ast)\\
&{}\land\operatorname{BranchBound}(r^\ast)\land
\operatorname{ProcedureAuthorized}(r^\ast)\land
\operatorname{ExactCalc}(r^\ast)\\
&{}\land\operatorname{HumanReceiptBound}(r^\ast)\land
\operatorname{ReleaseBound}(r^\ast).
\end{aligned}
\tag{53}
\]

**DERIVED.** 最后，案例执行证据必须绑定式（44）至式（47）的subject、tree和run。若案例只在本地未提交工作区成功，便不能借用该发布保证；若实际构建属于固定run，则可以报告“该命名案例在该发布边界内通过”，仍不得报告“软件证明了承租人的法律责任”。

## 16 反模型与明确非结果

**DERIVED.** 考虑反模型：模块\(f\)正确地产生分支\(b_1\)上的金额，适配器\(g\)却删除分支键并把结果附到\(b_2\)。两个局部测试都可能通过，但请求级观测已经改变，因此局部正确性不蕴含组合正确性。

**DERIVED.** 令\(\operatorname{PipelinePreserves}(f_1,\ldots,f_n)\)表示对每个可输入对象\(x\)，末端观察\(\operatorname{Obs}_n\)等于初始观察\(\operatorname{Obs}_0\)。该反模型断言存在一组阶段：它们逐个通过局部检查，但至少一个相邻接口不变量失败，因而全局观察保持不成立。

\[
\begin{aligned}
\operatorname{PipelinePreserves}(f_1,\ldots,f_n)
&\iff
\forall x,\ \operatorname{Obs}_n((f_n\circ\cdots\circ f_1)(x))
=\operatorname{Obs}_0(x),\\
&\exists f_1,\ldots,f_n:\
\left(\forall i,\operatorname{LocalPass}(f_i)\right)
\land\left(\exists j,\neg\operatorname{InterfaceInv}(f_j,f_{j+1})\right)
\land\neg\operatorname{PipelinePreserves}(f_1,\ldots,f_n).
\end{aligned}
\tag{54}
\]

**DERIVED.** 第二个反模型是污染洗白：来源不明的输入进入形式阶段，输出随后被人工记录采用。签署或采用不能反向证明原始材料真实。式（43）只保证特定`stageOutput`对tainted输入保持tainted；怎样以新证据解除或替换污染仍是尚未形式化的工作流规则。

**DERIVED.** 第三个反模型是证书状态改写：生成时状态为`RELEASE_PASS_PENDING_INDEPENDENT_VERIFICATION`，后来final gate通过。若事后把原JSON描述为`RELEASE_PASS`，最终发布结论或许仍为真，但历史证据已被错误陈述；正确做法是保留阶段pending，并另证同一run的后续门禁成功。

**CONJECTURE.** 本文没有证明概率Bayes模型正确校准、差分隐私、图相似度量、类比强度、解释质量、AI责任归属或任何实体法律结论。本文也没有证明三个夹具之外的全输入跨仓精化、46个变异之外的所有缺陷可检出，或托管平台和编译供应链绝对可信。

## 17 证据账本

**DERIVED.** 下表把主要论断、等级、证据和边界并列。等级针对本论文所报告的具体命题，而非对相关领域的一般评价。

| 论断 | 等级 | 证据 | 边界 |
|---|---|---|---|
| ULM01定义请求同一性与normal form | FORMALIZED | 式（2）—（3）对应的源码定义与性质 | 不证明文本相似即法律同一 |
| ULM02采用失败封闭outcome | FORMALIZED | 式（4） | 仅覆盖已枚举错误类型 |
| ULM03为类型化转换图 | FORMALIZED | 式（5）—（6） | 类型匹配不等于法律适当 |
| ULM04附着证明义务 | FORMALIZED | 式（7）—（8） | verifier拒绝不推出对象必错 |
| ULM05保持请求身份 | FORMALIZED | 式（9） | 不证明法律结论正确 |
| ULM06记录来源定位与假设依赖 | FORMALIZED | 式（10）—（11） | 通用taint在独立文件；来源记录不证明真实 |
| ULM07计算有限Horn闭包 | FORMALIZED | 式（12）—（13） | 不证明规则集完备 |
| ULM08定义良基支持论证 | FORMALIZED | 式（14）—（15） | 不证明支持最小或司法采纳 |
| ULM09区分attack与defeat | FORMALIZED | 式（16）—（17） | 胜负政策需外部输入 |
| ULM10实现四类Dung语义 | FORMALIZED | 式（18）—（22） | stable extension可能不存在 |
| ULM11支持分支敏感查询 | FORMALIZED | 式（23）—（24） | 结论仅属于固定分支 |
| ULM12保持程序marker并约束请求索引authority | FORMALIZED | 式（25）—（26） | 无角色时窗或现实授权认证 |
| ULM13进行同量纲有理数精确算术 | FORMALIZED | 式（27）—（28） | 式（29）—（30）金融应用未形式化 |
| ULM14保证不升级 | FORMALIZED | 式（31）—（34） | 不产生独立实体法律证据 |
| ULM15支持Horn add-only与只读分数 | FORMALIZED | 式（35）—（38） | 不含通用证据账本；Banach依赖压缩前提 |
| ULM16给出四个具体组合实例 | FORMALIZED | 式（39）—（40） | 不构成全流水线或预选观察面 |
| 回执记录字段及有限谓词 | FORMALIZED | 式（41）—（42） | 不认证身份、现实权限或行动发生 |
| 特定stageOutput保持taint | FORMALIZED | 式（43） | 无通用新证据解除定理 |
| subject与tree固定 | DERIVED | 给定SHA与tree证据 | 仅针对指定对象 |
| workflow run固定 | DERIVED | GitHub Actions run 33946211096 | 不覆盖其他run |
| 97个作业成功 | DERIVED | 工作流结果，其中91模块矩阵 | 不等于97项形式定理 |
| clean build完成2993项 | DERIVED | clean build日志 | 不与工作流作业数相加 |
| 145个ULM声明完成公理审计 | DERIVED | 全量公理审计枚举 | 声明数不等于法律命题数 |
| 核心组合审计覆盖27个声明 | DERIVED | 核心审计产物 | 不覆盖路径外声明 |
| 未见项目自定义公理 | DERIVED | 审计仅见三项基础依赖 | 依赖可信边界仍存在 |
| mutation为46/46 killed | DERIVED | 有限受控变异报告 | 分母固定为46 |
| 三份跨仓回执通过 | DERIVED | 三个命名夹具真实运行 | 不推出全输入精化 |
| final gate最终成功 | DERIVED | 同一run阶段链 | 不改写早期pending状态 |
| 法律输入应由适当制度来源提供 | DERIVED | 程序与回执接口边界 | 谁获授权及输入有效性不由Lean证明 |
| 案例展示端到端追踪 | DERIVED | 式（53）及案例记录 | 虚构示例，不是法律意见 |
| 概率与解释可设计为只读附着 | CONJECTURE | 式（36）的通用score仅作结构起点 | 专门语义与质量均未证明 |
| 实体法律正确性未被证明 | DERIVED | 保证链缺少实体法律真值前提 | 明确保留为外部责任边界 |

## 18 讨论

**DERIVED.** 组合保证的价值不是制造一个包罗万象的“正确”标签，而是允许使用者定位保证在哪一层中断。请求身份失败时无需讨论论证语义；来源污染未解除时无需把金额精确性当作实体可靠性；ULM12的请求绑定authority缺失时，`adjudicate`返回pending。应用是否另要求人工研究回执，属于发布政策而非该Lean函数的内建条件。

**DERIVED.** 发布边界使形式成果与软件供应对象发生可审计联系。subject标识讨论的提交，tree约束其文件内容，run约束执行实例，阶段状态记录时间顺序。只有四者共同存在，才能避免把别的提交、重跑结果或事后重写证书混入当前发布论断。

**CONJECTURE.** 实践中最有用的界面可能不是一个更复杂的法律知识图谱，而是一组短而强的类型：请求、来源事实、规则版本、论证、分支、程序动作、精确数量和回执。扁平而可绑定的数据更易进入审计、差异比较与失败恢复，也减少适配器静默丢字段的空间。

**DERIVED.** 该架构与经典程序验证的差别在于法律输入不能由程序规范完全封闭。Hoare式前后条件可以验证“若授权政策与事实输入满足，则计算保持不变量” [@Hoare1969]，却不能自行证明授权政策合法或事实应被采信。法律系统中的形式可信度因此必须与制度授权并列，而非替代制度授权。

**DERIVED.** 本文提出的发布政策把局部soundness、接口不变量、人工记录的外部核验和发布绑定组成合取；任何必要项缺失，政策只允许相应的未确定或拒绝状态。该合取是论文级release规则，不是ULM16中现成的统一定理。

**DERIVED.** 对任意对象\(x\)，令必要条件集合\(\mathcal N(x)\)由十六个\(\operatorname{ULMGuarantee}_i(x)\)以及\(\operatorname{CrossLayerInv}(x)\)、\(\operatorname{AuthorizedReceipt}(x)\)、\(\operatorname{BoundRun}(x)\)组成。于是论文级发布政策可闭合写为：

\[
\mathcal N(x)=
\{\operatorname{ULMGuarantee}_i(x)\mid1\le i\le16\}
\cup\{\operatorname{CrossLayerInv}(x),
\operatorname{AuthorizedReceipt}(x),
\operatorname{BoundRun}(x)\},
\qquad
\operatorname{ReleaseAssured}(x)\iff
\bigwedge_{P\in\mathcal N(x)}P,
\quad
\forall P\in\mathcal N(x),\quad
\neg P\Rightarrow\neg\operatorname{ReleaseAssured}(x).
\tag{55}
\]

### 18.1 组合不变量的审计顺序

**DERIVED.** 审计顺序应沿依赖方向展开，而不是先寻找一个总体分数。第一步核对请求与分支身份，第二步核对事实来源和规则版本，第三步核对闭包、论证、击败与查询之间的类型接口，第四步核对程序权限和精确算术参数，最后才核对运行回执与发布绑定。若第一步已经失败，后续结果至多说明另一个对象能够运行，不能补救当前对象的身份断裂。

**DERIVED.** 这种顺序还区分“内容失败”和“证据缺失”。内容失败表示已有证据反驳所需性质，例如命名回执出现结果不一致；证据缺失表示尚无合格对象证明或反驳性质，例如等待独立验证。二者都不得进入成功分支，但恢复动作不同：前者需要修复实现或规范桥，后者需要补齐真实生成且同subject绑定的证据。将两者压缩为一个红灯，会损失故障定位信息。

**DERIVED.** 组合的最低纪律是每个模块只报告其命名定理实际排除的升级：机器运行保持请求，Horn闭包相对于给定规则系统最小，程序层不把solver incomplete变成adjudicated，精确算术只执行已给表达式，同级共识不提升rank。把这些局部结果概括为“模块不得制造无权制造的对象”是论文级综合判断，不是一个全称Lean定理。

**DERIVED.** 否定式保证并不意味着系统只能拒绝。相反，当所有显式前提均有合格证据时，组合路径能够给出更窄但更可靠的肯定结论：某一请求在某一分支、某一规则版本、某一程序阶段及某一发布对象上产生了指定结果。此类结论比无版本、无分支的“系统正确”更易复核，也更容易在后续规则变化时准确失效。

### 18.2 制度接口与实践含义

**CONJECTURE.** 在法院、行政机关或企业合规场景中，最关键的部署设计不是让模型替代授权者，而是把哪些判断必须由谁作出转成显式接口。例如，事实采信、适用法选择、证据标准、利率政策和救济裁量可分别绑定角色与时点；软件则负责拒绝越权调用、保留异议分支并输出依赖清单。该方案能否降低复核成本仍需真实机构研究，本文没有经验数据支持效率结论。

**DERIVED.** 形式核心与制度接口之间需要双向可追踪：外部判断进入时必须携带权限、对象和有效期，机器结果返回时必须携带使用过的事实、规则、语义及未解决义务。只有输入责任与输出依赖同时可见，审计者才能区分“算法违反既定政策”与“既定政策本身存在法律争议”。形式证明只覆盖前者的已编码部分，后者必须保留给法律程序处理。

**CONJECTURE.** 该分工也为解释设计提供一个可检验方向。与生成流畅理由相比，展示实际支持图、攻击路径、分支差异、金额参数、人工动作记录与外部授权材料，可能更有助于专业复核；但“更有助于”属于用户研究命题，必须用任务正确率、漏错率、复核时间和异议识别率等指标验证，不能从形式结构直接推出 [@RibeiroEtAl2016; @GuidottiEtAl2018; @WachterEtAl2018]。

## 19 局限与有效性威胁

**CONJECTURE.** 构念有效性受“观测相等”定义影响。若观察函数遗漏具有法律意义的字段，ULM16仍可能在过窄观察面上成立。缓解方式是由形式作者、实现者与法律授权者共同冻结观察面，但这种共同选择本身不是机器可证明的中立事实。

**CONJECTURE.** 内部有效性受证据生成链影响。97个成功作业、2993个completed jobs、公理审计、变异报告和回执均可能遭受脚本错误、日志解析错误或环境偏差。subject、tree和run绑定缩小了误配空间，却没有证明托管平台、编译器或证据采集器不存在缺陷。

**CONJECTURE.** 外部有效性受有限分母约束。46个变异只代表选定故障族，三个夹具只代表命名路径，有限Horn载体只代表已编码规则。将这些结果推广到其他法域、其他事实规模、开放世界知识或对抗性输入，需要新的实验与证明。

**CONJECTURE.** 法律有效性仍依赖外部权威材料、版本选择、事实认定、解释方法和裁量。形式系统能够暴露这些输入，不能替代它们。尤其是责任归属、基本权利衡量和制度正当性，即使涉及人工智能监管文献，也不能从软件验证结果直接推出。

**CONJECTURE.** 本文没有提供用户研究，因而不能断言标签体系改善法官、律师或审计者的理解，也不能断言其解释质量优于其他界面。这些主张需通过预注册任务、错误发现率、复核一致性及时间成本等经验指标检验。

## 20 可复现性与失败恢复

**DERIVED.** 可复现对象应包括固定subject、tree、run、构建标识、证书原始状态、公理审计清单、变异集合和三份命名回执。复核者应保留原始阶段材料，分别验证内容绑定与状态顺序，而不是根据最终门禁结果重写中间产物。

**DERIVED.** 失败恢复遵循add-only原则。某个作业失败后，后续修复产生新run和新证据节点；旧失败仍留在账本。某份回执绑定错误时，应废止其发布资格并生成新回执，不修改旧回执中的请求、分支或构建字段。

**DERIVED.** 对Horn、论证或程序模块的失败，最小恢复单位是造成不变量破坏的边。修复后先重跑直接义务，再运行受影响的跨层观测检查。无关模块不因局部错误而被宣告错误，但也不能以无关模块成功抵销该错误。

**DERIVED.** 对发布管线，阶段pending是可恢复状态而非失败证据。`RELEASE_PASS_PENDING_INDEPENDENT_VERIFICATION`要求独立验证，`VERIFIED_PENDING_RELEASE_GATE`要求final gate；二者在同一run内依次满足后，才可报告整体发布门最终通过。若run改变，阶段证据必须重新绑定。

**CONJECTURE.** 长期复现还会受到依赖解析、操作系统镜像和托管服务变化影响。可采取固定工具链与保存日志的办法降低漂移，但除非相应对象进入哈希、签名或可验证构建边界，不应声称获得位级可复现性。

## 21 结论

**DERIVED.** 本文提出的ULM01—16架构把可执行法律推理分解为请求身份、失败封闭、类型化转换、证明义务、机器运行、来源、Horn闭包、论证、攻击与击败、Dung语义、分支查询、程序、精确算术、保证聚合、精化及跨模块观测保持。其共同原则是：任何保证都必须说明对象、前提、证据和边界。

**DERIVED.** 固定发布证据支持一个受限而具体的结论：指定subject与tree在GitHub Actions run 33946211096中最终通过发布门；97个作业成功，91模块矩阵完成，clean build报告2993个completed jobs；145个全量声明与27个核心声明完成公理审计；46/46个有限变异被杀死；三个命名夹具的跨仓回执通过。证书与独立报告的阶段pending状态均真实存在，并因同一run的后续final gate成功而闭合。

**DERIVED.** 该结论不包含实体法律正确性、全输入精化、概率校准、差分隐私、图相似性、类比强度、解释质量或AI责任归属。可组合保证的学术意义正在于拒绝这种无证升级：机器负责保持结构与证据，形式内核负责证明声明范围内的性质，发布系统负责绑定可执行对象，获授权的人类和制度负责法律判断。

## Declarations

### Funding

No external funding was received for this research.

### Conflict of Interest

The author declares no conflict of interest.

### Data Availability

The evidence discussed in this article consists of the identified source subject, tree, workflow run, audit outputs, mutation results, build logs, and three named refinement receipts. Availability is subject to the access controls and preservation policy of the corresponding repositories and workflow system.

### Ethics

This research did not involve human participants, personal data collection, clinical intervention, or animal experimentation. The worked case is fictional and does not constitute legal advice.

### Author Contributions (CRediT)

Laupinco: Conceptualization, Methodology, Formal Analysis, Investigation, Validation, Writing—Original Draft, Writing—Review and Editing, and Project Administration.

### AI Disclosure

Generative AI assistance was used in drafting and language refinement. The author determined the architecture, evidentiary boundaries, formal claims, legal-responsibility boundary, and final wording, and accepts responsibility for the manuscript. AI-generated text was not treated as evidence of formal proof or substantive legal correctness.

## References

**DERIVED.** 文内引文见 paper/references.bib
