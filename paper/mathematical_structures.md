# Mathematical Structures for Release-Bounded Legal Computation

**Author:** Laupinco

## Abstract

This paper presents the mathematical architecture implemented by the `legal-math-modeling` repository without treating formal syntax as a substitute for legal validity. The architecture combines a request-indexed normal form, finite typed incidence graphs, an explicit three-way result algebra, mandatory proof obligations, finite Horn closure, structural arguments, typed attack resolution, finite Dung semantics, branch-sensitive query evaluation, authority-bound adjudication, dimension-indexed exact arithmetic, a five-coordinate trust order, add-only refinement, and generic contraction results. The central contribution is not a theorem that “law is mathematics.” It is a collection of small invariants that prevent particular category errors: mixing cases, converting failure into success, erasing assumptions, confusing an incomplete search with a negative result, combining different semantic branches, adding unlike units, upgrading trust by aggregation, or allowing an empirical score to rewrite a normative solution. We classify every principal claim as `FORMALIZED`, `DERIVED`, or `CONJECTURE`. `FORMALIZED` means that a corresponding Lean declaration and theorem exists in the current source; it does not mean that the theorem’s premises are empirically or legally satisfied. `DERIVED` denotes a paper-level consequence or notation-preserving restatement. `CONJECTURE` denotes an extension not established by the repository. The resulting account makes the proof boundary visible and offers a reusable language for computational-law systems whose kernel must remain narrower than the legal judgment exercised around it.

## 中文摘要

本文重构 `legal-math-modeling` 仓库所实现的数学结构，并严格区分形式证明、工程验证与法律判断。模型由请求绑定的规范形、有限类型图、三分结果代数、强制证明义务、Horn 最小不动点、结构化论证、类型化攻击、Dung 语义、分支查询、权限绑定裁判、维度索引精确算术、五维信任向量、只增量精化与一般 Banach 收缩定理组成。本文的贡献不是宣称“法律已经被数学证明”，而是证明若干局部不变量：不同案件不得混合，失败不得映射成完成，假设依赖不得消失，求解未完成不得冒充否定结论，不同语义分支不得合并，不同量纲不得相加，聚合不得提升信任，经验分数不得改写规范解。每项主张均标注为 `FORMALIZED`、`DERIVED` 或 `CONJECTURE`。形式证明仅覆盖 Lean 中明确陈述的命题，并不自动证明法律输入、制度解释或运行时实现正确。

**Keywords:** computational law; formal methods; Lean; Horn closure; abstract argumentation; assurance; exact arithmetic; fixed points

## 1. Research questions and claim discipline

The paper addresses four questions. First, what is the smallest mathematical carrier that can preserve legal-computation identity across heterogeneous stages? Second, which local invariants can be proved without pretending that the formal system supplies legal premises? Third, how can finite rule closure, argumentation, procedure, calculation, and empirical observation coexist without silently converting one kind of evidence into another? Fourth, where does the present model stop?

The answer uses three labels. A claim marked `FORMALIZED` has a current Lean source anchor. A claim marked `DERIVED` follows at the paper level from formal definitions but is not necessarily a named Lean theorem. A claim marked `CONJECTURE` is proposed for future work. These labels classify proof status, not importance. An unformalized legal proposition may be institutionally decisive; a formally proved set identity may be legally trivial. This distinction follows the familiar idea that program logic proves properties relative to specifications [@Hoare1969] and that a proof assistant checks a term against a proposition rather than validating the world described by that proposition [@DeMouraUllrich2021; @Mathlib2020].

The repository’s normal form is deliberately finite. Finiteness permits explicit powerset semantics and cardinality-bounded iteration. It also prevents a common rhetorical jump from a bounded reference evaluator to an unrestricted production theorem. The present results concern the declared finite carriers and structured inputs. They do not establish jurisdiction-wide legal completeness, factual truth, institutional authority, or behavioral equivalence for every external runtime.

## 2. Related work

The architecture draws on four established traditions. Horn consequence operators provide a monotone rule core [@Horn1951]. Fixed-point semantics connect finite iteration to least models [@Tarski1955]. Abstract argumentation represents acceptance through attacks and defended sets rather than through monotone derivability alone [@Dung1995], while structured legal argumentation supplies attack types, priorities, and burdens [@PrakkenSartor1997; @BenchCapon2003; @ModgilPrakken2013]. Temporal structures and transition reasoning motivate explicit as-of boundaries [@Kripke1963; @Pnueli1977; @ClarkeEtAl1986].

The repository does not combine these traditions by declaring them equivalent. It connects them through typed intermediate objects and preservation obligations. That choice resembles an abstract-interpretation discipline in which an abstraction must state what observation it preserves [@CousotCousot1977]. Yet the current Lean package does not prove a general Galois connection between every layer. Any categorical or abstract-interpretation account beyond the named preservation predicates is therefore `CONJECTURE` unless separately proved.

## 3. Request-indexed normal form

The first invariant is identity. A context contains case scope, run scope, scenario, and versions. It is well formed exactly when the run belongs to the case:

$$
\operatorname{ContextWF}(k)
\;\Longleftrightarrow\;
k.\mathrm{runScope.caseScope}=k.\mathrm{caseScope}.
\tag{1}
$$

This is `FORMALIZED` in `ULM01NormalForm.lean` (`ContextKey.WellFormed`, `context_wf_iff`). A request adds a semantics profile, query identifier, and mapping version. A normal form then records the request, facts, rules, and active domains. The structure does not assert that the facts are true or that the rules are legally applicable. It ensures only that later components can be indexed by one explicit request.

An implementation transformation is described through observation preservation:

$$
\operatorname{Preserves}(o_A,o_B,f)
\;\Longleftrightarrow\;
\forall x,\;o_B(f(x))=o_A(x).
\tag{2}
$$

The composition theorem is:

$$
\operatorname{Preserves}(o_A,o_B,f)\land
\operatorname{Preserves}(o_B,o_C,g)
\Rightarrow
\operatorname{Preserves}(o_A,o_C,g\circ f).
\tag{3}
$$

Both are `FORMALIZED`. A broader claim that every compiler pass preserves all legally relevant meaning is `CONJECTURE`; it requires a chosen observation for each pass and a proof for the actual implementation.

## 4. Results, failures, and typed transitions

The result carrier prevents uncertainty from collapsing into completion:

$$
\operatorname{Outcome}(X)=
\operatorname{Complete}(X)
\;\uplus\;
\operatorname{Partial}(X,O),\;O\neq\varnothing
\;\uplus\;
\operatorname{Failure}(e).
\tag{4}
$$

This sum-type reading is `DERIVED` from the `FORMALIZED` inductive type in `ULM02Outcome.lean`. Its mapping operation preserves constructors, in particular

$$
\operatorname{map}(f,\operatorname{Failure}(e))
=\operatorname{Failure}(e).
\tag{5}
$$

The equation is `FORMALIZED` by `map_never_upgrades_failure`. The theorem is intentionally modest: it covers the specified `map`; it does not prove that every external orchestration layer preserves failures.

A typed graph contains finite nodes and edges. Edge well-formedness is the conjunction

$$
\begin{aligned}
\operatorname{EdgeWF}(G,e)\Longleftrightarrow{}&
\operatorname{WF}(G.r)\land e\in G.E\land e.r=G.r\\
&\land\;e.src\subseteq G.V\land e.tgt\subseteq G.V.
\end{aligned}
\tag{6}
$$

The local transition relation is

$$
s\to_G t\Longleftrightarrow
\exists e,\operatorname{EdgeWF}(G,e)\land e.r=s.r
\land e.src\subseteq s.active
\land t.active=s.active\cup e.tgt.
\tag{7}
$$

Equations (6)–(7) are `FORMALIZED` in `ULM03TypedGraph.lean`, as is request preservation (t.r=s.r). Node typing is not fully dependent: nodes carry a `NodeKind` tag and string identity. The source explicitly leaves full payload refinement open. Consequently, “ill-typed payloads are impossible” is `CONJECTURE`, whereas “declared incidence and request identity are checked by `EdgeWF`” is `FORMALIZED`.

## 5. Obligations and proof-carrying acceptance

Every edge receives a nonempty set of obligations. In mathematical notation,

$$
O_{req}(e)=\{\mathrm{typeSafety}\}\cup
\operatorname{toFinset}\!\left(
\operatorname{flatMap}(O,
baseline(e.kind)\mathbin{+\!+}e.claims)
\right).
\tag{8}
$$

The insertion of `typeSafety` proves \(O_{req}(e)\neq\varnothing\). Both the construction and nonemptiness theorem are `FORMALIZED` in `ULM04Obligations.lean`. Different executable kinds add obligations: a state transition adds update, identity, and branch claims; abstraction adds preservation; a probability kernel or ranker adds observation declaration; exact calculation adds dimensional correctness. The existence of a `probabilityKernel` tag is not a probability semantics. Any stochastic-kernel theorem is `CONJECTURE`.

Verification is separated from the proposition to be proved. For a goal predicate (g) and verifier (v),

$$
\operatorname{Sound}(g,v)\Longleftrightarrow
\forall ev,\;v.verify(ev)=\top\Rightarrow
ev.kind\in v.supported\land g(ev.subject).
\tag{9}
$$

Acceptance of an exact subject is

$$
\begin{aligned}
\operatorname{Sat}(v,s)\Longleftrightarrow{}&s.obligation\in O_{req}(s.edge)\land\\
&\exists ev,\;ev.subject=s\land ev.kind=s.obligation
\land v.verify(ev)=\top.
\end{aligned}
\tag{10}
$$

From (9) and (10), the repository proves (g(s)), required-obligation membership, and verifier-support membership. This is `FORMALIZED` by `sat_sound`. The premise `Sound(g,v)` remains essential. A verifier’s positive Boolean response alone never entails the goal.

## 6. Finite execution and Horn closure

The execution machine marks each applied edge. If (c) is a configuration, an edge is enabled when its sources are active, its request matches, and it has not been completed. Application performs

$$
\begin{aligned}
c'.active&=c.active\cup e.tgt,\\
c'.completed&=c.completed\cup\{e\},\\
c'.phase&=c.phase+1,\\
c'.request&=c.request.
\end{aligned}
\tag{11}
$$

The edge is then not re-enabled, and every finite `Run` preserves request identity. These statements are `FORMALIZED` in `ULM05Machine.lean`. The machine does not prove fairness of an external scheduler. Quiescence means that no well-formed graph edge is run-enabled; it is not a theorem that every legally relevant rule has been modeled.

Facts enter the rule layer through admitted attestations or explicit assumption witnesses. The dependency function is

$$
dep(p)=
\begin{cases}
\varnothing,&p.origin=admitted(a),\\
\{w.assumptionId\},&p.origin=assumed(w).
\end{cases}
\tag{12}
$$

This is `FORMALIZED` in `ULM06FactEvidence.lean`. It prevents an assumed premise from becoming dependency-free merely because it was encoded as a Horn atom.

For a Horn system (H=(U,F_0,R)), the immediate consequence operator is

$$
T_H(S)=F_0\cup
\{head(r)\mid r\in R,\;premises(r)\subseteq S\}.
\tag{13}
$$

The operator is monotone and remains inside (U). Iteration starts at the empty set:

$$
I_0=\varnothing,\qquad I_{n+1}=T_H(I_n).
\tag{14}
$$

The repository proves \(I_n\subseteq I_{n+1}\), stabilization no later than \(|U|\), and

$$
C_H=I_{|U|},\qquad T_H(C_H)=C_H,\qquad
T_H(S)=S\Rightarrow C_H\subseteq S.
\tag{15}
$$

Equations (13)–(15) are `FORMALIZED` across `HornDefinitions.lean`, `FiniteMonotoneIteration.lean`, `HornFixedPoint.lean`, and `ULM07HornSupport.lean`. The least-fixed-point result is exact for the finite declared system. Whether the declared rule set correctly captures law is an input question outside the theorem.

## 7. Structural argumentation

A canonical argument is not a hash or an unordered bag of premises. It is a request-bound labelled support hypergraph. Direct dependence is

$$
p\prec_a q\Longleftrightarrow
\exists e\in a.supportEdges,
p\in e.premises\land e.conclusion=q.
\tag{16}
$$

`ArgumentWF` requires a request-bound conclusion, a root available from a base premise or support edge, nonempty edge premises, no dangling nodes, explicit dependency inclusion, reachability to the root, and well-foundedness of (prec_a). These are `FORMALIZED` structural conditions in `ULM08ArgumentConstruction.lean`.

Coverage is deliberately relative:

$$
\operatorname{Coverage}(Expected,Actual)
\Longleftrightarrow Actual=Expected.
\tag{17}
$$

The Boolean equality checker is sound and complete for this equation. If every expected argument is independently well formed, equality transfers well-formedness to every actual argument. This is `FORMALIZED`. It is not a universal completeness theorem for a production generator, and the checker does not decide the `WellFounded` predicate.

Attacks are typed and witnessed:

$$
\operatorname{AttackWF}(a)
\Longleftrightarrow a.witness\neq\epsilon
\land a.attacker.request=a.target.request.
\tag{18}
$$

Given a Boolean policy $\pi$, the resolved defeat relation is

$$
D_\pi=
\{(a.attacker,a.target)\mid a\in Attacks,
\pi.succeeds(a)=\top\}.
\tag{19}
$$

The repository proves that every member of \(D_\pi\) has an actual well-formed source attack with the same request. This is `FORMALIZED` in `ULM09AttackDefeat.lean`. The policy itself is an input function. Its legal correctness is `CONJECTURE` unless supplied by a separately validated legal rule.

## 8. Dung semantics and branch identity

For the finite resolved framework (AF=(A,D)), attackers are

$$
Att(a)=\{b\in A\mid (b,a)\in D\}.
\tag{20}
$$

The characteristic function is

$$
F_{AF}(S)=\{a\in A\mid
\forall b\in Att(a),\exists c\in S:(c,b)\in D\}.
\tag{21}
$$

It is monotone, so the finite grounded extension is

$$
G=F_{AF}^{|A|}(\varnothing),\qquad
F_{AF}(G)=G,\qquad
F_{AF}(S)=S\Rightarrow G\subseteq S.
\tag{22}
$$

These are `FORMALIZED` in `ULM10DungProfiles.lean`, together with conflict-free, admissible, complete, preferred, stable, and grounded predicates. Preferred extensions are enumerated by filtering the powerset and the reference family is proved sound, complete, and nonempty. Stable extensions are kept separate because their family may be empty. This matches the conceptual distinction established in abstract argumentation [@Dung1995].

Query status is extension-relative. For an extension family $\mathcal E$,

$$
Common(q)\Longleftrightarrow
\forall E\in\mathcal E,\exists a\in E,conclusion(a)=q,
\tag{23}
$$

$$
Possible(q)\Longleftrightarrow
\exists E\in\mathcal E,\exists a\in E,conclusion(a)=q.
\tag{24}
$$

Both are `FORMALIZED` in `ULM11BranchQuery.lean`, along with refuted, undecided, inconsistent, and excluded statuses. Enterability and exclusion require positive witnesses; an incomplete gate cannot witness either. A branch includes scenario, assumptions, semantics profile, and extension. Two artifacts compose as one legal outcome exactly when their branch keys are equal. Branch non-mixing is therefore `FORMALIZED`, not a convention applied after evaluation.

## 9. Procedure, composition, and exact calculation

Procedure changes a stage without manufacturing a normative marker:

$$
applyCause(c,s)=s[stage\mapsto target(c)],\qquad
normativeMarker(applyCause(c,s))=normativeMarker(s).
\tag{25}
$$

This is `FORMALIZED` in `ULM12Procedure.lean`. Adjudication returns exactly one of adjudicated status, procedural disposition, pending legal judgment, or solver incomplete. An incomplete semantic evaluation always remains `solverIncomplete`; an extension’s existence does not by itself determine whether the legal burden is satisfied. Success or failure requires an authority object bound to the exact request. These constructor-separation results are `FORMALIZED`. The authority object does not certify the legal merit of its finding; it makes the source of that judgment explicit.

Domain composition enumerates nonempty subsets accepted by a policy:

$$
Choices(B,\pi)=
\{S\subseteq B.candidates\mid S\neq\varnothing
\land \pi.allows(S)=\top\}.
\tag{26}
$$

Each choice records its branch and policy identity. Sound membership and policy-binding properties are `FORMALIZED` in `ULM13DomainCompositionExact.lean`.

Exact arithmetic is indexed by dimension (d): scalar, currency, duration unit, or rate basis. Its evaluator obeys

$$
\begin{aligned}
eval(lit_d(q))&=q, & eval(x+_d y)&=eval(x)+eval(y),\\
eval(x-_d y)&=eval(x)-eval(y), & eval(q\cdot_d x)&=q\,eval(x).
\end{aligned}
\tag{27}
$$

The type prevents an addition between unlike dimensions. The evaluator is proved equal to an independently written recursive denotation. This is `FORMALIZED`. The source explicitly warns that interpreter correctness is not validation of a statutory calculation policy. Any claim that a damages or interest formula is legally correct is `CONJECTURE` until the formula and its authority are supplied.

## 10. Coverage and assurance

Coverage records open obligations and explicit exemptions. Completeness is

$$
Complete(C)\Longleftrightarrow C.openObligations=\varnothing,
\tag{28}
$$

and composition retains information:

$$
open(C_1\sqcup C_2)=open(C_1)\cup open(C_2),\qquad
NA(C_1\sqcup C_2)=NA(C_1)\cup NA(C_2).
\tag{29}
$$

These are `FORMALIZED` in `ULM14CoverageTrust.lean`. An exemption is not an erased obligation; it carries `NotApplicableEvidence`.

Trust is a five-coordinate vector over three ordinal levels:

$$
\tau=(\tau_{source},\tau_{text},\tau_{fact},
\tau_{proof},\tau_{authority})\in\{0,1,2\}^5.
\tag{30}
$$

Composition is the coordinatewise meet,

$$
(\tau\wedge\sigma)_i=\min(\tau_i,\sigma_i),\qquad
\tau\wedge\sigma\preceq\tau,\quad
\tau\wedge\sigma\preceq\sigma.
\tag{31}
$$

The non-upgrade inequalities are `FORMALIZED`. The coordinates are ordinal values, not probabilities, calibrated confidence intervals, or exchangeable scores. Mapping them to numerical risk is `CONJECTURE`.

An assurance envelope separately records specification status, implementation assurance, run-check status, coverage, legal-input status, scope, assumptions, trusted-computing-base references, and notices. Envelopes combine only when scopes match. Weak statuses dominate; all open-reference carriers combine by union. The repository proves scope preservation and retention of open obligations, pending legal inputs, spec references, exemptions, and notices. This is `FORMALIZED` fail-closed aggregation.

## 11. Incremental and empirical layers

An add-only Horn delta changes facts and rules while preserving the universe:

$$
F'_0=F_0\cup\Delta_F,\qquad
R'=R\cup\Delta_R,\qquad U'=U.
\tag{32}
$$

The repository proves

$$
T_H(S)\subseteq T_{H+\Delta}(S),\qquad
C_H\subseteq C_{H+\Delta}.
\tag{33}
$$

These properties are `FORMALIZED` in `ULM15IncrementalEmpiricalBanach.lean`. Correctness of an optimized implementation is specified as

$$
Correct(impl)\Longleftrightarrow
\forall\Delta,\ impl(\Delta)=FullRecompute(H+\Delta).
\tag{34}
$$

This is a `FORMALIZED` refinement relation, not evidence that an arbitrary production worklist satisfies it.

An empirical artifact contains normative solutions and a rational score. Attachment is read-only:

$$
Attach(S,s).normativeSolutions=S.
\tag{35}
$$

The declared deviation score is

$$
D(w,x)=\sum_{i=1}^{n}w_ix_i.
\tag{36}
$$

Both equations are `FORMALIZED`. No theorem says that (D) predicts court behavior, measures legal correctness, or should influence a normative outcome. Those interpretations are `CONJECTURE` and would require data, calibration, and an authority-approved decision rule.

## 12. Metric and contraction results

For positive weights (w_i>0), the weighted sup distance is

$$
d_w(x,y)=\max_i\frac{|x_i-y_i|}{w_i}.
\tag{37}
$$

The repository proves nonnegativity, symmetry, triangle inequality, and \(d_w(x,y)=0\Leftrightarrow x=y\). These are `FORMALIZED` in `WeightedSupNorm.lean`. A theorem named `weightedSupDist_complete` proves nonnegativity and point separation; despite its name, it does not establish a `CompleteSpace` instance. The paper therefore does not call that theorem a completeness proof.

For a coordinate map (T), the hypotheses

$$
|T(x)_i-T(y)_i|\le\sum_jL_{ij}|x_j-y_j|,\qquad
\sum_jL_{ij}w_j\le q w_i
\tag{38}
$$

imply

$$
d_w(Tx,Ty)\le q\,d_w(x,y).
\tag{39}
$$

This implication is `FORMALIZED` in `ContractionCondition.lean`. Separately, for any nonempty complete metric space and contracting (f), the generic Banach results prove existence, uniqueness, convergence, and the a-priori estimate

$$
d(f^n(x),x^*)\le
\frac{K^n}{1-K}d(x,f(x)).
\tag{40}
$$

These are `FORMALIZED` in `ULM15IncrementalEmpiricalBanach.lean`, building on Banach’s theorem [@Banach1922]. It is `CONJECTURE` that a particular legal evaluator is contracting until the evaluator, metric-space instance, and contraction premises are proved.

## 13. A worked structural composition

Consider a hypothetical request whose query concerns whether a claim is supported under a selected argumentation profile. The example is methodological, not a legal opinion. A source reviewer first supplies a set of admitted fact attestations and separately marks any provisional assumptions. The request key fixes the case, run, scenario, query, mapping version, and semantics profile. The normal form is accepted only when the run scope belongs to the case scope. At this point no legal conclusion has been computed. The structure merely prevents records from another request from entering without an explicit mismatch.

The admitted and assumed premises are converted into tagged atoms. `FORMALIZED`: admitted atoms have an empty assumption-dependency set, while assumed atoms retain the identifier of the assumption witness. If an implementation were to turn both origins into the same dependency-free string, it would no longer refine the formal tagging operation. The difference matters downstream: a conclusion supported by an assumption must remain distinguishable from one supported entirely by admitted inputs.

The Horn system then computes its finite support closure. Suppose \(F_0=\{p\}\), \(R=\{p\to q,q\to r\}\), and \(U=\{p,q,r\}\). The iterations are \(I_0=\varnothing\), \(I_1=\{p\}\), \(I_2=\{p,q\}\), and \(I_3=\{p,q,r\}\). `DERIVED`: this instance follows by evaluating the `FORMALIZED` operator, but the repository does not store this particular example as a named theorem. The fixed-point theorem ensures that one more step changes nothing. It does not say that \(p\), \(q\), or \(r\) is legally true. Their meaning still depends on the admitted facts, rules, versions, and authority outside the closure proof.

A position candidate can use only support contained in the closure and must share the request. A canonical argument then records the actual support hyperedges. For the chain above, the edge for (r) records (q) as a premise rather than merely placing (p,q,r) in a set. This distinction permits later explanation and attack targeting. `FORMALIZED`: a well-formed argument has a well-founded dependency relation, nonempty edge premises, available nodes, request-bound edges, and paths that reach the root. `CONJECTURE`: these conditions alone make the argument persuasive. They establish structural integrity, not weight or acceptability.

Suppose a second argument attacks the first by undercutting the rule \(q\to r\). The typed attack contains an explicit kind and a nonempty witness. The defeat policy decides whether this attack succeeds before the Dung layer receives the graph. `FORMALIZED`: if a pair appears in the resolved defeat relation, there is an actual well-formed attack in the validated input that produced it. `CONJECTURE`: the policy’s decision reflects the correct legal priority. That proposition needs a domain rule, source binding, and authorized interpretation.

The selected semantics now matters. Grounded evaluation returns the least fixed point of the characteristic function. Preferred evaluation returns all inclusion-maximal admissible sets. Stable evaluation may return no extension. The system does not merge these outputs. A branch key contains the scenario, assumptions, profile, and selected extension. `FORMALIZED`: different branch keys are not composable as one legal outcome. This blocks a particularly subtle error—taking one favorable proposition from one preferred extension and a second favorable proposition from an incompatible extension, then reporting their conjunction as if one coherent position supported both.

The query layer distinguishes universal and existential readings. `Common(q)` requires acceptance in every extension; `Possible(q)` requires acceptance in at least one. It also distinguishes explicit refutation from mere absence. An enterable query may be undecided when neither it nor its refuter occurs in an extension, or inconsistent when both occur. An excluded query is different again because exclusion needs a positive witness. `FORMALIZED`: an incomplete gate cannot be used as an enterability witness. Thus failure to finish a query check is not silently converted into “not accepted.”

Procedure adds another non-equivalence. Even when semantic extensions are complete, the repository requires a request-bound adjudication authority to turn a proof finding into an entity-level legal status. Procedure-only dispositions travel through a separate typed channel. `FORMALIZED`: an incomplete solver result remains `solverIncomplete`; no-extension without authority remains `pendingLegalJudgment`; and burden success or failure consequences are nonprocedural by construction. `DERIVED`: the architecture implements a separation between computational acceptance and institutional judgment. This is a structural observation, not a claim about which institution has lawful jurisdiction in a concrete dispute.

If several domain outcomes are available, composition enumerates only nonempty subsets selected from the actual bundle and allowed by the actual policy. The resulting child branch records the choice and policy identity. A calculation attached to that branch uses a dimension-indexed expression. RMB cannot be added to USD, nor days to months, because the addition constructor requires the same index on both operands. `FORMALIZED`: evaluation equals the recursive denotation. `CONJECTURE`: the chosen unit, rate basis, rounding method, or policy corresponds to governing law.

Finally, assurance envelopes combine only within one scope. If one component has open specification obligations or a failed run check, the combined envelope preserves the weaker status. Open obligations, pending legal references, assumptions, TCB references, exemptions, and notices are accumulated rather than averaged away. The five-coordinate trust vector likewise uses a meet. A strong proof score cannot compensate for an unreviewed legal source because coordinates remain separate. `DERIVED`: this gives the architecture a noncompensatory assurance interpretation. It does not produce a quantitative probability of correctness.

The worked trace illustrates why the model contains several apparently repetitive identity fields. A request identifier in an atom, argument, attack set, framework, branch, authority, and receipt is not redundant in the proof-theoretic sense. Each field is the point at which a transformation could otherwise detach an output from its subject. The local equality proofs compose into a chain of custody. `FORMALIZED`: selected links in that chain are proved. `CONJECTURE`: every external serialization, API call, database write, and user-interface presentation preserves the same identity. Runtime receipts and integration tests can provide engineering evidence for those links, but they are not interchangeable with Lean proofs.

## 14. Why the structures are deliberately non-unified

A tempting design would replace all statuses with one confidence number and all transformations with one generic arrow. The current formalization rejects that compression. Failure tags, open obligations, legal-input assumptions, implementation assurance, run-check status, trust coordinates, and empirical scores answer different questions. Treating them as one scalar would require conversion functions and validity theorems that do not exist.

The same caution applies to rule support and argument acceptance. Horn closure is monotone in its support set; Dung acceptance may change when defeats are added. The bridge from structured attacks to a binary defeat graph occurs only after a policy resolves the attacks. This is not accidental duplication. It preserves the difference between “derivable from rules,” “defended in a conflict graph,” and “adjudicated by an authority.” Each relation has a different carrier and different proof obligations.

Likewise, temporal validity is not encoded as an extra trust coordinate. A retracted source may have been accurately transcribed and strongly authenticated yet be inapplicable at the relevant as-of time. Dimensional correctness is not a legal-authority level. A perfectly dimensioned calculation may implement the wrong statute. Empirical fit is not normative soundness. These distinctions are `DERIVED` architectural consequences of the separate types. A theorem that they form one universal algebra remains `CONJECTURE`.

The value of non-unification is diagnostic precision. When a release is blocked, the open carrier identifies whether the deficit lies in a specification, implementation refinement, run check, semantic coverage, legal input, authority receipt, or other notice. That information supports repair. A single low score would show that something is wrong without preserving what must be supplied. A single high score could also hide a fatal deficit through compensation. The meet and union constructions avoid that failure mode at the cost of a less compact summary.

## 15. Evidence ledger

| Claim | Status | Lean anchor | What it does not establish |
|---|---|---|---|
| Request-preserving local transition | `FORMALIZED` | `ULM03TypedGraph.localTransition_preserves_request` | Legal adequacy of nodes or edges |
| Failure cannot become complete under `Outcome.map` | `FORMALIZED` | `ULM02Outcome.map_never_upgrades_failure` | Failure handling by every external service |
| Required obligations are nonempty | `FORMALIZED` | `ULM04Obligations.requiredObligations_nonempty` | Discharge of those obligations |
| Finite Horn least fixed point | `FORMALIZED` | `ULM07HornSupport.supportClosure_fixed`, `supportClosure_least` | Correctness of encoded law |
| Structural argument well-formedness | `FORMALIZED` | `ULM08ArgumentConstruction.ArgumentWF` | Completeness of a production generator |
| Dung grounded and preferred reference semantics | `FORMALIZED` | `ULM10DungProfiles` | Legal correctness of attack policy |
| Branch non-mixing | `FORMALIZED` | `ULM11BranchQuery.different_branches_not_composable` | Which branch a court should choose |
| Incomplete solving is not adjudication | `FORMALIZED` | `ULM12Procedure.adjudicate_incomplete` | Substantive legal judgment |
| Dimension-safe interpreter | `FORMALIZED` | `ULM13DomainCompositionExact.exact_execution_matches_denotation` | Statutory formula validity |
| Trust meet cannot upgrade | `FORMALIZED` | `ULM14CoverageTrust.trust_meet_le_left/right` | Probabilistic calibration |
| Empirical attachment is read-only | `FORMALIZED` | `ULM15IncrementalEmpiricalBanach.empirical_is_read_only` | Predictive validity |
| Full legal-system correctness | `CONJECTURE` | none | Requires legal inputs, implementation refinement, and runtime evidence |

This ledger is part of the contribution. It prevents a theorem about a carrier from being narrated as a theorem about institutions.

## 16. Validation boundary and limitations

The formal package establishes internal propositions for its declared types. It does not establish that source documents were correctly digitized, that fact attestations are truthful, that a burden rule represents current law, that an attack witness is persuasive, or that an authority acted lawfully. Those are external premises. The model’s achievement is to prevent such premises from disappearing once introduced.

The finite evaluators are reference specifications. Powerset enumeration can be expensive, and the current proofs do not establish complexity bounds for production workloads. The graph’s node kinds are tagged rather than dependently payload-typed. The defeat policy is uninterpreted beyond a Boolean decision. The exact arithmetic language is rational and dimension-indexed but does not encode calendars, rounding law, currency conversion, or statutory interest schedules in this module. The trust vector is deliberately noncompensatory and coarse. The generic Banach theorem is not a convergence proof for the legal evaluator. Probability, differential privacy, graph similarity, analogy, explanation quality, and substantive AI liability require separate models.

These limitations do not weaken the stated theorems. They determine what propositions the theorems are about. The architecture is best understood as a set of proof-preserving boundaries around legal computation, not as an automated source of legal authority.

## 17. Reproducibility protocol

A reader can reproduce the paper’s formal inventory without accepting its legal interpretation. First, identify the exact repository subject and read the named Lean definitions rather than relying on section titles. Second, check whether a displayed equation is a literal definition, a named theorem, a paper derivation, or a conjecture. Third, inspect the theorem’s premises. A request-preservation theorem applies only after a `LocalTransition` or `Run` witness exists; a verifier theorem applies only after verifier soundness and exact subject binding; a Banach theorem applies only after contraction and complete-space hypotheses.

Fourth, keep proof evidence separate from execution evidence. A successful build shows that the current sources elaborate in the recorded toolchain. It does not prove that an external runtime implements the same functions. Runtime fixtures and receipts can test that connection, but their subject identity, commit, input, configuration, and outcome must match. Fifth, keep both forms of evidence separate from legal authority. A source reviewer or adjudication authority supplies premises that the kernel does not discover.

Sixth, reproduce negative boundaries as well as positive theorems. Confirm that partial outcomes require open obligations, different branch keys do not compose, incomplete evaluation remains incomplete at adjudication, trust meets do not upgrade either input, and empirical attachment leaves normative solutions unchanged. These checks establish the absence of several laundering paths.

Finally, do not infer coverage from counts alone. A theorem count records declarations; a module matrix records compilation targets; a mutation score records detection of selected code changes. None independently establishes legal-domain completeness. Reproducibility therefore means rebuilding the exact formal claim and its evidence ledger, not converting a successful pipeline into a universal correctness statement.

## 18. Conclusion

The mathematical architecture supports a narrow but useful thesis: heterogeneous legal-computation stages can be connected without erasing identity, failure, assumptions, branches, dimensions, or assurance deficits. The thesis is backed by `FORMALIZED` equations for finite closure, argumentation semantics, branch-sensitive procedure, exact arithmetic, non-upgrading trust, and read-only empirical attachment. The broader thesis that this architecture yields legally correct decisions remains `CONJECTURE`. That separation is the condition under which formal methods can contribute to legal systems honestly.

## Declarations

**Funding.** No external funding was received.

**Conflict of Interest.** The author declares no competing interests.

**Data Availability.** The formal sources, specifications, and public evidence discussed here are contained in the `legal-math-modeling` repository [@LegalMathModeling2026]. No private client data are used.

**Ethics.** This study uses no human participants and no private case files. It does not supply legal advice or replace authorized legal judgment.

**CRediT Author Statement.** Laupinco: Conceptualization, Methodology, Software, Formal Analysis, Investigation, Writing—Original Draft, Writing—Review and Editing.

**AI Disclosure.** AI-assisted drafting was used to reorganize prose and check consistency. The author remains responsible for all claims, source selection, formulas, and final text. AI output is not treated as formal or legal authority.

## References

References are maintained in `paper/references.bib`; citations use repository BibTeX keys [@LegalMathModeling2026; @Dung1995; @PrakkenSartor1997; @Horn1951; @Tarski1955; @CousotCousot1977; @Banach1922; @DeMouraUllrich2021; @Mathlib2020; @Hoare1969].
