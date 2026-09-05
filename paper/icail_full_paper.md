# Request-Bound, Fail-Closed, and Branch-Safe Legal Reasoning: A Machine-Checked Architecture from Horn Closure to Adjudication

**Author:** Laupinco

**Article type:** Full research paper for Artificial Intelligence and Law / ICAIL
**Evidence baseline:** `legal-math-modeling`, ULM01–ULM16, release subject `2a1d33df353a005dffc5d8b95faa591524e2636e`

## Abstract

Formal legal-reasoning systems often combine rules, evidence, arguments, temporal conditions, numerical calculations, and human authorization. Each component may be locally plausible while their composition silently changes case identity, merges incompatible branches, upgrades incomplete computations, or treats repeated machine agreement as legal authority. This paper presents a bounded architecture for preventing those failures. Its technical basis is a Lean 4 development organized as sixteen Unified Legal Model modules (ULM01–ULM16). The development gives machine-checked definitions and theorems for request identity, a fail-closed outcome algebra, typed graph transitions, mandatory proof obligations, sound verifier contracts, finite execution, Horn least closure, structured arguments, attacks and defeats, Dung-style semantics, branch-sensitive queries, procedure-aware adjudication, dimension-indexed exact calculation, coverage and trust composition, add-only incrementality, temporal applicability, receipt authority, and taint non-interference. We distinguish three epistemic levels: **FORMALIZED** statements are backed by named Lean declarations; **DERIVED** statements follow mathematically from an explicitly stated model but are not themselves claimed as repository theorems; **CONJECTURE** statements are proposed design hypotheses requiring additional formalization or empirical study. The central contribution is not a theorem that a legal answer is substantively correct, nor one global theorem covering every released result. It is a family of local invariants that constrain composition; the release policy separately requires subject-bound evidence for request, branch, obligations, runtime checks, temporal scope, recorded authority fields, and trust degradation. We report the verification discipline, explain the limits of the certificate, and show why probability, analogy, differential privacy, graph similarity, explanation quality, and liability allocation remain outside the proved core.

## 中文摘要

形式化法律推理系统通常同时处理规则、证据、论证、时间条件、数值计算与人工授权。即使每个组件局部上看似合理，组合后仍可能悄然改变案件身份、混合互不相容的分支、把未完成计算升级为结论，或把多个机器代理的一致意见误当成法律权威。本文提出一套有边界的防错架构，其技术基础是由十六个统一法律模型模块（ULM01–ULM16）构成的 Lean 4 证明开发。该开发对请求身份、失败闭合结果代数、类型化图转移、强制证明义务、可靠验证器契约、有限执行、Horn 最小闭包、结构化论证、攻击与击败、Dung 语义、分支查询、程序性裁判、维度索引精确计算、覆盖与信任组合、只增量更新、时间适用性、收据权限及污点不干扰给出机器核验定义与定理。本文严格区分三类知识状态：**FORMALIZED** 表示存在对应 Lean 声明；**DERIVED** 表示在明示模型内可数学推出、但不冒充仓库定理；**CONJECTURE** 表示仍需形式化或经验检验的设计假说。核心贡献不是证明某项法律结论在实体法上正确，也不是一个覆盖所有发布结果的统一定理，而是一组约束组合的局部不变量；发布政策另行要求请求、分支、义务、运行检查、时间范围、权限记录字段及信任降级均绑定同一对象的证据。本文同时说明证书能力边界，并明确概率推理、法律类比、差分隐私、图相似性、解释质量与责任分配尚不属于已证明核心。

**Keywords:** computational law; formal methods; Lean 4; argumentation; non-monotonic reasoning; proof-carrying legal computation; assurance cases

## 1. Problem and contribution

The familiar question “can legal reasoning be formalized?” is too coarse to guide engineering. A production decision path contains several logically distinct questions. Is the request still the same request after translation? Were all applicable rules considered? Does a verifier’s success mean that its advertised property holds? Were mutually exclusive argumentation extensions combined? Does a numerical evaluator preserve units? Was the evidence valid at the decision’s as-of time? Who had authority to approve the step? A single global label such as “verified” conceals these distinctions.

Classical work gives powerful local models. Horn clauses support constructive closure [@Horn1951]. Fixed-point theory explains least solutions of monotone operators [@Tarski1955]. Abstract argumentation separates arguments from attacks and defines extension semantics [@Dung1995], while structured approaches add preferences and defeasibility [@PrakkenSartor1997; @ModgilPrakken2013]. Program logics show how local specifications can constrain computation [@Hoare1969]. Yet a legal pipeline needs an explicit theorem-bearing interface between these families. Its most dangerous errors are often not incorrect local steps but invalid composition.

This paper answers the following research question:

> Which invariants are sufficient to make a heterogeneous legal-reasoning pipeline request-bound, fail-closed, branch-safe, and evidence-calibrated, without claiming that formal validity itself determines substantive law?

The answer is a layered architecture implemented in Lean 4 [@DeMouraUllrich2021; @Mathlib2020] and distributed as an inspectable proof corpus [@LegalMathModeling2026]. Its contribution has four parts. First, it provides a common identity and outcome layer. Second, it connects monotone Horn support to non-monotone argument evaluation without conflating their semantics. Third, it formalizes composition rules that preserve open obligations, the weakest trust status, branch identity, and human authority. Fourth, it makes negative claims operational: incomplete evidence remains incomplete, tainted input remains tainted, and same-level consensus cannot create higher authority.

## 2. Epistemic discipline

The paper uses three labels. **FORMALIZED** means that the proposition is represented by a definition or theorem in the current Lean source. It does not mean that every external runtime implements that source, that all inputs are factually correct, or that a court would accept the encoded norm. **DERIVED** means that a conclusion follows by ordinary mathematics from assumptions written in this paper, but the paper does not attribute a corresponding theorem to the repository. **CONJECTURE** marks a proposed empirical, legal, or mathematical extension.

Let the status function be

$$
\lambda(c)\in\{\mathsf{FORMALIZED},\mathsf{DERIVED},\mathsf{CONJECTURE}\}.
\tag{1}
$$

The labels are intentionally not ordered as degrees of truth. A `FORMALIZED` proposition may be conditional on an abstract policy. A `DERIVED` proposition may be mathematically uncontroversial but absent from the proof corpus. A `CONJECTURE` may later become a legal design choice rather than a theorem. What matters is that readers can tell which burden of justification applies.

We also separate four validation layers:

$$
\mathcal V=\mathcal V_{\mathrm{kernel}}\times
\mathcal V_{\mathrm{build}}\times
\mathcal V_{\mathrm{runtime}}\times
\mathcal V_{\mathrm{legal}}.
\tag{2}
$$

Lean kernel acceptance addresses the first coordinate. Continuous integration addresses reproducible elaboration and specified checks. Cross-repository receipts can witness runtime refinement for selected fixtures. Legal correctness remains a human and institutional judgment. No projection from the first three coordinates automatically fixes the fourth.

## 3. Request identity and observation preservation

Every computation is indexed by a request key (k), including a case scope and run scope. The well-formedness predicate is:

$$
\operatorname{WF}(k)\iff
k.\operatorname{runScope.caseScope}=k.\operatorname{caseScope}.
\tag{3}
$$

**FORMALIZED.** ULM01 defines this equality and proves equivalent normal-form conditions. The equation is deliberately modest. It does not prove that a case identifier refers to the correct real-world dispute; it prevents the system from silently changing the identifier already supplied.

Translation between representations is governed by observation preservation. Given observations \(o_A:A\to O\), \(o_B:B\to O\), and transformation \(f:A\to B\), define:

$$
\operatorname{Preserves}(o_A,o_B,f)iff
\forall x\in A,\quad o_B(f(x))=o_A(x).
\tag{4}
$$

**FORMALIZED.** Preservation composes:

$$
\operatorname{Preserves}(o_A,o_B,f)\land
\operatorname{Preserves}(o_B,o_C,g)
\Rightarrow
\operatorname{Preserves}(o_A,o_C,g\circ f).
\tag{5}
$$

This theorem supplies a reusable interface for serialization, compiler passes, or report rendering. It still requires the observation function to be chosen correctly. If (o) ignores legally material fields, preservation of (o) cannot restore them. That choice belongs to specification review.

## 4. A fail-closed outcome algebra

A binary success/failure type is inadequate when a result is usable but has unresolved obligations. ULM02 therefore distinguishes complete, partial, and failed outcomes:

$$
\operatorname{Outcome}(\alpha)=
\operatorname{Complete}(x:\alpha)
+\operatorname{Partial}(x:\alpha,O:O\neq\varnothing)
+\operatorname{Failure}(e).
\tag{6}
$$

**FORMALIZED.** The non-emptiness witness prevents `Partial` from becoming a second spelling of `Complete`. Mapping a pure function over the payload cannot upgrade failure:

$$
\operatorname{map}(f,\operatorname{Failure}(e))
=\operatorname{Failure}(e).
\tag{7}
$$

This algebra implements a local form of fail-closedness. It does not prohibit an authorized human from resolving an obligation; it prohibits a generic payload transformation from pretending that resolution already happened. A release gate can then distinguish “a value exists” from “the value is certified for this use.”

## 5. Typed transitions, obligations, and verifiers

Let a typed graph (G) contain nodes (V_G), edges (E_G), and request (r_G). For an edge (e), well-formedness requires graph and edge request identity plus endpoint inclusion:

$$
\operatorname{EdgeWF}(G,e)\iff
\operatorname{WF}(G.r)\land e\in E_G\land e.r=G.r
\land \operatorname{src}(e)\subseteq V_G
\land \operatorname{tgt}(e)\subseteq V_G.
\tag{8}
$$

An edge is enabled in state (s) only when request identifiers agree and all source nodes are active:

$$
\operatorname{Enabled}(e,s)\iff
e.r=s.r\land\operatorname{src}(e)\subseteq s.active.
\tag{9}
$$

Applying it grows the active set:

$$
s'.active=s.active\cup\operatorname{tgt}(e),
\qquad s'.r=s.r.
\tag{10}
$$

**FORMALIZED.** ULM03 proves request preservation for local transitions. The node representation exposes a kind tag; it does not yet establish a fully dependent payload refinement for every node family. That omission is a formal boundary, not a harmless implementation detail.

Every edge creates a nonempty obligation set. With `typeSafety` as a mandatory member and edge-kind baselines joined with claims,

$$
O_{\mathrm{req}}(e)=\{\mathsf{typeSafety}\}\cup
\operatorname{flatMap}\bigl(O,
\operatorname{baseline}(e.kind)\mathbin{++}e.claims\bigr),
\quad O_{\mathrm{req}}(e)\neq\varnothing.
\tag{11}
$$

**FORMALIZED.** Verification is not merely a Boolean call. A verifier (v) advertises supported evidence kinds, and its soundness is parameterized by a semantic guard (g):

$$
\operatorname{VerifierSound}(g,v)\iff
\forall ev,\ v(ev)=\top\Rightarrow
ev.kind\in v.supported\land g(ev.subject).
\tag{12}
$$

A satisfaction witness binds the obligation, edge, evidence kind, and successful verifier result:

$$
\operatorname{Sat}(v,s)\iff
s.o\in O_{\mathrm{req}}(s.edge)\land
\exists ev,\ ev.subject=s\land ev.kind=s.o\land v(ev)=\top.
\tag{13}
$$

**FORMALIZED.** `VerifierSound` and `Sat` entail (g(s)). The theorem establishes a contract: it does not prove that an arbitrary executable verifier is sound. That separate refinement burden is exactly why runtime receipts and mutation fixtures matter.

## 6. Finite execution and support closure

ULM05 adds a finite-state machine. An edge can run only when it has not already completed:

$$
\operatorname{runEnabled}(e,c)\iff
e.r=c.r\land\operatorname{src}(e)\subseteq c.active
\land e\notin c.completed.
\tag{14}
$$

The update unions targets into the active set, inserts the edge into `completed`, and increments the phase. **FORMALIZED.** The applied edge is no longer enabled, and any finite run preserves the request. Termination of all imaginable orchestration policies is not claimed; the theorem concerns the stated finite transition relation.

Support generation uses a Horn system (H=(F_0,R,U)). Its immediate-consequence operator is

$$
T_H(S)=F_0\cup
\{\operatorname{head}(r)\mid r\in R,
\operatorname{prem}(r)\subseteq S\}.
\tag{15}
$$

The finite iteration is

$$
I_0=\varnothing,
\qquad I_{n+1}=T_H(I_n),
\qquad I_n\subseteq I_{n+1}.
\tag{16}
$$

Because all facts live in finite universe (U), the chain stabilizes by (|U|). Define

$$
C_H=I_{|U|}.
\tag{17}
$$

**FORMALIZED.** ULM07 proves \(T_H(C_H)=C_H\) and \(C_H\subseteq S\) for every fixed point \(S\). This is the least closure used to constrain candidate support:

$$
\operatorname{CandidateWF}(H,c)iff
c.r=H.r\land c.support\subseteq C_H.
\tag{18}
$$

The fixed-point layer follows the constructive tradition of Horn reasoning and monotone semantics [@Horn1951; @Tarski1955; @CousotCousot1977]. It is intentionally monotone. Defeat and competing extensions enter only after support has been constructed, so that absence of an accepted argument is not confused with absence of derivable support.

## 7. Structured arguments and argumentation semantics

A structured argument (a) carries a finite dependency relation. Direct support is

$$
p\prec_a q\iff
\exists e\in E_a,\quad p\in\operatorname{prem}(e)
\land\operatorname{concl}(e)=q.
\tag{19}
$$

**FORMALIZED.** ULM08 requires this relation to be well-founded, prevents dangling nodes, binds the request, and retains premise dependencies. Its coverage predicate is exact equality between an expected carrier and an actual carrier:

$$
\operatorname{ArgumentCoverage}(E,A)iff A=E.
\tag{20}
$$

This is a closed-world completeness check against a frozen expected set. It is not a universal proof that a production generator discovered every legally relevant argument.

Attacks are typed witnesses. A minimal well-formedness predicate is

$$
\operatorname{AttackWF}(x)\iff
x.witness\neq\epsilon\land
x.attacker.r=x.target.r.
\tag{21}
$$

A defeat policy $\pi$ selects successful attacks:

$$
D_{\pi}=\{(x.attacker,x.target)\mid
x\in Attacks,\ \pi.succeeds(x)=\top\}.
\tag{22}
$$

**FORMALIZED.** Every resolved defeat has a well-formed, same-request source attack. But `succeeds` is an abstract Boolean function. Its legal priority rule is not proved merely because source binding is.

Given argumentation framework (AF=(A,D)), Dung’s characteristic function [@Dung1995] is represented as

$$
F_{AF}(S)=\{a\in A\mid
\forall b\in Att(a),\exists c\in S:(c,b)\in D\}.
\tag{23}
$$

ULM10 formalizes conflict-free, admissible, complete, preferred, stable, and grounded semantics. In particular,

$$
G=F_{AF}^{|A|}(\varnothing),
\qquad F_{AF}(G)=G,
\qquad G\subseteq S\text{ for every fixed point }S.
\tag{24}
$$

The implementation also proves sound and complete finite enumeration for preferred extensions. **FORMALIZED.** These results establish abstract argumentation semantics, not a judicial rule that one semantics must be chosen in a jurisdiction.

## 8. Branch-sensitive queries

For profile (p), the extension family is selected explicitly:

$$
Ext_p(AF)=
\begin{cases}
\{G\}, & p=\mathsf{grounded},\\
PreferredExt(AF), & p=\mathsf{preferred},\\
StableExt(AF), & p=\mathsf{stable},\\
CompleteExt(AF), & p=\mathsf{complete}.
\end{cases}
\tag{25}
$$

Skeptical and credulous queries become distinct quantifier patterns:

$$
\operatorname{Common}(q)\iff
\forall e\in Ext_p(AF),\ \operatorname{AcceptedIn}(e,q),
\tag{26}
$$

$$
\operatorname{Possible}(q)\iff
\exists e\in Ext_p(AF),\ \operatorname{AcceptedIn}(e,q).
\tag{27}
$$

**FORMALIZED.** The branch identifier is carried into query results, and composition is permitted only within one branch:

$$
\operatorname{Composable}(x,y)\iff x.branch=y.branch.
\tag{28}
$$

This small equation closes a major loophole. If one extension supports liability and another supports a defense, a report may present both as possible, but it may not combine the favorable fragments into a nonexistent super-extension. Branch-safety therefore protects the semantics of disagreement without pretending to eliminate it.

## 9. Procedure, authority, and adjudication

Procedure is modeled separately from the normative marker. Applying a procedural cause changes the stage but preserves the marker. **FORMALIZED.** Adjudication then has four constructors:

$$
\operatorname{Adjudicate}\in
\{\mathsf{adjudicated},\mathsf{procedural},
\mathsf{pendingLegalJudgment},\mathsf{solverIncomplete}\}.
\tag{29}
$$

An incomplete solver response maps to `solverIncomplete`, absence of authority maps to `pendingLegalJudgment`, and procedural inputs remain procedural. Substantive success or failure requires request-bound authority. This is a type-level refusal to equate computational completion with authorized adjudication.

Authority has an ordinal rank. For level (l) and action kind (k),

$$
\operatorname{canIssue}(l,k)\iff
\operatorname{rank}(l)\ge\operatorname{rank}(\operatorname{required}(k)).
\tag{30}
$$

A one-step receipt must move exactly one rank:

$$
\operatorname{receiptValid}(r)\iff
\operatorname{rank}(r.to)=\operatorname{rank}(r.from)+1.
\tag{31}
$$

**FORMALIZED.** Repeating same-rank votes cannot promote authority. Human receipts are task-, digest-, time-, and revocation-bound:

$$
\operatorname{bind}(r,t,d)\iff r.task=t\land r.digest=d,
\tag{32}
$$

$$
\operatorname{valid}(r,now)\iff
r.issued\le now\le r.expiry\land\neg r.revoked.
\tag{33}
$$

The receipt records an action and reviewer and proves only the stated task/digest and time/revocation predicates. It does not authenticate the reviewer, establish institutional authorization or competence, or prove that the human judgment was legally right.

## 10. Exact quantities, coverage, and trust

ULM13 uses dimension-indexed expressions. Literals, addition, subtraction, and scalar multiplication have exact rational denotations:

$$
\begin{aligned}
\llbracket lit(q)\rrbracket&=q,\\
\llbracket x+y\rrbracket&=\llbracket x\rrbracket+\llbracket y\rrbracket,\\
\llbracket x-y\rrbracket&=\llbracket x\rrbracket-\llbracket y\rrbracket,\\
\llbracket qx\rrbracket&=q\llbracket x\rrbracket.
\end{aligned}
\tag{34}
$$

**FORMALIZED.** Type indices prevent direct addition of mismatched dimensions. The evaluator is proved equal to the recursive denotation. This establishes arithmetic coherence, not correctness of the legal rule that supplied the expression.

Coverage remains explicit:

$$
\operatorname{Complete}(C)\iff C.openObligations=\varnothing,
\tag{35}
$$

$$
open(C_1\sqcup C_2)=open(C_1)\cup open(C_2).
\tag{36}
$$

Trust is a five-coordinate ordinal vector, not a probability:

$$
\tau=(\tau_s,\tau_t,\tau_f,\tau_p,\tau_a)\in\{0,1,2\}^{5}.
\tag{37}
$$

Composition takes the coordinatewise minimum,

$$
(\tau\wedge\sigma)_i=\min(\tau_i,\sigma_i),
\qquad \tau\wedge\sigma\preceq\tau,\sigma.
\tag{38}
$$

**FORMALIZED.** Assurance packages merge only within a common scope; implementation and run-check statuses take the weaker value; unresolved obligations, legal inputs, trusted-computing-base references, and notices are unioned. Composition therefore cannot improve assurance through aggregation.

## 11. Temporal applicability and non-interference

Legal materials are time-indexed. An interval intersection is

$$
[a,b]\cap[c,d]=
\begin{cases}
[\max(a,c),\min(b,d)],&\max(a,c)\le\min(b,d),\\
\varnothing,&\text{otherwise}.
\end{cases}
\tag{39}
$$

An authority version is effective at (t) when its start has passed and its optional end has not:

$$
\operatorname{effectiveAt}(v,t)\iff
v.from\le t\land(v.to=\bot\lor t\le v.to).
\tag{40}
$$

Observation is as-of safe only if

$$
\operatorname{observationAllowed}(t_{obs},t_{asof})
\iff t_{obs}\le t_{asof}.
\tag{41}
$$

**FORMALIZED.** ULM rejects future, retracted, and superseded sources. Its Kripke-style “always” guard is conditional: when all reachable worlds already satisfy the temporal ordering, the guard holds globally, following the general tradition of modal and temporal semantics [@Kripke1963; @Pnueli1977; @ClarkeEtAl1986]. It is not a theorem that arbitrary transitions preserve the ordering from the initial state.

Taint is a two-point join algebra:

$$
\mathsf{clean}\sqcup\mathsf{clean}=\mathsf{clean},
\qquad x\sqcup\mathsf{tainted}=\mathsf{tainted}.
\tag{42}
$$

**FORMALIZED.** Any tainted input taints the combined output. Replication does not sanitize it:

$$
\bigsqcup_{i=1}^{n}\mathsf{tainted}=\mathsf{tainted}.
\tag{43}
$$

This blocks a characteristic multi-agent failure: correlated agents cannot manufacture provenance merely by agreeing.

## 12. Incrementality and convergence

For an add-only Horn update $\Delta=(\Delta_F,\Delta_R)$,

$$
F'_0=F_0\cup\Delta_F,
\qquad R'=R\cup\Delta_R,
\qquad U'=U.
\tag{44}
$$

The consequence operator and closure are monotone across the update:

$$
T_H(S)\subseteq T_{H+\Delta}(S),
\qquad C_H\subseteq C_{H+\Delta}.
\tag{45}
$$

**FORMALIZED.** A correct incremental implementation is specified extensionally:

$$
\operatorname{Correct}(impl)\iff
\forall\Delta,\quad impl(\Delta)=\operatorname{FullRecompute}(H+\Delta).
\tag{46}
$$

This is a refinement contract. It is not evidence that a particular worklist implementation satisfies the contract.

The development also contains a general Banach theorem. If \(f\) is a contraction with constant \(0\le K<1\) on a nonempty complete metric space, then its fixed point \(x^*\) is unique and

$$
d(f^n(x),x^*)\le\frac{K^n}{1-K}d(x,f(x)).
\tag{47}
$$

For positive weights (w_i), the weighted sup distance is

$$
d_w(x,y)=\max_i\frac{|x_i-y_i|}{w_i}.
\tag{48}
$$

Coordinate bounds

$$
|T(x)_i-T(y)_i|\le\sum_jL_{ij}|x_j-y_j|,
\qquad \sum_jL_{ij}w_j\le q w_i
\tag{49}
$$

imply \(d_w(Tx,Ty)\le qd_w(x,y)\). **FORMALIZED.** No theorem establishes that the complete legal evaluator is such a contraction. The weighted-distance file proves metric properties for finite real vectors; a misleading declaration name must not be read as a proof of `CompleteSpace`.

## 13. Release evidence and reproducibility

The formal corpus is tested as a commit-bound release candidate, not as a floating claim about a repository name. The proof inventory contains 145 declarations in the full theorem audit and 27 in the core composition audit. Axiom output permits only the standard dependencies `propext`, `Classical.choice`, and `Quot.sound`; no custom axiom is admitted. The reproducibility locator is [GitHub Actions run `33946211096`](https://github.com/laubeing-droid/legal-math-modeling/actions/runs/33946211096), bound to subject `2a1d33df353a005dffc5d8b95faa591524e2636e` and tree `c7525f767b43c7e8a663a4a9702f64cdea78b979`; the relevant archives are named `lean-full-build`, `python-gates`, and `release-certificate`. These counts describe the audited subject and should not be transplanted to later commits without regenerating evidence. Because hosted artifact retention is finite, long-term scholarly reproduction requires a separate durable deposit of those archives.

The certificate pipeline binds a subject commit, CI run identity, build logs, theorem manifests, axiom audits, claim audits, a mutation-property report, cross-repository refinement evidence, and an independent verifier verdict. The design is intentionally self-hostile in one narrow sense: certificate generation failure is a job failure, missing evidence remains listed, and the independent report must agree with certificate status. A green workflow icon is therefore not enough; the JSON contents are the authoritative release statement.

The mutation gate uses executable fixtures rather than a fabricated pass file. A baseline must pass, and deliberately altered inputs must be rejected for the expected property. Runtime refinement receipts are generated in the separately authorized `juris-calculus` repository and consumed across repositories. **DERIVED.** Together these mechanisms reduce the gap between theorem-level interfaces and executable implementations. They do not make a finite fixture suite a proof of all runtime behavior.

Reproduction should therefore report a tuple:

$$
E=(sha,tree,run,modules,axioms,mutation,receipts,certificate,verdict).
\tag{50}
$$

A release claim is acceptable only when every required component refers to the same subject and the final verdict is non-failed. This paper reports the architecture; exact current evidence must always be read from the archived artifacts for the named subject.

## 14. What remains outside the proved core

Several attractive research claims are deliberately excluded.

First, Bayesian legal reasoning is well developed in the literature [@FentonNeilLagnado2013; @VlekEtAl2015; @FentonNeilBerger2016], but the current Lean edge kind named `probabilityKernel` creates obligations rather than defining a probability kernel. Bayes updates, calibration, and proper scoring are **CONJECTURE** extensions.

Second, the repository does not prove a graph-similarity metric. Earlier candidate axioms were removed after counterexamples. Transferring the weighted sup metric to graphs would require a justified embedding \(\phi:G\to\mathbb R^n\); without it, metric claims are **CONJECTURE**.

Third, differential privacy requires adjacency, mechanisms, and quantitative privacy parameters [@DworkEtAl2006; @DworkRoth2014]. A legal privilege label cannot determine a unique $\varepsilon$. The repository records counterexample evidence, not a Lean differential-privacy theorem. Any mapping from privilege to privacy budget is at most **DERIVED** within additional institutional assumptions.

Fourth, legal analogy and precedent have substantive theories [@RisslandAshley1987; @BenchCaponSartor2003; @Horty2011; @Teitelbaum2015], but the proved core contains no generic analogy-strength relation. Structural support, branch, and trust guards may constrain an analogy engine; they do not validate its similarity judgment.

Fifth, traceability is not human explanation quality. The architecture can preserve witnesses, dependencies, branches, and authority receipts. Whether an explanation is comprehensible, causally faithful, or legally sufficient requires separate user studies and doctrinal criteria [@RibeiroEtAl2016; @Lipton2018; @GuidottiEtAl2018; @WachterEtAl2018].

Finally, the system is not a theorem of tort liability. Current European AI regulation and product-liability rules supply important legal context [@EU2024AIAct; @EU2024ProductLiability; @Hacker2023], but fault, defect, causation, damage, defenses, and allocation are not represented as proved ULM semantics. The architecture can carry evidence and authority for liability analysis; the analysis itself remains jurisdiction- and fact-dependent.

## 15. Discussion

The architecture’s main theoretical move is separation followed by typed composition. Horn closure answers what support follows monotonically from an admitted base. Argumentation semantics answers which supported arguments survive attacks under a selected profile. Procedure answers whether a result is substantive, procedural, pending human judgment, or computationally incomplete. Coverage and trust answer what remains unresolved and how assurance degrades. Temporal and receipt layers answer when material is applicable and who may authorize a transition. No layer is allowed to impersonate another.

This separation has a practical consequence for AI systems. A language model may propose a fact, rule encoding, attack, explanation, or calculation, but proposal does not alter its authority. It must enter through an obligation-bearing edge, acquire evidence of the advertised kind, remain tied to the request and branch, and retain taint where provenance is inadequate. Multiple proposals may improve search coverage; they cannot vote themselves into verified truth. That design is compatible with hybrid human–AI workflows while making the authority boundary explicit.

The architecture also offers a disciplined answer to the “symbolic versus statistical” debate. Statistical models may supply observations or candidate rankings. Symbolic rules may supply closure and argument structure. Formal proofs may establish preservation properties. Human decision-makers may provide legal authorization. The system does not require one method to replace the others. It requires each method to declare what it supplies and forbids downstream composition from strengthening that declaration without a witness.

## 16. Limitations

The proof corpus is a specification artifact. It does not prove the factual truth of inputs, the completeness of a legal ontology, the validity of a jurisdictional rule base, the soundness of every external verifier, or the behavioral equivalence of every runtime implementation. ULM16 demonstrates concrete normal-form composition instances rather than closing every TheorySpec family. The typed graph exposes node kinds but not a dependent payload proof for every kind. Argument coverage is relative to a frozen expected carrier. The exact evaluator proves denotational agreement, not statutory interpretation. Incremental correctness is a contract, not a completed proof of a production algorithm.

The empirical evidence is finite. Mutation fixtures can show that specified perturbations are detected; they cannot quantify all fault classes. Cross-repository receipts can bind an execution to a task, digest, time, and authority transition; they cannot establish that a human legal judgment is correct. The formal release process is only as current as its subject SHA and archived artifacts.

No human subjects, private legal files, customer data, or confidential model outputs were used. The work does not evaluate accuracy, fairness, usability, or disparate impact in operational legal settings. Deployment would require jurisdiction-specific legal validation, security review, data governance, accessibility evaluation, and continuing monitoring.

## 17. Conclusion

The ULM architecture demonstrates that heterogeneous legal computation can be made compositionally conservative. **FORMALIZED:** request identity is preserved; failure is not upgraded by mapping; typed transitions retain scope; obligations are nonempty; verifier success is meaningful only under a soundness contract; finite Horn iteration yields a least closure; arguments, attacks, and extensions are request-bound; incompatible branches do not compose; incomplete computation and absent authority remain visible; dimensional arithmetic is exact; open obligations union; trust meets downward; add-only Horn updates preserve prior closure; temporal applicability excludes future and superseded sources; authority receipts record ranks while peer consensus cannot promote them, task/digest predicates prevent cross-task or cross-input reuse under their stated equalities, and taint cannot be removed by the formalized consensus operators.

**DERIVED:** a release pipeline that binds these artifacts to one commit and checks real mutation/refinement evidence gives a stronger assurance case than build success alone. **CONJECTURE:** probability, analogy strength, graph metrics, explanation quality, privacy-budget selection, and substantive liability can be added without violating the architecture if they receive their own semantics, evidence obligations, and legal authorization rules.

The appropriate claim is therefore precise: the system proves selected invariants of a legal-reasoning specification and its composition boundaries. It does not prove “the law,” replace adjudication, or turn AI agreement into authority. That restraint is not a weakness of the model; it is the condition under which formal legal computation can be audited.

## Declarations

**Funding.** This research received no specific grant from any funding agency in the public, commercial, or not-for-profit sectors.

**Declaration of interests.** The author declares no known competing financial interests or personal relationships that could have appeared to influence the work.

**Data and code availability.** No new empirical dataset was created. The formal definitions, theorem sources, scripts, manifests, and release documentation are available in the `legal-math-modeling` repository [@LegalMathModeling2026]. Commit-specific CI artifacts must be consulted for release claims.

**Ethics.** The study used no human participants, personal data, customer matters, or confidential legal records. It is a formal-methods and software-artifact study.

**CRediT author statement.** Laupinco: Conceptualization, Methodology, Formal analysis, Software, Validation, Investigation, Resources, Data curation, Writing—original draft, Writing—review and editing, Project administration.

**AI disclosure.** AI-assisted tools supported literature-search planning, structural drafting, language revision, and formatting. The author directed the research, checked claims against the cited sources and formal artifacts, made all legal and scholarly judgments, and accepts full responsibility for the manuscript.

## References

Bibliographic metadata for all citation keys is provided in `references.bib`. Entries use verified DOI resolvers, publisher records, official EUR-Lex pages, or the official journal PDF where no journal DOI exists.
