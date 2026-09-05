# Compositional Assurance for Executable Legal Reasoning: A Release-Bounded Formal Architecture

**Laupinco**

## Abstract

Legal-reasoning software combines several activities that are often described by one misleading word: correctness. A kernel may accept a theorem while an executable adapter mis-serializes its input; a runtime may reproduce selected fixtures while its legal premises remain unauthorized; a continuous-integration job may be green while a certificate records missing evidence. This paper presents a compositional assurance architecture that keeps those questions separate and makes their permitted connections explicit. The architecture is implemented in the `legal-math-modeling` repository as sixteen Unified Legal Model modules (ULM01–ULM16). They cover request identity, fail-closed outcomes, typed transition graphs, proof obligations, machine execution, fact provenance, Horn closure, canonical arguments, attacks and defeats, Dung semantics, branch-sensitive queries, procedure, dimensioned exact arithmetic, coverage and trust, add-only refinement, empirical annotations, and theory composition. The formal corpus is accompanied by a subject-bound release pipeline rather than inferred from workflow colour. At the reported release subject, the full ULM theorem audit enumerates 145 declarations and the core-composition audit enumerates 27; the audit output contains no project-defined axiom and only the admitted library-level dependencies `propext`, `Classical.choice`, and `Quot.sound`. Executable mutation fixtures and cross-repository refinement receipts add bounded engineering evidence. They do not convert finite testing into universal proof. The central result is therefore an assurance algebra, not a claim that law has been automated: guarantees compose only when identity, scope, failure state, evidence provenance, and authority remain compatible. Probability assignments, differential privacy, graph similarity, analogical strength, explanation quality, liability, and substantive legal correctness remain outside the proved boundary unless separately specified and evidenced.

## 中文摘要

法律推理软件常把多种不同问题统称为“正确性”：Lean 内核接受某个定理，并不保证 Python 适配器没有序列化错误；运行时通过若干夹具，并不表示其法律前提已经获得授权；持续集成任务显示绿色，也不表示证书内容没有缺失证据。本文提出一套可组合但严格限界的保证架构，并在 `legal-math-modeling` 仓库的 ULM01–ULM16 中实现。十六个模块依次处理请求身份、失败封闭结果、类型化转换图、证明义务、机器执行、事实来源、Horn 闭包、规范论证、攻击与击败、Dung 语义、分支查询、程序状态、带量纲精确算术、覆盖与信任、仅新增精化、经验性附注及理论组合。本文不以 CI 任务颜色代替发布结论，而要求证书绑定同一提交、源码树、运行身份和证据集合。在所报告的 subject 上，全量 ULM 公理审计覆盖 145 个声明，核心组合审计覆盖 27 个声明；输出未发现项目自定义公理，仅出现 `propext`、`Classical.choice` 与 `Quot.sound`。真实 mutation 夹具与跨仓 refinement receipt 提供有限的工程证据，但不会把有限测试升级为普遍证明。本文的核心结论是一种保证代数：只有请求身份、范围、失败状态、证据来源和裁决权限兼容时，局部保证才能组合。概率、差分隐私、图相似度、类比强度、解释质量、责任归属与实体法律正确性均不在已证明范围内，除非另行定义、验证并取得法律授权。

**Keywords:** formal methods; computational law; argumentation semantics; fail-closed verification; proof provenance; release certificate; refinement receipt

**关键词：** 形式化方法；计算法学；论证语义；失败封闭验证；证明来源；发布证书；精化回执

## 1. Introduction

Formal methods can establish exact propositions about exact models. They cannot, by themselves, decide whether the model contains the right law, whether a witness came from an admissible source, whether an executable program implements the model, or whether an institution authorizes the resulting disposition. Treating these questions as one scalar notion of confidence creates a predictable failure: evidence produced for one layer is silently spent at another. A successful build is presented as legal validation; a benchmark becomes a proof; an authorized human decision is mistaken for a theorem; or a theorem about a finite abstract argumentation framework is generalized to a production pipeline that was never related to it.

The engineering problem is not simply to prove more. It is to prevent valid local proofs from being used outside their domain. Hoare-style program logic already teaches that a judgment has preconditions, a command, and postconditions rather than an unqualified label of correctness [@Hoare1969]. Fixed-point semantics likewise derive consequences relative to a specified carrier and operator [@Tarski1955]. Abstract interpretation emphasizes that a sound relation depends on a declared abstraction boundary [@CousotCousot1977]. The present architecture applies that discipline to a legal-reasoning pipeline and adds release evidence that preserves the identity of the artifact to which each claim belongs.

The paper uses three labels throughout. **FORMALIZED** denotes a proposition elaborated by Lean and included in the audited subject. **DERIVED** denotes a mathematical or engineering consequence that follows from formal results plus explicitly stated premises, or an observation established by subject-bound executable evidence. **CONJECTURE** denotes a proposed extension, empirical hypothesis, or legal interpretation not proved in the formal corpus. These labels are disjoint as evidentiary classes even when the same sentence contains objects from several layers.

The architecture distinguishes four coordinates of assurance. For a system artifact (x), define

$$
\mathcal{A}(x)=\bigl(F(x),R(x),E(x),L(x)\bigr),
\tag{1}
$$

where (F) is formal theorem status, (R) is runtime-refinement evidence, (E) is empirical support, and (L) is legal authorization or substantive legal judgment. **DERIVED.** No coordinate determines another without a separately proved bridge:

$$
F(x)\not\Rightarrow R(x),\qquad R(x)\not\Rightarrow L(x),\qquad
E(x)\not\Rightarrow F(x),\qquad L(x)\not\Rightarrow F(x).
\tag{2}
$$

This non-collapse principle is the paper's central organizing constraint. It is not philosophical ornament. It determines data types, transition rules, query semantics, certificate structure, and the wording permitted in release reports.

The research questions are:

1. How can a legal-reasoning architecture preserve request and case identity across heterogeneous transformations?
2. How can incompleteness, failure, and contested evidence remain visible rather than being coerced into a successful result?
3. Which fixed-point, argumentation, procedural, arithmetic, and incremental properties can be composed as Lean theorems?
4. What do mutation fixtures, refinement receipts, axiom audits, and release certificates add, and what do they leave unproved?
5. Which attractive extensions must remain conjectural because their premises or bridge theorems are absent?

**FORMALIZED.** ULM01–ULM16 answer the first three questions for the explicit types and hypotheses described below. **DERIVED.** The release pipeline answers the fourth for one recorded subject, using executable evidence that is deliberately narrower than a proof of the whole runtime. **CONJECTURE.** The fifth question defines a research programme rather than a completed theorem family.

## 2. Related Work and the Missing Assurance Boundary

Dung's abstract argumentation framework supplies the basic pair \(AF=(A,\rightarrow)\), with extensions determined by attacks among arguments [@Dung1995]. Preference-sensitive and structured approaches add priorities, defeasible rules, values, and proof standards [@PrakkenSartor1997; @BenchCapon2003; @BenchCaponSartor2003; @ModgilPrakken2013]. Those theories explain how acceptance may be computed once the framework and semantics are fixed. They do not automatically establish that a runtime constructed the intended framework from admissible legal materials.

Nonmonotonic logic provides a second foundation. Reiter's defaults, circumscription, defeasible logics, and Horn consequence operators show how conclusions depend on rule activation, exceptions, and least fixed points [@Reiter1980; @McCarthy1980; @AntoniouEtAl2001; @Maher2001; @Horn1951]. The present work uses a finite Horn closure as a support layer and keeps defeat semantics separate. This separation prevents a priority or attack policy from being hidden inside ordinary deductive closure.

Temporal logic and normative systems introduce further distinctions. Kripke structures and linear-time operators make truth world- and path-sensitive [@Kripke1963; @Pnueli1977; @ClarkeEtAl1986]. Deontic traditions distinguish obligation, permission, prohibition, and constitutive rules [@VonWright1951; @MakinsonVanDerTorre2000]. The architecture uses bounded temporal applicability and minimal deontic slices, but it does not claim a complete jurisprudential theory of time or normativity.

Probabilistic legal reasoning and Bayesian networks can represent uncertainty over evidence and hypotheses [@TaroniEtAl2014; @FentonNeilLagnado2013; @VlekEtAl2015; @FentonNeilBerger2016]. Explainability research studies local surrogates, counterfactuals, and the limits of post hoc accounts [@RibeiroEtAl2016; @Lipton2018; @GuidottiEtAl2018; @WachterEtAl2018]. Privacy research provides precise mechanisms, adjacency relations, and composition laws [@DworkEtAl2006; @DworkRoth2014; @NissimEtAl2007; @AbadiEtAl2016]. These bodies of work are relevant, but relevance is not formal inclusion. Probability, explanation quality, and differential privacy are treated below as explicit non-results because the current ULM core does not define their required semantics.

Lean offers a small trusted kernel in which declarations can be checked against explicit dependencies [@DeMouraUllrich2021]. Mathlib supplies reusable mathematical infrastructure [@Mathlib2020]. Yet kernel acceptance is only one coordinate in Equation (1). The missing boundary in many descriptions of formally informed legal software lies between an accepted theorem, a built executable, a tested adapter, a valid evidence package, and an authorized legal act. This paper makes that boundary an object of design.

## 3. Method: Models, Claims, and Composition Conditions

The method is source-bounded. Each formal claim is tied to a named declaration in `proofs/lean/juris_lean/JurisLean/`; each release claim is tied to a subject commit and CI run; each runtime claim is tied to fixture identifiers and receipt bindings. Narrative prose has no authority to enlarge any of those sets.

Let a claim record be

$$
c=(\mathit{id},\mathit{label},\mathit{subject},\mathit{scope},\mathit{evidence}).
\tag{3}
$$

Its admissibility requires label-specific evidence:

$$
\operatorname{Admissible}(c)\iff
\begin{cases}
\operatorname{KernelAccepted}(c.evidence,c.subject), & c.label=\mathrm{FORMALIZED},\\
\operatorname{PremisesListed}(c)\land\operatorname{DerivationValid}(c), & c.label=\mathrm{DERIVED},\\
\operatorname{MarkedOpen}(c), & c.label=\mathrm{CONJECTURE}.
\end{cases}
\tag{4}
$$

The architecture forbids composition merely because two artifacts share a human-readable case name. Let (k) be a context key and (r) a request key. ULM01 requires internal scope agreement:

$$
\operatorname{WFContext}(k)\iff k.\mathit{runScope}.\mathit{caseScope}=k.\mathit{caseScope}.
\tag{5}
$$

A transformation \(f:\alpha\to\beta\) preserves an observable request identity when

$$
\operatorname{Preserves}(o_\alpha,o_\beta,f)
\iff \forall x\in\alpha,\ o_\beta(f(x))=o_\alpha(x).
\tag{6}
$$

**FORMALIZED.** `JurisLean.ULM.preserves_comp` proves that preservation composes. If (f) and (g) preserve the observation, then

$$
o_\gamma(g(f(x)))=o_\alpha(x).
\tag{7}
$$

This small theorem does significant architectural work. Every later bridge can state which observation it preserves, rather than relying on informal naming conventions.

Composition also requires compatible assurance scope. For envelopes (a) and (b), the combination is partial:

$$
a\otimes b=
\begin{cases}
\operatorname{some}(\operatorname{combine}(a,b)), & a.scope=b.scope,\\
\operatorname{none}, & a.scope\ne b.scope.
\end{cases}
\tag{8}
$$

**FORMALIZED.** ULM14 proves rejection of incompatible scopes and preservation of the common scope when composition succeeds. **DERIVED.** Equations (6) and (8) jointly rule out two common mistakes: cross-request evidence reuse and cross-scope assurance laundering.

### 3.1 Assurance obligations as typed interfaces

An assurance boundary is useful only if it changes what downstream stages may do. The project therefore treats an evidence object as a typed interface rather than a persuasive paragraph. A theorem declaration can discharge a formal proposition with specified hypotheses. A module-build record can establish that a source file elaborated in a pinned environment. A mutation report can establish rejection of enumerated malformed fixtures. A runtime receipt can establish that a named executable produced a named result from a named input. A legal-authority record can establish that the model received a decision from an identified authority under an encoded permission rule. None of these objects is interchangeable.

**DERIVED.** The practical consequence is a no-substitution rule. If an interface requires a kernel-accepted theorem, a regression test cannot satisfy it. If it requires a runtime receipt, a theorem about an abstract function cannot satisfy it. If it requires authorized legal input, neither a theorem nor a receipt can satisfy it. This rule is stricter than ordinary documentation because it makes absence machine-visible. A field remains open, pending, failed, or missing until evidence of the required kind arrives.

The architecture distinguishes an object's payload from the authority to rely on that payload. An evidence token may carry text and provenance while remaining assumed. A proof subject may be syntactically well formed while lacking a sound verifier entry. An extension family may be mathematically well defined while a query has no entry witness. A legal status may be representable while the issuer lacks authority. These are not exceptional edge cases. They are normal intermediate states in research and adjudication, and the data model must preserve them.

**FORMALIZED.** ULM02, ULM06, ULM11, ULM12, and ULM14 provide distinct constructors or predicates for these states. **DERIVED.** Because the distinctions exist in the type and proposition layer, later stages can be forbidden from collapsing them by pattern matching on a generic success flag. This design reduces equivocation between “the system returned an object,” “the object satisfied a formal predicate,” and “an authorized decision was made.” It does not stop every possible external consumer from ignoring the distinction, but such a consumer cannot honestly cite the relevant ULM preservation theorem.

### 3.2 Threat model

The threat model includes accidental and strategic claim inflation. Accidental inflation occurs when a developer reads a successful test as evidence for a theorem, combines outputs from two branches, treats solver timeout as absence, or copies a certificate generated before its run identity existed. Strategic inflation occurs when a report deliberately suppresses missing evidence, treats repeated low-authority statements as consensus, or advertises finite conformance fixtures as whole-program verification. The architecture does not assume a malicious operating system or prove cryptographic security. Its target is evidence-boundary failure inside a controlled release and research workflow.

Five threats organize the controls. The first is identity drift. An artifact may be correct for request (r_1) but attached to (r_2), or it may belong to source commit (s_1) but appear in a release for (s_2). ULM request preservation addresses the semantic pipeline; subject and tree bindings address the release pipeline. The second threat is state upgrading. Partial, failed, pending, or incomplete results may be serialized as success. The outcome and procedural constructors prevent that conversion inside their typed relations. The third threat is provenance cleaning. Assumed or tainted premises may acquire apparent credibility through aggregation. Dependency sets, taint join, trust meet, and receipt rank prevent this within the formal model.

The fourth threat is semantic mixing. Grounded, preferred, complete, and stable semantics answer different questions. Sceptical and credulous acceptance quantify differently over extension families. Factual scenarios with different assumptions describe different worlds. ULM11's branch key therefore treats scenario, assumptions, and semantic profile as part of result identity. The fifth threat is bridge fiction: a formal function and a runtime implementation may be described by similar names without a verified relation. Mutation reports and external receipts test selected bridge properties, while the absence of a universal refinement theorem remains explicit.

**DERIVED.** These threats explain why a single confidence score is unsuitable. If a five-coordinate trust vector were averaged, a high proof score could numerically compensate for absent legal authority. If release checks were reduced to one Boolean job conclusion, a missing subject SHA could be hidden by unrelated successful jobs. The architecture instead retains product structure: every necessary coordinate must meet its own threshold, and combination takes the weaker input where an order is defined.

### 3.3 Proof strategy and finite carriers

The recurring proof strategy is finite monotone iteration. Horn closure and the Dung characteristic operator are monotone over finite powersets. Starting from a lower element and iterating cannot add more than the finite carrier contains, so stabilization occurs within a cardinality bound. The proof architecture factors this reasoning into a reusable finite-monotone component and then instantiates it for each operator. This gives fixedness and leastness without assuming an opaque solver is correct.

**FORMALIZED.** The finite iteration module proves that a monotone, inflationary operator over a finite universe stabilizes at or before the carrier's cardinality. Horn and Dung modules instantiate that result. **DERIVED.** The bound is mathematical, not a benchmark prediction. It counts semantic iterations of the encoded operator and does not state wall-clock complexity for a runtime, memory use, serialization overhead, or solver scheduling.

Finite carriers also make enumerator specifications tractable. Preferred, complete, and stable families can be defined by filtering a powerset reference universe. This is valuable as an executable mathematical reference even when it is not efficient enough for large production inputs. A faster implementation can be compared against that reference on bounded fixtures, but performance optimization does not inherit correctness automatically. It must satisfy an explicit equality or refinement relation.

The same discipline governs argument coverage. Equality between actual and expected finite carriers supports an exact Boolean checker theorem. It cannot establish that the expected carrier is legally exhaustive. Selecting the expectation is an upstream modeling act. **CONJECTURE.** A stronger generator-completeness result would require an inductive characterization of all permissible argument constructions and a proof that the generator enumerates exactly those constructions. That target is intentionally not inferred from finite fixture equality.

### 3.4 Legal input as an independent premise

Legal propositions depend on authority, jurisdiction, temporal applicability, procedural posture, and interpretation. The model can represent these dependencies, but representation does not validate their contents. For example, a source bundle may include a provision with dates and provenance. Temporal predicates can reject observations from the future or sources marked retracted. Neither operation decides whether the provision governs the dispute or how an ambiguous phrase should be construed.

**DERIVED.** Legal input therefore enters the assurance envelope as an independent status with retained references. A complete formal proof over assumed legal premises is still conditional. A runtime that faithfully refines the formal function is still conditional. This is comparable to proving a program correct relative to a specification while separately asking whether the specification expresses the intended policy. The architecture makes that familiar separation visible in legal terms.

Human authority is likewise modeled as a gate, not simulated as a conclusion. A validated authority object has identity and request bindings, and procedural theorems constrain what follows once it is supplied. **FORMALIZED.** The model blocks pending and solver-incomplete states from equaling adjudicated status. **CONJECTURE.** It does not prove that an external person holds office, has jurisdiction, followed due process, or interpreted the law correctly. Those facts require institutional evidence beyond the formal kernel.

### 3.5 Claim discipline for the remainder of the paper

Every section below follows the same reporting rule. A FORMALIZED claim names the relevant module or theorem family and repeats the material hypotheses when omission could mislead. A DERIVED claim identifies the additional premise, such as the existence of a subject-bound CI artifact or a finite fixture report. A CONJECTURE claim is never used as a premise for a formalized result. Counterexamples and failed historical receipts are retained because they define the edge of an admissible inference.

This discipline also limits negative claims. Saying that differential privacy is not established does not show that privacy is impossible. Saying that a graph metric is not proved does not show that no suitable metric exists. Saying that runtime refinement is demonstrated only for three fixtures does not imply that the remaining inputs diverge. In each case, the correct status is absence of the stronger evidence, not evidence for its negation. This distinction prevents fail-closed reporting from becoming unwarranted pessimism.

Finally, the paper separates source truth from presentation. Equations provide a readable mathematical reconstruction of Lean definitions, but the Lean source determines exact syntax and theorem scope. Tables summarize release artifacts, but the JSON and logs determine their contents. Prose can help a legal or engineering reader understand why a boundary matters. It cannot amend a theorem, change a receipt, or authorize a legal conclusion.

## 4. ULM01–ULM04: Identity, Outcomes, Graphs, and Obligations

### 4.1 Normal form and request identity

ULM01 defines the normal-form vocabulary: semantic profiles, layers, node kinds, edge kinds, claim kinds, context keys, request keys, and positions. The representation is intentionally administrative as well as semantic. Legal computations are not anonymous functions over propositions. They operate within a case, run, request, source, and semantic profile.

**FORMALIZED.** The normal-form preservation relation in Equation (6) is closed under function composition. **DERIVED.** A pipeline of (n) individually preserving transformations therefore satisfies

$$
o_n\circ f_n\circ\cdots\circ f_1=o_0.
\tag{9}
$$

This equation does not prove that the transformations preserve every property. It proves only the selected observation. The distinction is essential: request identity can be preserved while legal meaning is corrupted, so semantic refinement remains a separate obligation.

### 4.2 Fail-closed result algebra

ULM02 defines a three-way outcome:

$$
\operatorname{Outcome}(X)=
\operatorname{Complete}(x)\mid
\operatorname{Partial}(x,O)\mid
\operatorname{Failure}(e),
\qquad O\ne\varnothing.
\tag{10}
$$

The nonempty obligation set is not decorative metadata. It witnesses why a partial result is not complete. Mapping a function over an outcome is shape-preserving:

$$
\operatorname{map}(f,\operatorname{Failure}(e))=\operatorname{Failure}(e).
\tag{11}
$$

**FORMALIZED.** `failure_ne_complete`, `partial_ne_complete`, and `map_never_upgrades_failure` establish that neither a failed nor partial constructor becomes complete by mere mapping. **DERIVED.** Any adapter that catches a failure and emits a success-shaped object is outside this algebra and must not inherit its claims.

Define an information order only for release interpretation:

$$
\operatorname{Failure}\preceq\operatorname{Partial}\preceq\operatorname{Complete}.
\tag{12}
$$

**DERIVED.** A safe transformation is non-upgrading unless it discharges recorded obligations with new evidence. Equation (12) is an explanatory order, not a Lean theorem in ULM02.

### 4.3 Typed transition graphs

ULM03 represents a finite graph of typed nodes and edges. For edge (e) in graph (G), well-formedness includes graph membership, request agreement, and declared incidence:

$$
\operatorname{EdgeWF}(G,e)\Rightarrow
e\in G.E\land e.request=G.request\land
e.source,e.target\in G.V.
\tag{13}
$$

For local state (s=(A,C,r,p)), an edge is enabled when its source is active, the edge is not completed, and the request matches. Application extends the active set and completed set:

$$
\operatorname{applyEdge}(e,s).active=s.active\cup\{e.target\},
\tag{14}
$$

$$
\operatorname{applyEdge}(e,s).completed=s.completed\cup\{e\}.
\tag{15}
$$

**FORMALIZED.** `target_subset_applyEdge`, `localTransition_preserves_request`, and `localTransition_has_declared_edge` prove target inclusion, request preservation, and declared-edge membership. **CONJECTURE.** A fully dependent payload type in which each node kind statically determines its payload is not closed by these theorems. The current kind tag is useful but weaker.

### 4.4 Proof obligations and sound verification contracts

ULM04 assigns baseline obligations to edge kinds and additional obligations to claim kinds. The required set is

$$
\operatorname{Req}(e)=\operatorname{Baseline}(e.kind)
\cup\bigcup_{c\in e.claims}\operatorname{ForClaim}(c)
\cup\{\mathrm{typeSafety}\}.
\tag{16}
$$

**FORMALIZED.** `typeSafety_mem_required` and `requiredObligations_nonempty` show respectively that type safety is always required and the obligation list is nonempty.

A verifier entry binds a subject and evidence. Soundness is a predicate, not a property inferred from the name “verifier”:

$$
\operatorname{VerifierSound}(P,v)\iff
\forall s,\ \operatorname{Accepts}(v,s)\rightarrow P(s).
\tag{17}
$$

Satisfaction requires exact subject and evidence alignment. **FORMALIZED.** `sat_sound` establishes

$$
\operatorname{VerifierSound}(P,v)\land\operatorname{Sat}(v,s)
\Rightarrow P(s).
\tag{18}
$$

The premise `VerifierSound` is substantive. The theorem does not prove an arbitrary Python checker sound. A runtime checker needs separate tests, mutations, and refinement evidence.

## 5. ULM05–ULM07: Execution, Evidence, and Horn Support

### 5.1 A machine that cannot manufacture a new request

ULM05 lifts local transitions into a small machine with running and halted states. A configured edge is enabled once when graph membership, local enablement, and the once-only condition hold. If (C) is the completed set,

$$
\operatorname{runEnabled}(e,c)\Rightarrow e\notin C.
\tag{19}
$$

After application,

$$
e\in\operatorname{applyRunEdge}(e,c).completed,
\tag{20}
$$

so the same edge is not re-enabled. The phase counter advances by one, but phase arithmetic does not itself imply semantic progress.

**FORMALIZED.** `applied_edge_not_reenabled`, `step_preserves_request`, and `run_preserves_request` establish once-only execution and request invariance. A halted machine has no next step. A configuration is quiescent if no graph edge remains enabled; completing all graph edges is sufficient:

$$
G.E\subseteq c.completed\Rightarrow\operatorname{Quiescent}(G,c).
\tag{21}
$$

**DERIVED.** Termination of a particular schedule additionally depends on the finite graph and on executing enabled edges rather than stuttering outside the `Step` relation.

### 5.2 Facts, assumptions, and tainted origins

ULM06 separates establishment, contest status, premise permission, evidence tokens, and assumption witnesses. A premise token has either an admitted origin or an assumed origin. Its dependency function is

$$
\operatorname{deps}(p)=
\begin{cases}
\varnothing, & p.origin=\operatorname{admitted},\\
\{a.id\}, & p.origin=\operatorname{assumed}(a).
\end{cases}
\tag{22}
$$

Tagging preserves the request identifier:

$$
\operatorname{request}(\operatorname{tagPremise}(p))=p.request.
\tag{23}
$$

**FORMALIZED.** Well-formed admitted premises have admitted status, every origin is classified, admitted dependencies are empty, assumed dependencies contain the assumption identifier, and tagging preserves request identity. **DERIVED.** A conclusion supported by an assumed premise must carry that dependency forward. Repetition cannot turn an assumption into an admitted fact.

This is reinforced by the core taint model. With clean and tainted states, join behaves as

$$
\mathrm{clean}\sqcup\mathrm{clean}=\mathrm{clean},\qquad
x\sqcup\mathrm{tainted}=\mathrm{tainted}.
\tag{24}
$$

**FORMALIZED.** The taint noninterference results prevent aggregation, majority, or repeated presentation from cleaning a tainted input. **DERIVED.** Quantity of unverified copies is not a substitute for provenance.

### 5.3 Finite Horn closure

ULM07 attaches request-bound atoms to a Horn system. Let (U) be the finite atom universe and (T_H) its immediate-consequence operator:

$$
T_H(S)=S\cup\{h\in U\mid\exists(B\to h)\in R,\ B\subseteq S\}.
\tag{25}
$$

The closure is computed by a bounded iterate:

$$
\operatorname{Cl}_H=T_H^{|U|}(F_0).
\tag{26}
$$

**FORMALIZED.** The underlying Horn and finite-monotone modules prove monotonicity, stabilization by the finite bound, fixed-point status, leastness, soundness, completeness relative to the encoded Horn system, and minimal-model status. ULM07 proves the request-bound property and the candidate filter soundness:

$$
\operatorname{CandidateWF}(H,c)\Rightarrow c.support\subseteq\operatorname{Cl}_H.
\tag{27}
$$

**DERIVED.** “Complete” here means complete for the finite encoded Horn rules. It says nothing about whether the rule set captures all legally relevant norms or facts.

## 6. ULM08–ULM10: Arguments, Defeats, and Extension Semantics

### 6.1 Canonical support hypergraphs

ULM08 represents an argument as a root, a node set, and support hyperedges. A support hyperedge (h=(P,t)) reads “premises (P) support target (t).” Direct dependency is

$$
x\prec_a y\iff\exists h\in a.H,\ x\in h.premises\land y=h.target.
\tag{28}
$$

Reachability uses the transitive closure of this relation. Availability requires each support node to belong to the argument carrier or to the permitted support closure. The source definition states well-foundedness directly over the dependency relation:

$$
\operatorname{SupportWF}(a):=\operatorname{WellFounded}(\operatorname{SupportDependsOn}(a)).
\tag{29}
$$

**FORMALIZED.** This is the predicate implemented by `SupportWellFounded`; the repository does not state a separate biconditional equating it with a no-cycle formula. **DERIVED.** On the finite concrete support carrier used here, well-foundedness rules out a directed dependency cycle. `ArgumentWF` combines request agreement, root membership, non-dangling hyperedges, availability, and the source predicate. Coverage compares an actual finite argument carrier with a frozen expected carrier:

$$
\operatorname{Coverage}(A,E)\iff A=E.
\tag{30}
$$

**FORMALIZED.** `checkArgumentCoverage_sound` and `checkArgumentCoverage_complete` prove equivalence between the Boolean coverage checker and Equation (30). `covered_argument_is_well_formed` transfers well-formedness from an expected member to a covered actual member. **DERIVED.** This is relative completeness against a supplied finite expectation, not a general theorem that a production argument generator finds every legally valid argument.

### 6.2 Typed attacks and policy-resolved defeats

ULM09 defines attack kinds and requires a nonempty witness with matching request identity. For a validated attack set $A$ and a Boolean policy $\pi$, defeat resolution is filtering:

$$
\operatorname{Defeat}_\pi(A)=\{a\in A\mid \pi(a)=\mathrm{true}\}.
\tag{31}
$$

Membership therefore has the exact characterization

$$
a\in\operatorname{Defeat}_\pi(A)
\iff a\in A\land\pi(a)=\mathrm{true}.
\tag{32}
$$

**FORMALIZED.** Every resolved defeat has a well-formed source attack and preserves request identity. Query refutation is directed and irreflexive:

$$
\neg\operatorname{QueryRefutes}(q,q).
\tag{33}
$$

Contradiction requires the specified reciprocal relation rather than mere disagreement. **CONJECTURE.** The correctness of a concrete legal defeat policy is not established by filtering theorems. `DefeatPolicy.succeeds` is a policy input whose substantive validity needs legal authority and, where executable, refinement evidence.

### 6.3 Grounded, complete, preferred, and stable semantics

ULM10 converts structured arguments and resolved defeats into a finite Dung framework. For \(S\subseteq A\), the characteristic operator is

$$
\Gamma_{AF}(S)=\{a\in A\mid
\forall b\,(b\rightarrow a\Rightarrow\exists c\in S\ c\rightarrow b)\}.
\tag{34}
$$

The grounded extension is the finite iterate

$$
G=\Gamma_{AF}^{|A|}(\varnothing).
\tag{35}
$$

**FORMALIZED.** `groundedExtension_fixed` and `groundedExtension_least` prove

$$
\Gamma_{AF}(G)=G,
\tag{36}
$$

$$
\Gamma_{AF}(S)=S\Rightarrow G\subseteq S.
\tag{37}
$$

Conflict freedom, defence, admissibility, completeness, preferredness, and stability are defined in their standard finite forms [@Dung1995]. In particular,

$$
\operatorname{Admissible}(S)\iff
\operatorname{ConflictFree}(S)\land
\forall a\in S,\operatorname{Defends}(S,a),
\tag{38}
$$

$$
\operatorname{Complete}(S)\iff
\operatorname{Admissible}(S)\land
\forall a,\operatorname{Defends}(S,a)\Rightarrow a\in S,
\tag{39}
$$

$$
\operatorname{Preferred}(S)\iff
\operatorname{Admissible}(S)\land
\nexists T\supsetneq S,\operatorname{Admissible}(T),
\tag{40}
$$

$$
\operatorname{Stable}(S)\iff
\operatorname{ConflictFree}(S)\land
\forall a\in A\setminus S,\exists b\in S,\ b\rightarrow a.
\tag{41}
$$

**FORMALIZED.** The grounded extension is grounded and unique under the encoded definition. The finite preferred family is nonempty; its enumerator is sound and complete. Complete and stable enumerators have exact membership specifications. Existence of a preferred extension does not imply existence of a stable one.

## 7. ULM11–ULM12: Branch-Sensitive Queries and Procedure

### 7.1 Extension results without false totality

ULM11 returns grounded, preferred, complete, or stable extension families according to a semantic profile. It also represents no-extension and incomplete evaluation explicitly. For a discovered family (D) and true family (T), an incomplete result asserts only

$$
D\subseteq T,
\tag{42}
$$

with nonempty open obligations. **FORMALIZED.** Grounded and preferred extension families are nonempty under their encoded conditions. **DERIVED.** Stable evaluation may validly report no extension. A solver timeout must remain incomplete rather than being reported as “no extension,” because absence and failure to establish presence are different propositions.

A branch key includes scenario, assumptions, and semantic profile:

$$
b=(\mathit{scenario},\mathit{assumptions},\mathit{profile}).
\tag{43}
$$

Composition as one legal outcome requires equality of branch keys:

$$
\operatorname{Composable}(b_1,b_2)\Rightarrow b_1=b_2.
\tag{44}
$$

**FORMALIZED.** `different_branches_not_composable` blocks the union of incompatible scenarios, assumption sets, or semantics. This prevents sceptical and credulous conclusions, or outcomes from different factual assumptions, from being silently merged.

### 7.2 Query gates

Queries distinguish entry, exclusion, and incompleteness. Relative to extension family \(\mathcal{E}\), define

$$
\operatorname{Common}(q,\mathcal{E})\iff
\forall E\in\mathcal{E},\operatorname{AcceptedIn}(q,E),
\tag{45}
$$

$$
\operatorname{Possible}(q,\mathcal{E})\iff
\exists E\in\mathcal{E},\operatorname{AcceptedIn}(q,E),
\tag{46}
$$

$$
\operatorname{UndecidedSome}(q,\mathcal{E})\iff
\exists E\in\mathcal{E},\neg\operatorname{AcceptedIn}(q,E)
\land\neg\operatorname{RefutedIn}(q,E).
\tag{47}
$$

**FORMALIZED.** Undecided status requires an enterable query, inconsistency requires both acceptance and refutation witnesses, and enterability has a positive witness. **DERIVED.** The gates prevent a missing query mapping from masquerading as a negative answer.

### 7.3 Procedure and adjudicative authority

ULM12 separates procedural status from merits findings. Procedure causes move a case between stages while preserving its normative marker. A valid adjudicative authority is bound to the exact request and contains a nonempty reviewer identity. Let \(A\Vdash_r x\) mean that authority \(A\) may issue finding \(x\) for request \(r\). Then

$$
A\Vdash_r x\Rightarrow A.request=r\land A.reviewer\ne\epsilon.
\tag{48}
$$

Adjudication returns one of four shapes:

$$
\operatorname{AdjudicateResult}=
\operatorname{adjudicated}\mid
\operatorname{procedural}\mid
\operatorname{pending}\mid
\operatorname{solverIncomplete}.
\tag{49}
$$

**FORMALIZED.** Procedural dispositions take precedence where the input is procedural. Burden success and burden failure create nonprocedural statuses only under validated authority. Incomplete evaluation remains `solverIncomplete`; absence of an extension without authority remains `pending`; neither equals `adjudicated`:

$$
\operatorname{pending}\ne\operatorname{adjudicated},\qquad
\operatorname{solverIncomplete}\ne\operatorname{adjudicated}.
\tag{50}
$$

**DERIVED.** The formal machine can constrain how an authorized finding is represented. It cannot manufacture the authorization or determine that a reviewer is legally competent under an external legal regime.

## 8. ULM13: Domain Composition and Exact Arithmetic

Domain outcomes may be combined only under a declared policy. If \(O\) is the set of domain outcomes and \(Allowed\subseteq\mathcal{P}(O)\), composition choices are nonempty allowed subsets:

$$
\operatorname{Choices}(O,Allowed)=
\{S\subseteq O\mid S\ne\varnothing\land S\in Allowed\}.
\tag{51}
$$

**FORMALIZED.** `compositionChoices_sound`, `choice_wf_selected_subset`, and `choice_wf_policy_bound` establish that generated choices are drawn from the available outcomes and remain within the declared policy and branch.

ULM13 also defines a typed exact-expression language. Dimensions include scalars, money indexed by currency, durations indexed by unit, and rates indexed by basis:

$$
d::=\operatorname{Scalar}\mid\operatorname{Money}(c)
\mid\operatorname{Duration}(u)\mid\operatorname{Rate}(b).
\tag{52}
$$

Expressions are indexed by dimension. Addition and subtraction require equal dimensions; scaling uses a rational scalar:

$$
e_1,e_2:\operatorname{Expr}(d)
\Rightarrow e_1+e_2:\operatorname{Expr}(d),
\tag{53}
$$

$$
q\in\mathbb{Q},\ e:\operatorname{Expr}(d)
\Rightarrow q\cdot e:\operatorname{Expr}(d).
\tag{54}
$$

The denotation is rational-valued and structural:

$$
\llbracket e_1+e_2\rrbracket_d=
\llbracket e_1\rrbracket_d+\llbracket e_2\rrbracket_d.
\tag{55}
$$

**FORMALIZED.** Evaluation equals denotation, and `executeExact` returns the computed rational as a complete outcome:

$$
\operatorname{eval}(e)=\llbracket e\rrbracket_d.
\tag{56}
$$

**DERIVED.** The result rules out floating-point rounding inside this expression language and prevents cross-currency or cross-duration-unit addition at the type level. **CONJECTURE.** It does not validate a statutory rate, select a legally correct accrual period, perform currency conversion, or establish a jurisdiction's rounding rule. Those are legal inputs and policy functions outside the interpreter theorem.

## 9. ULM14: Coverage, Trust, and Assurance Algebra

### 9.1 Coverage is not a Boolean shortcut

A coverage status stores open obligations and evidence for items classified as not applicable. Completeness is exact:

$$
\operatorname{IsComplete}(C)\iff C.open=\varnothing.
\tag{57}
$$

Aggregation unions both the unresolved and exemption evidence:

$$
(C_1\oplus C_2).open=C_1.open\cup C_2.open,
\tag{58}
$$

$$
(C_1\oplus C_2).exempt=C_1.exempt\cup C_2.exempt.
\tag{59}
$$

**FORMALIZED.** `incomplete_not_complete` ensures that a nonempty open set is not complete. The retention theorems ensure that composition does not erase either open obligations or not-applicable evidence from an input.

### 9.2 Trust is coordinatewise and non-upgrading

The trust vector has five coordinates:

$$
t=(t_{source},t_{text},t_{fact},t_{proof},t_{authority})
\in\{0,1,2\}^{5}.
\tag{60}
$$

Its meet is coordinatewise minimum:

$$
(a\wedge b)_i=\min(a_i,b_i).
\tag{61}
$$

**FORMALIZED.** `trust_meet_le_left` and `trust_meet_le_right` prove

$$
a\wedge b\le a,\qquad a\wedge b\le b.
\tag{62}
$$

**DERIVED.** A highly trusted proof cannot repair an untrusted source coordinate, and high source trust cannot substitute for authority. A scalar average would permit compensation; coordinatewise meet deliberately does not.

### 9.3 Assurance envelopes

An assurance envelope records scope, specification status, implementation assurance, run-check status, coverage, legal-input status, open specification references, trusted-computing-base assumptions, and notices. Composition takes weaker status coordinates and unions unresolved material. In schematic form,

$$
\operatorname{assure}(a\otimes b)=
\bigl(\min a.status\ b.status,\ a.open\cup b.open,\ a.notice\cup b.notice\bigr).
\tag{63}
$$

**FORMALIZED.** ULM14 proves that an open specification cannot become proved by combination, pending legal inputs remain pending, and notices and open references are retained. **DERIVED.** The algebra is designed against “assurance by aggregation,” in which several weak reports are rhetorically summed into a strong conclusion.

## 10. ULM15: Add-Only Refinement, Empirical Separation, and Banach Results

### 10.1 Monotone Horn extension

For Horn system \(H=(U,F,R)\), an add-only delta supplies \(\Delta F\subseteq U\) and new rules over the same universe. Extension is

$$
H\oplus\Delta=(U,F\cup\Delta F,R\cup\Delta R).
\tag{64}
$$

**FORMALIZED.** ULM15 proves one-step, iterate, and closure inclusion:

$$
T_H(S)\subseteq T_{H\oplus\Delta}(S),
\tag{65}
$$

$$
T_H^n(S)\subseteq T_{H\oplus\Delta}^n(S),
\tag{66}
$$

$$
\operatorname{Cl}_H\subseteq\operatorname{Cl}_{H\oplus\Delta}.
\tag{67}
$$

The `IncrementalImplementationCorrect` predicate defines correctness as equality with child full recomputation:

$$
\operatorname{IncCorrect}(I,H,\Delta)\iff
I(H,\Delta)=\operatorname{FullRecompute}(H\oplus\Delta).
\tag{68}
$$

**FORMALIZED.** If that predicate holds, the incremental result equals the reference and is fixed under the child operator. **CONJECTURE.** No theorem here proves that a particular production worklist satisfies Equation (68), nor that deletions preserve closure.

### 10.2 Empirical annotations remain read-only

An empirical artifact pairs normative solutions with a score. Attachment is observational:

$$
\operatorname{attachEmpirical}(S,q).normativeSolutions=S.
\tag{69}
$$

A deviation score is a rational weighted sum:

$$
D(w,x)=\sum_{i=0}^{n-1}w_i x_i.
\tag{70}
$$

**FORMALIZED.** `CORE_15_empirical_read_only` establishes that adding the score does not alter normative solutions, and `CORE_16_deviation_decomposition` records the sum's decomposition. **CONJECTURE.** The features and weights have not thereby been calibrated, validated, or granted legal authority.

### 10.3 Banach theorems and their exact premise

The Banach portion uses an arbitrary nonempty complete metric space and a contracting map, following the classical fixed-point theorem [@Banach1922]. For \(0\le q<1\), assume

$$
d(f(x),f(y))\le q\,d(x,y).
\tag{71}
$$

**FORMALIZED.** Under the encoded hypotheses, ULM15 proves existence and uniqueness of a fixed point, convergence of iterates, and an a priori error bound:

$$
\exists x^*,\ f(x^*)=x^*,
\tag{72}
$$

$$
f(x)=x\land f(y)=y\Rightarrow x=y,
\tag{73}
$$

$$
f^n(x)\longrightarrow x^*,
\tag{74}
$$

$$
d(f^n(x),x^*)\le\frac{q^n}{1-q}d(f(x),x).
\tag{75}
$$

The supporting weighted sup distance is

$$
d_w(x,y)=\max_i\frac{|x_i-y_i|}{w_i},\qquad w_i>0.
\tag{76}
$$

The core file proves nonnegativity, symmetry, triangle inequality, and separation for this expression. A coordinatewise Lipschitz premise plus a weighted coupling bound proves contraction. **CONJECTURE.** A theorem named `weightedSupDist_complete` in the historical core establishes nonnegativity and separation, not a `CompleteSpace` instance. The ULM15 Banach result instead assumes a genuinely complete metric space. No legal evaluator has been proved contracting merely because a weighted distance can be written down.

## 11. ULM16: Composition Without Global Overclaim

ULM16 names core and composition identifiers and instantiates a set of cross-module results. Its contribution is a checked spine through the preceding modules, not a claim that every declaration in the repository composes automatically.

The core chain can be summarized as

$$
\text{request}\to\text{typed transition}\to\text{premise provenance}
\to\text{Horn support}\to\text{argument}\to\text{defeat}
\to\text{extension}\to\text{query}\to\text{procedure}.
\tag{77}
$$

**FORMALIZED.** Named ULM16 results include typed-transition request preservation, admitted-premise status, support fixedness, generated-candidate soundness, well-formed defeat bridges, branch nonmixing, query-enterability requirements, procedural nonmanufacture, policy-bound domain choice, exact denotation, empirical read-only attachment, argument-coverage soundness, preferred-extension completeness, machine-subject preservation, nonempty required obligations, verifier soundness, and incomplete-not-adjudicated separation.

Four explicit composition laws are especially important:

$$
\operatorname{trust}(a\wedge b)\le\operatorname{trust}(a),
\quad
\operatorname{trust}(a\wedge b)\le\operatorname{trust}(b),
\tag{78}
$$

$$
\operatorname{observe}(g(f(x)))=\operatorname{observe}(x),
\tag{79}
$$

$$
\operatorname{Cl}_H\subseteq\operatorname{Cl}_{H\oplus\Delta},
\tag{80}
$$

$$
\operatorname{map}(f,\operatorname{Failure}(e))
=\operatorname{Failure}(e).
\tag{81}
$$

**DERIVED.** These laws yield a reusable design criterion: safe composition preserves identity, cannot increase trust, cannot retract add-only Horn consequences, and cannot convert failure by mere transport. **CONJECTURE.** They do not prove a single end-to-end refinement theorem from every Python input through every legal output.

## 12. Temporal, Authority, and Human-Receipt Constraints

The ULM spine is supplemented by core modules that constrain time and authority. In a Kripke structure (K), the encoded “always” operator requires the property at the current world and at each transitively reachable world:

$$
\Box_K\varphi(i)\iff
\varphi(i)\land\forall j\,(i\to_K^+j\Rightarrow\varphi(j)).
\tag{82}
$$

**FORMALIZED.** The temporal theorem proves the configured guard when the guard is assumed at every relevant world. **CONJECTURE.** It is not an induction theorem deriving future preservation from a single initial-state hypothesis.

Temporal applicability uses closed intervals and observation times. A source is effective at time (t) when

$$
\operatorname{effectiveAt}(s,t)\iff s.start\le t\land t\le s.end,
\tag{83}
$$

with the appropriate handling of optional endpoints. Observation is allowed only when

$$
t_{observed}\le t_{asOf}.
\tag{84}
$$

**FORMALIZED.** Future observations are blocked, and retracted or superseded sources are invalid under the encoded applicability predicate. **DERIVED.** This is temporal hygiene, not proof that the source text was correctly interpreted.

Receipt authority is ranked. For rank function \(\rho\), issuance is permitted only if

$$
\operatorname{canIssue}(a,k)\iff\rho(a)\ge\rho_{required}(k).
\tag{85}
$$

The authority lattice has finitely many ranks, and repeating receipts of the same level does not increase rank:

$$
\rho(\operatorname{consensus}(a,\ldots,a))\le\rho(a).
\tag{86}
$$

**FORMALIZED.** `AuthorityReceipt` records a subject, case scope, issuer, source level, and target level. Its current `receiptValid` predicate checks only that the target rank is exactly one greater than the source rank; it does not authenticate the recorded identity, scope, or issuer. Separate theorems show that repeated peer agreement cannot synthesize a higher authority level. `HumanResearchReceipt` records a task, input digest, reviewer, action, time window, and revocation flag; `receiptBindsTask` and `receiptCurrentlyValid` check only the corresponding field equalities and validity conditions:

$$
\operatorname{ValidHR}(r,t,d)\Rightarrow r.task=t\land r.digest=d
\land\neg r.revoked.
\tag{87}
$$

**FORMALIZED.** Given the binding predicate, the same receipt cannot be reused for a different task or input, and an expired or revoked receipt fails the current-validity predicate. **DERIVED.** These predicates establish record-level traceability inside the model. They do not prove external identity, institutional authorization, reviewer competence, or the truth of a human legal conclusion.

## 13. Release Assurance as a Subject-Bound Argument

### 13.1 Why a green job is insufficient

A release claim concerns a particular source object. Let the release evidence vector be

$$
\mathcal{E}_{rel}=
(sha,tree,run,modules,build,axioms,claims,mutation,receipts,certificate,verdict).
\tag{88}
$$

The binding invariant is

$$
\forall e\in\mathcal{E}_{rel},\quad e.subject.sha=sha
\land e.subject.tree=tree,
\tag{89}
$$

where fields that do not embed a tree directly must be linked through the same run identity. **DERIVED.** A passing job for a different SHA is irrelevant; a cancelled or timed-out run is not a pass; and a certificate copied from an earlier stage can conceal missing subject data unless final generation overwrites it.

The certificate status function is fail-closed:

$$
\operatorname{CertStatus}(E)=
\begin{cases}
\mathrm{BLOCKED}, & \operatorname{missing}(E)\ne\varnothing,\\
\mathrm{PENDING\_VERIFY}, & \operatorname{generated}(E)\land\neg\operatorname{verified}(E),\\
\mathrm{VERIFIED}, & \operatorname{verified}(E)\land\operatorname{consistent}(E).
\end{cases}
\tag{90}
$$

Generation and independent verification are different events. The verifier must agree with the certificate and must fail if required evidence is absent:

$$
\operatorname{ReleaseGate}(E)=1\Rightarrow
\operatorname{missing}(E)=\varnothing
\land\operatorname{verdict}(E)\notin\{\mathrm{FAILED},\mathrm{INCOMPLETE}\}.
\tag{91}
$$

### 13.2 Audited formal inventory

At the release subject recorded by the project, the full ULM axiom-audit module enumerates 145 theorem declarations and the core-composition audit enumerates 27. The emitted dependencies contain only

$$
\mathcal{A}_{allowed}=
\{\mathrm{propext},\mathrm{Classical.choice},\mathrm{Quot.sound}\}.
\tag{92}
$$

No project-defined axiom appears in that audited output. **FORMALIZED** refers here to the declarations accepted at that subject. **DERIVED.** The counts are inventory facts about the recorded subject, not timeless constants. Later commits must regenerate the manifest and audit.

The formal evidence relation can be written as

$$
\operatorname{FormalRelease}(s)\iff
\operatorname{MatrixPass}(s)\land
\operatorname{CleanBuildPass}(s)\land
\operatorname{AuditPass}(s)\land
\operatorname{GuardPass}(s).
\tag{93}
$$

The matrix checks module elaboration; the clean build checks integration from a cleared project build state; the guard scan detects forbidden proof escapes; the axiom audit inspects dependencies. None alone subsumes the others.

### 13.3 The content-level certificate record

The reported release snapshot binds subject SHA `2a1d33df353a005dffc5d8b95faa591524e2636e`, tree `c7525f767b43c7e8a663a4a9702f64cdea78b979`, and [GitHub Actions run `33946211096`](https://github.com/laubeing-droid/legal-math-modeling/actions/runs/33946211096). Its 97 jobs succeeded, including a 91-module matrix and a clean build reporting 2993 completed jobs. The run's named artifacts include `lean-full-build`, `python-gates`, and `release-certificate`; the content claims below refer to the JSON and logs inside those archives, not to the workflow colour. The certificate was generated with no missing CI evidence and moved through the staged content status `RELEASE_PASS_PENDING_INDEPENDENT_VERIFICATION`; the independent report recorded `VERIFIED_PENDING_RELEASE_GATE` with no errors, after which the final gate succeeded. **DERIVED.** The word “pending” in those two JSON statuses describes pipeline order, not an unresolved final conclusion, because the subsequent verifier and final-gate artifacts are present and bound to the same run. GitHub artifact retention is finite, so durable scholarly reproduction also requires depositing those run archives with the cited subject. These values are snapshot claims and must not be reused for another subject.

The acceptance predicate is therefore content-based:

$$
\operatorname{AcceptRelease}(E)\iff
E.subject.sha\ne\epsilon\land
E.missing=\varnothing\land
\operatorname{Consistent}(E.certificate,E.verifier)
\land\operatorname{FinalGatePass}(E).
\tag{94}
$$

**DERIVED.** A green workflow icon is neither necessary evidence by itself nor sufficient evidence for Equation (94). The JSON fields, logs, and bindings carry the claim.

## 14. Real Mutation Evidence and Cross-Repository Refinement Receipts

### 14.1 Mutation as a boundary test

The mutation gate starts from a passing baseline and applies controlled malformed transformations to certificate or checker inputs. Let \(C\) be a valid fixture, \(M=\{m_1,\ldots,m_n\}\) the selected mutations, and \(V\) the independent checker. A mutation is killed when

$$
\operatorname{Killed}(m_i)\iff V(m_i(C))=\operatorname{reject}.
\tag{95}
$$

The property score is

$$
\operatorname{MS}(M,C,V)=
\frac{|\{m\in M\mid\operatorname{Killed}(m)\}|}{|M|}.
\tag{96}
$$

At the reported subject, 46 of 46 controlled mutations were rejected, so the observed score for that fixture set was

$$
\operatorname{MS}=46/46=1.
\tag{97}
$$

**DERIVED.** This demonstrates that the exercised certificate/checker boundary detected the selected missing, altered, inconsistent, or malformed evidence properties. It is not Lean-source mutation coverage, Python implementation mutation coverage, path coverage, or a proof that all adversarial transformations will be rejected. Calling it “100% mutation testing” without naming the denominator would be false.

The mutation gate adds evidence because ordinary positive tests can share the same mistake as the producer. The controlled negative fixtures ask whether the consumer rejects states that the release contract forbids. Still, the conclusion remains finite:

$$
\bigl(\forall m\in M,\ V(m(C))=\operatorname{reject}\bigr)
\not\Rightarrow
\forall x\notin\operatorname{Valid},\ V(x)=\operatorname{reject}.
\tag{98}
$$

### 14.2 Runtime refinement receipts

A cross-repository receipt connects the model subject to an independently versioned runtime. Abstractly,

$$
r=(sha_{LMM},sha_{JC},build,fixture,inputDigest,outputDigest,status).
\tag{99}
$$

Receipt validity requires exact bindings and an accepted status:

$$
\operatorname{ReceiptValid}(r)\iff
r.sha_{LMM}=s_L\land r.sha_{JC}=s_J\land
\operatorname{DigestMatch}(r)\land r.status=\mathrm{PASS}.
\tag{100}
$$

The cross-repository gate consumed real receipts produced by `juris-calculus`, rather than locally fabricating a report in the model repository. At the reported release, three executable refinement fixtures passed and bound the LMM subject to the JC runtime subject identified in the release evidence (short prefix `c79e03b`) and build identifier `github-actions:33946211096:1`. **DERIVED.** The receipts establish traceability and agreement for those three fixture executions.

They do not prove universal refinement:

$$
\forall f\in F_{tested},\ I(f)=S(f)
\not\Rightarrow
\forall x\in Input,\ I(x)=S(x).
\tag{101}
$$

Here (I) is the runtime implementation and (S) is the specification-side expected behavior. Equation (101) is the central receipt boundary. A true refinement theorem would quantify over a defined input domain and relate all relevant states, traces, failures, and outputs. The current receipts are executable witnesses over a small, named set.

### 14.3 Independent verification and evidence non-substitution

Mutation and receipt evidence are useful because they test bridge machinery that Lean does not execute. Their authority is nevertheless constrained:

$$
\operatorname{KernelProof}\oplus\operatorname{MutationPass}
\oplus\operatorname{ReceiptPass}
\not=\operatorname{LegalCorrectness}.
\tag{102}
$$

**DERIVED.** The left side supplies a stronger engineering assurance case than any component alone. It validates theorem elaboration, selected checker failures, and selected cross-runtime observations. Legal correctness still depends on source selection, interpretation, jurisdiction, time, procedural posture, and authorized judgment.

## 15. An End-to-End Worked Assurance Trace

Consider a hypothetical request (r) asking whether a claim enters an argumentation analysis under a specified body of source material. The example is schematic and carries no jurisdictional legal conclusion.

First, a context key and request key are created and checked:

$$
r.context.runScope.caseScope=r.context.caseScope.
\tag{103}
$$

Second, evidence tokens are admitted or marked as assumptions. Suppose premise (p_1) is admitted and (p_2) depends on assumption (a_7):

$$
\operatorname{deps}(p_1)=\varnothing,
\qquad
\operatorname{deps}(p_2)=\{a_7\}.
\tag{104}
$$

Third, Horn closure derives candidate support within the finite universe:

$$
S=\operatorname{Cl}_H(F_0),\qquad
\operatorname{support}(c)\subseteq S.
\tag{105}
$$

Fourth, argument construction requires non-dangling, available, acyclic support. Attacks are admitted only with witnesses and same-request identity. The policy-resolved defeat framework is then

$$
AF_r=(A_r,\operatorname{Defeat}_{\pi_r}).
\tag{106}
$$

Fifth, a selected semantics yields an extension family. Under grounded semantics,

$$
\mathcal{E}_r=\{\Gamma_{AF_r}^{|A_r|}(\varnothing)\}.
\tag{107}
$$

Under preferred semantics the family may contain several extensions; under stable semantics it may be empty. Query output must therefore preserve the semantic profile and branch key.

Sixth, assume the query is accepted in one preferred extension and not accepted in another. The correct query statement is possible acceptance, not common acceptance:

$$
\operatorname{Possible}(q,\mathcal{E}_r)=\top,
\qquad
\operatorname{Common}(q,\mathcal{E}_r)=\bot.
\tag{108}
$$

Seventh, a solver timeout leaves a nonempty obligation set (O). The result must be partial or `solverIncomplete`:

$$
O\ne\varnothing\Rightarrow
\operatorname{result}\ne\operatorname{adjudicated}.
\tag{109}
$$

Eighth, if an exact arithmetic expression is needed, its dimension is fixed before evaluation. A monetary amount in currency (c) cannot be added to duration (u):

$$
\operatorname{Money}(c)\ne\operatorname{Duration}(u).
\tag{110}
$$

Ninth, the ULM procedure authority object attaches a finding to an exact request under `AdjudicationAuthority.ValidFor`, while the separate human-research receipt predicates bind a task and input digest. Neither predicate authenticates its recorded reviewer. The formal output remains conditional on those distinct records and their premises. Finally, release evidence for the software subject is checked independently of the hypothetical case:

$$
\operatorname{CaseResult}(r)\land\operatorname{ReleaseAccepted}(s)
\not\Rightarrow\operatorname{LegallyCorrect}(r).
\tag{111}
$$

**FORMALIZED.** Each local equality or nonconversion used above corresponds to ULM declarations under their precise hypotheses. **DERIVED.** Their composition yields a trace in which identity, provenance, semantic profile, open obligations, and authority remain visible. **CONJECTURE.** Whether the source set and policy correctly state applicable law is intentionally unanswered.

## 16. Countermodels and Explicit Non-Results

### 16.1 Probability is not encoded by trust levels

The three-valued trust coordinates are ordered labels, not probabilities. In general,

$$
t_i\in\{0,1,2\}\not\Rightarrow
\exists p_i\in[0,1]\text{ with }t_i=p_i.
\tag{112}
$$

Even if a calibration map \(\kappa:\{0,1,2\}\to[0,1]\) were proposed, posterior inference would require a probabilistic model, dependence assumptions, and data. **CONJECTURE.** Bayesian legal models could be connected to evidence tokens, but no such bridge is formalized. The existing trust meet must not be described as probability aggregation.

### 16.2 Differential privacy is not a property of evidence omission

Differential privacy requires a neighboring relation \(\sim\), a randomized mechanism \(M\), and a quantified inequality [@DworkEtAl2006; @DworkRoth2014]:

$$
\Pr[M(D)\in S]\le e^\varepsilon\Pr[M(D')\in S]+\delta
\quad\text{for all }D\sim D'.
\tag{113}
$$

The ULM core defines none of the required probability space, adjacency relation, sensitivity, privacy budget, or randomized mechanism. **CONJECTURE.** A future privacy layer would need all of them plus composition and authority rules. Redaction, digest binding, or absence of raw customer data does not prove Equation (113).

### 16.3 Graph similarity is not a metric by naming

A graph similarity (s(G,H)) becomes a distance only if a transformation such as (d=1-s) satisfies nonnegativity, identity of indiscernibles, symmetry, and triangle inequality:

$$
d(G,H)\ge0,\quad d(G,H)=0\iff G=H,\quad
d(G,H)=d(H,G),\quad
d(G,K)\le d(G,H)+d(H,K).
\tag{114}
$$

Common overlap scores can assign zero distance to distinct graphs after lossy feature extraction or violate the triangle inequality. **CONJECTURE.** No ULM theorem establishes a graph metric or positive-semidefinite kernel. Argument-framework identity and support coverage should not be confused with similarity topology.

### 16.4 Analogical strength and explanation quality remain empirical or normative

Case-based reasoning may score similarity between a source case and target case [@RisslandAshley1987]. A generic weighted score

$$
S(x,y)=\sum_i w_i\phi_i(x,y)
\tag{115}
$$

does not prove that the selected dimensions are legally relevant, that the weights are calibrated, or that a higher score warrants the same outcome. **CONJECTURE.** Analogical strength needs a domain-specific semantics and evaluation design.

Explanation generation faces a parallel issue. Fidelity to an executable decision function can be expressed as

$$
\operatorname{Fid}(e,f;N)=
\Pr_{x\sim N}[e(x)=f(x)],
\tag{116}
$$

but legal adequacy also concerns reasons, sources, counterarguments, and reviewability [@Lipton2018; @GuidottiEtAl2018; @WachterEtAl2018]. **CONJECTURE.** The current proof traces and provenance fields can support explanation, but no Lean theorem establishes human comprehensibility or legal sufficiency.

### 16.5 Liability is not a function computed by the formal core

European regulation and product-liability reforms create obligations and allocation questions that depend on actor roles, defects, causation, damage, defenses, and temporal application [@EU2024AIAct; @EU2024ProductLiability; @Hacker2023; @BuitenEtAl2021]. The tempting formula

$$
\operatorname{Liable}(a)=
f(\operatorname{role}(a),\operatorname{fault}(a),\operatorname{cause}(a),\operatorname{damage})
\tag{117}
$$

is merely schematic. **CONJECTURE.** No ULM theorem decides substantive liability. The architecture can record authority, provenance, procedure, and open obligations relevant to an analysis, but the legal judgment must be supplied under a jurisdiction- and time-specific rule set.

## 17. Evidence Ledger

The following ledger maps paper claims to stable source modules. Line numbers are included for the current source snapshot and must be refreshed after edits.

| Evidence class | Paper claim | Source anchor | Exact boundary |
|---|---|---|---|
| FORMALIZED | Observation preservation composes | `ULM01NormalForm.lean:138`, `preserves_comp` | Only the selected observation |
| FORMALIZED | Failure and partial outcomes do not become complete by mapping | `ULM02Outcome.lean:58–68` | No claim about arbitrary exception handlers |
| FORMALIZED | Local transitions preserve request and use declared edges | `ULM03TypedGraph.lean:69–74` | Node payload dependency remains open |
| FORMALIZED | Required obligations are nonempty; sound satisfaction entails the goal | `ULM04Obligations.lean:60–99` | Executable verifier soundness is a premise |
| FORMALIZED | Steps and runs preserve request; applied edges are not re-enabled | `ULM05Machine.lean:66–87` | Scheduling fairness not proved |
| FORMALIZED | Premise origins and dependencies remain explicit | `ULM06FactEvidence.lean:108–115` and adjacent declarations | Admission does not prove factual truth |
| FORMALIZED | Horn support closure is fixed, least, and request-bound | `ULM07HornSupport.lean:17–61` | Relative to finite encoded rules |
| FORMALIZED | Coverage checker is sound and complete for frozen expected arguments | `ULM08ArgumentConstruction.lean:83–107` | Not general generator completeness |
| FORMALIZED | Defeats come from well-formed attacks and preserve request | `ULM09AttackDefeat.lean:46–121` | Policy legality not proved |
| FORMALIZED | Grounded fixed point and finite extension enumerators | `ULM10DungProfiles.lean:91–255` | Stable existence not guaranteed |
| FORMALIZED | Branch nonmixing and witness-based query gates | `ULM11BranchQuery.lean:115–220` | No cross-profile aggregation |
| FORMALIZED | Pending and incomplete are not adjudicated | `ULM12Procedure.lean:228–256` | Authority must be supplied |
| FORMALIZED | Policy-bounded choices and exact rational denotation | `ULM13DomainCompositionExact.lean:46–151` | Statutory inputs not validated |
| FORMALIZED | Trust meet is non-upgrading; unresolved evidence is retained | `ULM14CoverageTrust.lean:57–301` | Ordinal trust is not probability |
| FORMALIZED | Add-only closure inclusion and generic Banach consequences | `ULM15IncrementalEmpiricalBanach.lean:37–146` | Runtime worklist and legal contraction open |
| FORMALIZED | Named core and composition instances | `ULM16TheoryComposition.lean:75–262` | Not a universal end-to-end refinement theorem |
| DERIVED | 145 full-audit and 27 core-audit declarations; no custom axiom | `ULMAllTheoremsAxiomAudit.lean`, `ULMCoreCompAxiomAudit.lean`, subject-bound CI artifacts | Counts are snapshot-specific |
| DERIVED | Controlled mutation fixtures rejected 46/46 | `mutation-property-report.json` in the recorded release artifacts | Certificate/checker boundary only |
| DERIVED | Three cross-repository fixtures passed with bound receipts | `runtime-refinement-report.json` and external receipts in the recorded release artifacts | Finite fixture agreement only |
| CONJECTURE | Probability, DP, graph metric, analogy, explanation quality, liability | No closing ULM theorem | Requires new models, evidence, and authority |

This ledger is part of the argument, not a decorative appendix. It provides a direct test for narrative drift: if a statement cannot be assigned a row with an adequate boundary, its label must be downgraded or the statement removed.

## 18. Discussion

### 18.1 What composition achieves

The strongest contribution is negative in form but constructive in effect: evidence cannot silently cross a boundary. Request preservation stops artifacts from different runs being merged. Branch keys stop semantic profiles and assumptions being collapsed. Fail-closed outcomes stop timeouts and open obligations being reported as adjudications. Trust meet and assurance composition stop weak inputs being upgraded by aggregation. Authority receipts stop repeated low-rank confirmations being presented as a higher-rank act. Release bindings stop evidence from one commit certifying another.

These controls support a precise compositional claim. Let \(f_1,\ldots,f_n\) be stages with local contracts \(C_i\). A global contract follows only when adjacent postconditions and preconditions match and all shared observations agree:

$$
\operatorname{Global}(f_n\circ\cdots\circ f_1)
\Leftarrow
\bigwedge_{i=1}^{n} C_i
\land\bigwedge_{i=1}^{n-1}\operatorname{Compatible}(post_i,pre_{i+1})
\land\operatorname{SameSubject}.
\tag{118}
$$

**DERIVED.** The ULM modules instantiate many (C_i), but Equation (118) also explains why the paper does not claim complete system verification. Several runtime-to-formal and legal-authority compatibility premises remain external.

### 18.2 Why bounded claims are practically stronger

An expansive claim such as “the legal AI is formally verified” is difficult to falsify because its subject is unspecified. A bounded claim names a theorem, input type, request key, subject SHA, evidence artifact, and excluded inference. It can fail. That is an advantage.

The release pipeline makes failure informative. If identity evidence is absent, the certificate lists it as missing. If a mutation survives, the property report names it. If a receipt is structurally valid but results differ, the refinement verdict is inconclusive rather than cosmetically green. Historical receipt bundles in the repository demonstrate this behavior: structurally valid evidence may expose divergence instead of supporting agreement. **DERIVED.** A fail-closed record is useful even when it blocks release because it locates the unsupported bridge.

### 18.3 Relationship to legal judgment

The architecture does not remove the human legal role. It narrows the human task by preserving the materials that must be judged: sources, time, assumptions, semantic branch, unresolved obligations, and authority. A reviewer can see whether a conclusion is common or merely possible, whether a premise is admitted or assumed, and whether a procedure ended in adjudication or incompleteness.

The division of labor is

$$
\mathrm{LLM\ proposes}\to
\mathrm{typed\ candidate}\to
\mathrm{formal/runtime\ gates}\to
\mathrm{authorized\ legal\ judgment}.
\tag{119}
$$

**DERIVED.** Verification gates may reject malformed or unsupported candidate material. **CONJECTURE.** They cannot decide the legally correct source interpretation unless that interpretation has itself been encoded under accountable authority.

## 19. Limitations and Threats to Validity

The formal results are model-relative. Finite Horn completeness is completeness for the encoded rule system. Argument coverage is equality with a supplied expected carrier. Dung results concern a finite framework after attack resolution. Procedure results assume validated authority objects. Exact arithmetic proves interpreter correctness for typed rational expressions, not correctness of statutory parameters. Banach results assume completeness and contraction rather than proving those properties for a legal evaluator.

The audit has a subject boundary. The figures 145 and 27, the allowed-axiom set, matrix size, build count, Python test count, mutation count, and receipt count belong to one recorded release subject. They may become stale after any source, workflow, dependency, fixture, or verifier change. A later paper version should regenerate them from the new release evidence instead of editing the prose alone.

Mutation validity is limited by operator selection. The 46 killed fixtures show that the checker rejects 46 selected malformed states. They do not estimate an unknown population of all bugs and should not be interpreted as a statistical confidence interval. A producer and checker may still share an unmutated misconception.

Receipt validity is limited by fixture representativeness. Three passing cross-repository fixtures prove three passing executions with bindings. They do not cover every canonical input, failure state, performance condition, dependency version, or adversarial serialization. A universal runtime refinement theorem remains open.

The legal-content boundary is the largest limitation. The corpus does not prove jurisdiction-wide coverage, authoritative source selection, correct interpretation of ambiguous provisions, evidential admissibility, calibrated proof standards, or institutional competence. No private customer data or production benchmark is evaluated here. The paper makes no empirical performance claim about real cases.

There is also a presentation risk. Mathematical notation can create unwarranted confidence even when every proposition is qualified. The three evidence labels and the ledger reduce this risk but cannot eliminate inattentive reading. The decisive sources remain the Lean declarations and subject-bound artifacts, not the paper's rhetoric.

## 20. Reproducibility and Failure Recovery

Reproduction should start from the recorded subject rather than the repository's moving default branch. A reproducer must inspect the subject SHA and tree, theorem manifest, module matrix, clean-build log, axiom output, guard report, claim audit, mutation report, cross-repository receipts, certificate JSON, and independent-verifier JSON. Local Lean execution is not treated as authority in this project; the CI workflow bound to the subject is the authoritative elaboration environment.

The minimum acceptance relation is

$$
\operatorname{Reproduced}(s)\iff
\operatorname{Checkout}(s)\land
\operatorname{AllRequiredArtifacts}(s)\land
\operatorname{ContentChecksPass}(s).
\tag{120}
$$

A workflow status alone does not satisfy `ContentChecksPass`. Reviewers should confirm that `subject.sha` is nonempty, `missing_ci_evidence` is empty or explicitly accepted as a downgrade, the axiom output contains only allowed dependencies, the verifier agrees with the certificate, and the run head equals the claimed subject.

Failure recovery follows the failed layer. A Lean elaboration failure requires repairing imports, types, or proofs without weakening the theorem. A certificate failure requires repairing evidence generation or ordering, not suppressing the exit code. A surviving mutation requires either strengthening the checker or narrowing the claimed property. A receipt mismatch requires preserving the mismatch and diagnosing the formal/runtime bridge. A missing legal authority requires a pending or incomplete disposition, not a synthetic authorization object.

## 21. Conclusion

**FORMALIZED.** ULM01–ULM16 establish a connected family of results about identity-preserving transitions, fail-closed outcomes, finite Horn closure, canonical support, policy-resolved defeat, Dung extension semantics, branch-sensitive queries, procedural nonmanufacture, typed exact arithmetic, non-upgrading trust, add-only refinement, generic contraction results, and selected cross-module compositions. At the audited subject, 145 declarations in the full ULM audit and 27 in the core-composition audit have no project-defined axiom dependency.

**DERIVED.** A release certificate becomes meaningful when its content binds the source subject and when independent checks inspect missing evidence, axiom output, mutations, receipts, and verifier agreement. Forty-six killed certificate/checker mutations and three passing cross-repository refinement fixtures strengthen the engineering case for the recorded subject. Their denominators remain explicit.

**CONJECTURE.** The architecture may support later work on probabilistic evidence, privacy, graph embeddings, analogical strength, explanations, and liability analysis. None of those topics is already proved merely because it can be expressed in mathematical notation. Their admission requires new types, hypotheses, bridge theorems, fixtures, empirical evaluation, and legal authority.

The resulting position is deliberately modest and operationally demanding. Formal proof decides propositions inside the model. Runtime evidence checks selected bridges. Release certificates bind claims to artifacts. Authorized people remain responsible for law. Keeping those functions separate is not a retreat from legal automation; it is the condition under which formal results can be used without being misrepresented.

## Declarations

### Funding

This research received no external funding.

### Conflict of Interest

The author declares no conflict of interest.

### Data Availability

No personal, confidential, customer, or case-level research data were used. The formal source, scripts, schemas, documentation, and subject-bound release artifacts discussed in the paper are contained in or linked from the `legal-math-modeling` repository. Availability of a repository artifact does not enlarge its evidentiary scope.

### Ethics

The study did not involve human participants, intervention, private legal files, or personal data. The worked trace is schematic and carries no legal advice or jurisdiction-specific holding. Human authorization remains outside the formal kernel and is represented only as a bounded input condition.

### Author Contributions (CRediT)

Laupinco: Conceptualization, Methodology, Software, Formal Analysis, Validation, Investigation, Resources, Data Curation, Writing – Original Draft, Writing – Review and Editing, Supervision, and Project Administration. Laupinco is the sole author.

### AI Disclosure

Generative AI assisted with language drafting, structural revision, and consistency checks for this manuscript. The author determined the research questions, formal scope, evidence policy, theorem selection, interpretations, and final claims. AI output was not treated as proof, legal authority, empirical data, or an independent citation source. The controlling evidence remains the cited literature, Lean source, and subject-bound release artifacts.

## References

Bibliographic records for all citations are maintained in `paper/references.bib`. Citations in this manuscript use Pandoc citation keys and introduce no key outside that bibliography.
