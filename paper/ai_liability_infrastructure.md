# Liability Infrastructure for Verifiable Legal AI

**Author:** Laupinco

## Abstract

Artificial-intelligence liability is often discussed as if a court needed only to select a liable actor after an automated system caused harm. That view is too narrow for systems assembled from models, data, deployers, interfaces, and post-deployment updates. This paper develops a mathematical infrastructure for recording the conditions from which a legally authorized decision-maker may later reason about responsibility. It separates ex ante regulatory duties under the European Union Artificial Intelligence Act from ex post compensation under the 2024 Product Liability Directive. The model represents an AI supply chain as a typed graph, assigns time-indexed duties to actors, records causal and evidential links without converting them into legal conclusions, and defines a release certificate that states exactly which technical claims were checked. Ten principal equations specify actor-role incidence, duty activation, trace propagation, causal contribution, evidential sufficiency, defect hypotheses, damage allocation, recourse, temporal compliance, and certificate closure. These equations are analytical proposals, not statements of European law and not Lean theorems. The repository's formal kernel may establish structural invariants for selected data types and transformations, but it does not prove defect, causation, fault, damages, or the legally correct allocation of responsibility in any case. The resulting architecture therefore follows a strict division of labour: software preserves provenance and checks formal invariants; legal authorities supply governing norms and evaluate facts; courts or other competent institutions make dispositive judgments. The model is useful as auditable infrastructure precisely because it refuses to collapse those layers.

## 中文摘要

本文提出一套面向可验证法律人工智能的责任基础设施。模型不把“系统输出错误”直接等同于产品缺陷、过错、因果关系或赔偿责任，而是把供应链主体、法定义务、版本、更新、技术事件、证据来源与损害主张分别建模。现行欧盟《人工智能法》被作为事前风险治理基线，2024 年新版《产品责任指令》被作为产品缺陷与损害赔偿的事后制度基线。本文给出的主体—角色矩阵、义务激活函数、因果贡献、证据充分性、损害分配与追偿公式均属于分析性推导或待检验模型，并非欧盟法的数学替代物，也没有获得 Lean 证明。形式化内核只能证明被编码结构的有限性质；具体案件中的事实认定、法律解释和责任裁判仍由有权限的人类机构完成。

**Keywords:** AI liability; product liability; AI Act; provenance; causal contribution; formal verification; release certificate

**关键词：** 人工智能责任；产品责任；人工智能法；来源追踪；因果贡献；形式验证；发布证书

## 1. Research Questions and Claim Discipline

This paper asks four questions. First, what minimum information must an AI system retain so that a later liability inquiry is not defeated by a missing model version, undocumented update, or ambiguous role assignment? Second, how can ex ante compliance and ex post liability be related without treating compliance as immunity or non-compliance as automatic causation? Third, which parts of that infrastructure are amenable to machine checking? Fourth, where must the model stop and defer to legally authorized judgment?

Every substantive proposition is marked with one of three labels. **FORMALIZED** means that a proposition is represented and proved in the repository's Lean sources for the stated types and assumptions. **DERIVED** means that the proposition follows mathematically from definitions introduced in this paper but is not represented as a proved Lean theorem. **CONJECTURE** means that the proposition is a design hypothesis or empirical claim requiring validation. These labels concern epistemic status, not rhetorical confidence.

**DERIVED.** Liability infrastructure should be modeled as an evidence-preserving relation among actors, artifacts, events, duties, and claims, rather than as a function that emits a liable party. If a program returns a party name, the output is at most a candidate conclusion accompanied by premises and provenance.

**DERIVED.** The operative European baseline is dual. Regulation (EU) 2024/1689 establishes harmonized rules and risk-management obligations for AI systems, while Directive (EU) 2024/2853 modernizes liability for defective products, including software-related products and components [@EU2024AIAct; @EU2024ProductLiability]. The two instruments have different objects, addressees, triggers, and consequences. Their joint relevance does not merge them into one liability calculus.

**CONJECTURE.** A supply-chain evidence graph that is complete at release time and maintained across substantial updates will reduce avoidable uncertainty about attribution. The conjecture is testable through incident reconstruction studies; it is not established merely because the graph has a mathematically tidy schema.

## 2. Related Work

**DERIVED.** Scholarship on AI liability identifies opacity, distributed control, autonomy, and changing software as pressures on conventional fault and product-liability analysis. Hacker criticizes gaps and compromises in proposed European liability responses, while Buiten, de Streel, and Peitz analyze incentives and the allocation of AI-related accident costs [@Hacker2023; @BuitenEtAl2021]. These sources motivate an infrastructure capable of distinguishing producers, deployers, component suppliers, operators, and affected persons.

**DERIVED.** Explainability research supplies techniques for local prediction explanations and counterfactual statements, but an explanation is not itself proof of legal causation. LIME explains a classifier near an input; counterfactual explanations identify changes associated with a different output; surveys classify families of explanation methods [@RibeiroEtAl2016; @WachterEtAl2018; @GuidottiEtAl2018]. Lipton's critique is especially relevant: interpretability is not a single measurable property and may conceal incompatible desiderata [@Lipton2018]. Liability infrastructure must therefore record what an explanation method establishes, and what it does not.

**DERIVED.** Formal verification offers a different kind of assurance. Hoare logic relates programs to preconditions and postconditions, and Lean checks proof terms in a small trusted kernel [@Hoare1969; @DeMouraUllrich2021]. Such methods can establish that a transformation preserves an encoded invariant. They cannot establish that the encoded rule is the governing law, that testimony is credible, or that a causal standard is satisfied unless those matters have first been supplied as assumptions.

**DERIVED.** Nonmonotonic and argumentation research explains why legal conclusions may change when exceptions, priorities, or counterarguments appear [@Reiter1980; @Dung1995; @PrakkenSartor1997]. This supports representing a liability claim as defeasible and contestable. It does not license treating an abstract argumentation extension as a judgment.

## 3. Normative Baseline Without Normative Substitution

**DERIVED.** The AI Act operates primarily through ex ante classifications and obligations. A system may be prohibited, high-risk, transparency-regulated, or outside a particular obligation, depending on facts and definitions in the Regulation [@EU2024AIAct]. A technical system may assist by retaining classification inputs, conformity records, instructions, monitoring events, and update histories. It must not silently decide contested statutory interpretation.

**DERIVED.** The Product Liability Directive operates through an ex post structure involving a product, defectiveness, damage, causation, responsible economic operators, defenses, disclosure, and national implementation [@EU2024ProductLiability]. Software can be within the product framework, and post-market control and updates can matter. Yet “software caused a surprising output” is not identical to “a product was defective” under the Directive.

**DERIVED.** Compliance and liability are related but non-equivalent predicates. Let (C(x,t)) mean that artifact (x) satisfies the set of applicable recorded compliance checks at time (t), and let (L(x,h,t)) mean that legal liability for harm (h) is established under the governing law. The infrastructure adopts no implication in either direction:

\[
C(x,t) \not\Rightarrow \neg L(x,h,t),
\qquad
\neg C(x,t) \not\Rightarrow L(x,h,t).
\tag{1}
\]

Equation (1) is a boundary rule. Compliance may be relevant evidence, and a breach may support an argument, but intervening legal elements remain necessary.

**DERIVED.** Likewise, a certificate for a software release concerns a specified build and evidence bundle, not legal approval:

\[
\operatorname{Cert}(r)=\operatorname{Pass}
\not\Rightarrow
\operatorname{LawfulUse}(r,u,j,t).
\tag{2}
\]

The right-hand predicate depends on on use (u), jurisdiction (j), time (t), and facts not exhausted by release testing.

## 4. Typed Supply-Chain Model

Let (A) be actors, (R) legally or operationally relevant roles, (X) artifacts, (V) versions, (E) events, (D) duties, (H) alleged harms, (N) norms, and (T) time. Artifacts include models, training or evaluation data, source modules, configuration, prompts, interfaces, documentation, and generated outputs. Events include release, deployment, update, override, alert, incident, and retirement.

**DERIVED.** Role membership is time-indexed because an actor can acquire or lose control. Define the incidence tensor

\[
\rho:A\times R\times X\times T\rightarrow\{0,1\},
\qquad
\rho(a,r,x,t)=1
\iff a\text{ occupies role }r\text{ for }x\text{ at }t.
\tag{3}
\]

No role name is inferred solely from a repository username. Its value must be supported by contracts, technical control, statutory definitions, or other admissible sources.

**DERIVED.** An applicability function separates a norm from a duty instance:

\[
\alpha:N\times A\times X\times T\times F\rightarrow\{0,1,?\},
\tag{4}
\]

where $F$ is a fact assignment and $?$ denotes unresolved applicability. A duty instance exists only after an authorized interpretation supplies $\alpha=1$. The infrastructure must preserve $?$; it may not coerce unknown to false or true.

**DERIVED.** Active duties are then

\[
D_t(a,x)=\{d\in D\mid \exists n\in N:\alpha(n,a,x,t,F)=1
\land \operatorname{grounds}(n,d)\}.
\tag{5}
\]

Equation (5) enables traceability from an obligation record back to its asserted legal source. It does not decide whether the interpretation of that source is correct.

**DERIVED.** Artifact provenance is a directed acyclic multigraph \(G_P=(X\times V,E_P)\). An edge \(p\xrightarrow{k}q\) means that versioned artifact \(q\) depends on \(p\) through relation \(k\), such as compilation, fine-tuning, configuration, retrieval, or human approval. For a released artifact \(q\), its trace closure is

\[
\operatorname{Trace}(q)=\mu Z.\bigl(\{q\}\cup
\{p\mid \exists z\in Z,\exists k:(p\xrightarrow{k}z)\in E_P\}\bigr).
\tag{6}
\]

The least-fixed-point notation is justified by monotonicity of the predecessor operator on the powerset lattice [@Tarski1955]. It produces a finite dependency closure when the recorded graph is finite.

**FORMALIZED.** The repository contains selected formal structures and invariants for its legal-modeling modules. This statement is limited to the theorem inventory and source-bound release evidence. It does not imply that Equation (6), EU-law classifications, or the liability functions below are implemented and proved in Lean.

## 5. Events, Control, and Causal Contribution

**DERIVED.** Each event record is a tuple

\[
e=(\tau, a, x_v, \operatorname{kind}, i, o, s),
\tag{7}
\]

where \(\tau\) is time, \(a\) the initiating or recording actor, \(x_v\) the versioned artifact, \(i\) and \(o\) input and output references, and \(s\) a source reference. Source references point to retained evidence; they are not truth labels.

**CONJECTURE.** Causal contribution can be screened with an intervention model before legal evaluation. Let (Y) denote a harm-relevant outcome and (Z_x) the state of component (x). Define a technical contribution score

\[
\kappa_x(h)=
\mathbb{E}[Y_h\mid do(Z_x=z_x)]-
\mathbb{E}[Y_h\mid do(Z_x=z_x^{\star})].
\tag{8}
\]

The baseline $z_x^{\star}$, causal graph, estimand, and data all require justification. A nonzero $\kappa_x$ does not establish legal causation; it identifies a model-dependent difference for investigation.

**CONJECTURE.** Distributed systems also require interaction terms. For components (x) and (y), define

\[
\iota_{xy}(h)=\kappa_{xy}(h)-\kappa_x(h)-\kappa_y(h).
\tag{9}
\]

Positive or negative interaction warns against allocating all contribution to a single component. The score remains descriptive and depends on the selected counterfactual model.

**DERIVED.** Technical control can be represented separately from causal contribution:

\[
\gamma(a,x,t)=
w_1\operatorname{Modify}+w_2\operatorname{Deploy}
+w_3\operatorname{Monitor}+w_4\operatorname{Disable},
\quad \sum_i w_i=1.
\tag{10}
\]

The features are binary or graded records of actual capability. The weights are policy parameters, not facts. Control evidence may inform role classification or recourse, but Equation (10) is not a legal test.

## 6. Evidence Sufficiency and Contestability

Let a claim (c) have supporting items (S_c), opposing items (O_c), and unresolved challenges (U_c). Every item has provenance, acquisition time, version, and status. “Verified” means checked by a named procedure against a source, not substantively accepted by a court.

**DERIVED.** A non-dispositive completeness measure is

\[
Q(c)=
\frac{\sum_{e\in S_c}q(e)-\sum_{e\in O_c}q(e)}
{1+\sum_{e\in S_c\cup O_c\cup U_c}|q(e)|},
\qquad -1<Q(c)<1.
\tag{11}
\]

The denominator prevents a large unnormalized file count from masquerading as certainty. Duplicate or derivative artifacts must share an evidence family so that repeated copies do not multiply weight.

**DERIVED.** A claim is procedurally ready for human review only if mandatory fields are present and blocking contradictions are exposed:

\[
\operatorname{Ready}(c)=
\operatorname{CompleteFields}(c)\land
\operatorname{SourceBound}(c)\land
\neg\operatorname{HiddenConflict}(c).
\tag{12}
\]

Readiness is not truth, admissibility, or legal sufficiency. It means that the reviewing authority receives a package whose omissions are not concealed.

**DERIVED.** Unknown information is absorbing for mandatory predicates. For a three-valued conjunction \(\wedge_3\),

\[
1\wedge_3 ?=?,\qquad 0\wedge_3 ?=0,
\qquad ?\neq 1.
\tag{13}
\]

This rule blocks a certificate from passing merely because an absent fact was treated as satisfied.

## 7. Defect Hypotheses, Damage, and Recourse

**DERIVED.** A defect inquiry is represented as a hypothesis set rather than a scalar label:

\[
\Delta(x_v,h)=
\{\delta_1:\text{design},\delta_2:\text{manufacture or integration},
\delta_3:\text{instructions},\delta_4:\text{update or control},
\delta_5:\text{cybersecurity}\}.
\tag{14}
\]

The labels organize evidence. Their legal relevance and content must be determined from the applicable transposition and authoritative interpretation of Directive (EU) 2024/2853 [@EU2024ProductLiability].

**CONJECTURE.** For analytical simulation, an evidential defect score may be defined as

\[
s_{\delta}(x_v,h)=
\sigma\!\left(\beta_0+\sum_j\beta_j f_j(x_v,h)\right),
\tag{15}
\]

where $\sigma$ is logistic and $f_j$ are disclosed features. This score is neither defectiveness nor probability of judicial liability. It is a model output whose calibration, jurisdictional validity, and fairness require empirical study.

**DERIVED.** If an authorized decision has already established a total compensable amount \(M_h\) and legally valid shares \(\lambda_a\), bookkeeping may enforce

\[
M_h\ge 0,\qquad \lambda_a\ge0,\qquad
\sum_{a\in A_h}\lambda_a=1,
\qquad m_a=\lambda_a M_h.
\tag{16}
\]

The software checks arithmetic after the legal inputs exist. It does not choose \(M_h\), \(A_h\), or \(\lambda_a\).

**DERIVED.** Recourse is a separate directed relation. If (m_a) is the amount initially borne by (a) and (r_{ab}) is an authorized recourse amount from (a) against (b), then net burden is

\[
b_a=m_a-\sum_b r_{ab}+\sum_b r_{ba}.
\tag{17}
\]

Separating victim-facing compensation from inter-operator recourse prevents an internal allocation model from delaying the external remedy.

## 8. Temporal Compliance and Update Semantics

**DERIVED.** AI systems change after release. A compliance snapshot cannot be inherited across an update unless the impact relation permits it. Let \(v\prec v'\) be an update and \(I(v,v')\) its affected duty set. Then

\[
\operatorname{Carry}(d,v,v')=
\operatorname{Pass}(d,v)\land d\notin I(v,v')
\land\operatorname{EvidenceStable}(d,v,v').
\tag{18}
\]

Otherwise the duty must be re-evaluated. The impact set must be auditable and cannot be empty by default.

**DERIVED.** An event-time duty ledger is append-only in logical effect:

\[
L_{t+1}=L_t\cup\{e_{t+1}\},
\qquad
\operatorname{View}(L,t)=\{e\in L\mid \tau(e)\le t\}.
\tag{19}
\]

Corrections add superseding records rather than erase the fact that an earlier record existed. This supports reconstruction while allowing privacy-preserving retention policies at the storage layer.

**CONJECTURE.** A monitoring policy can prioritize events with a disclosed risk function

\[
R(e)=P(H\mid e)\cdot S(H\mid e)\cdot X(e),
\tag{20}
\]

where probability, severity, and exposure are separately estimated. Multiplication is a policy choice, not a statutory formula; alternative aggregation rules should be tested for calibration and distributional impact.

## 9. Certificate Architecture

**DERIVED.** A release certificate is a tuple

\[
\mathcal{C}=(s,t,b,g,m,a,r,q),
\tag{21}
\]

where (s) is subject commit, (t) source tree, (b) build identity, (g) gate results, (m) mutation evidence, (a) axiom audit, (r) runtime receipts, and (q) claim audit. Each component must bind to the same subject or explicitly state a cross-repository dependency identity.

**DERIVED.** Certificate closure is fail-closed:

\[
\operatorname{Closed}(\mathcal{C})=
\operatorname{SameSubject}(\mathcal{C})\land
\bigwedge_{g_i\in g}\operatorname{Pass}(g_i)\land
\operatorname{NoMissing}(\mathcal{C})\land
\operatorname{VerifierPass}(\mathcal{C}).
\tag{22}
\]

A green job color is not a substitute for the predicates in Equation (22). A verifier report marked failed or incomplete blocks closure even if the workflow platform reports success.

**FORMALIZED.** Where the repository's release evidence identifies a theorem manifest and axiom audit for a specific subject, those artifacts can support bounded claims about that subject. They do not support a claim that Equations (8)--(20) are Lean-verified or legally authorized.

## 10. Analysis

**DERIVED.** The model prevents four category errors. First, it prevents role inference from becoming liability. The incidence tensor records an asserted role with a source; it does not impose a legal consequence. Second, it prevents technical causality from becoming legal causation. Intervention scores expose assumptions and candidate contributions. Third, it prevents compliance from becoming immunity. Equation (1) leaves the liability predicate open. Fourth, it prevents release evidence from becoming legal validation. Equation (2) constrains the meaning of certificates.

**DERIVED.** The graph also improves contestability. An affected person can challenge a particular edge, event, version, or duty source rather than confront an undifferentiated system narrative. A producer can identify a downstream modification; a deployer can identify missing instructions; a component supplier can dispute integration assumptions. These are structured positions, not automatically successful defenses.

**CONJECTURE.** The most valuable empirical test is reconstruction latency. For a set of incidents (I), compare the time and unresolved-question count under ordinary logs and under the proposed typed ledger:

\[
\Delta T=\frac1{|I|}\sum_{i\in I}(T_i^{\mathrm{ordinary}}-T_i^{\mathrm{typed}}),
\quad
\Delta U=\frac1{|I|}\sum_{i\in I}(U_i^{\mathrm{ordinary}}-U_i^{\mathrm{typed}}).
\tag{23}
\]

Positive values would support operational usefulness. They would not prove legal correctness.

**CONJECTURE.** A second test concerns false confidence. Reviewers should receive identical cases with and without a “formal certificate” label while the underlying evidence remains constant. If the label changes liability judgments, the interface may induce automation bias. The certificate display should then be redesigned to foreground scope and exclusions.

## 11. Evidence Ledger

### 11.1 Worked Trace Without a Liability Verdict

**DERIVED.** Consider a high-risk decision-support service assembled from a base model, a domain adapter, a retrieval collection, a policy configuration, and a user interface. The producer releases version (v_1); a deployer later changes the retrieval collection and threshold configuration, creating (v_2); an operator relies on one output in a transaction that is later alleged to have caused loss. The infrastructure creates separate event records for the release, modification, deployment, query, output, human review, and alleged incident. It does not compress them into the sentence “the AI caused the loss.” That sentence is a legal and causal conclusion whose predicates remain to be evaluated.

**DERIVED.** The trace closure for the disputed output includes precisely the recorded ancestors of (v_2). If the base model is unchanged but the retrieval collection and threshold differ, the graph permits a reviewer to ask whether the alleged failure is invariant under the deployer's modifications. Replaying the same input against (v_1) and (v_2) can provide comparative evidence. A different output under (v_1) may support investigation of the changed components, but it does not by itself establish that those changes were defective, that the earlier output was legally adequate, or that the difference caused compensable damage.

**DERIVED.** Duty records are evaluated independently. A producer-facing record may concern technical documentation, risk management, instructions, monitoring cooperation, or an update under the producer's control. A deployer-facing record may concern use according to instructions, human oversight, input relevance, monitoring, or impact assessment, depending on classification and context. The system stores the legal source and applicability premises for every asserted duty. If a premise is contested, the duty status becomes unresolved rather than silently passing.

**DERIVED.** The evidential package should expose at least five competing hypotheses: the system performed as specified but the specification was unsuitable; an implementation departed from the specification; a downstream modification altered performance; a human decision broke the causal sequence; or the alleged loss arose independently. These hypotheses may overlap. A reviewer can attach supporting and opposing evidence to each hypothesis while leaving its legal significance open.

**CONJECTURE.** Counterfactual replay is useful only when the retained environment is sufficiently reproducible. Model weights without the retrieval corpus, prompt policy, dependency versions, randomness controls, and input normalization are an incomplete reconstruction. Conversely, perfect technical replay does not reproduce a human decision context. Empirical validation should therefore report both a technical replay coverage rate and a contextual reconstruction rate rather than one undifferentiated reproducibility score.

**DERIVED.** The worked trace illustrates why the liability layer should consume, but not be identical to, the release layer. Release evidence answers questions such as whether a named artifact was built, whether selected tests passed, whether formal modules elaborated, and whether a verifier accepted a same-subject evidence bundle. The liability inquiry asks additional questions about applicable norms, reasonable expectations, presentation, foreseeable use, control, defect, disclosure, causation, damage, and defenses. The second inquiry may cite the first; it cannot be reduced to it.

### 11.2 Operational Acceptance Criteria

**DERIVED.** A deployment can adopt the infrastructure without adopting any liability prediction model. The minimum operational acceptance criteria are: every production output resolves to a versioned component graph; every legally significant change creates a new event rather than overwriting history; every asserted duty points to a source and records unresolved applicability; every evidence item has provenance and challenge status; every automated score is labeled non-dispositive; and every release certificate identifies its subject and missing evidence. These criteria are observable engineering properties.

**CONJECTURE.** Organizations may be tempted to add a single “liability risk” number. This should be resisted unless the number is tied to a precise decision, population, loss function, calibration study, and review pathway. A scalar collapses different uncertainties: uncertainty about facts, uncertainty about law, uncertainty about causal structure, and uncertainty about future institutional decisions. Keeping those dimensions separate increases cognitive load, but it also makes disagreement inspectable.

**DERIVED.** Retention policy creates a genuine tension. An incident reconstruction benefits from detailed logs, while privacy, confidentiality, security, and data-minimization duties can restrict retention. The graph therefore stores stable identifiers and provenance relations without assuming that all underlying content remains indefinitely available. A tombstone can record lawful deletion, the authority for deletion, the deletion time, and the resulting limitation on reconstruction. It must not pretend that deleted content was verified.

**CONJECTURE.** The infrastructure should be evaluated with adversarial omission tests. Investigators can remove or corrupt a role assignment, update record, dependency edge, or source reference and ask whether the gate fails closed. Mutation detection is relevant because a system that continues to issue an unqualified certificate after a material evidence deletion has not implemented the stated assurance contract. Such tests establish behavior on the chosen mutations, not completeness against all future failures.

| Claim | Status | Evidence | What the evidence does not establish |
|---|---|---|---|
| The AI Act and Directive 2024/2853 are distinct operative EU instruments | DERIVED | Official texts [@EU2024AIAct; @EU2024ProductLiability] | Their application to a particular system or case |
| AI opacity and distributed control complicate liability design | DERIVED | Legal-economic analysis [@Hacker2023; @BuitenEtAl2021] | A universal liability rule |
| Provenance closure is a least fixed point of the recorded dependency operator | DERIVED | Definition (6), Tarski [@Tarski1955] | Completeness or truth of recorded edges |
| Intervention scores can organize causal investigation | CONJECTURE | Proposed Equations (8)--(9) | Legal causation or admissibility |
| Release gates can check same-subject evidence | FORMALIZED only where matched by repository theorem and certificate artifacts | Subject-bound formal artifacts | Product safety, compliance, defect, damages, or liability |
| Typed ledgers reduce reconstruction time | CONJECTURE | Requires incident study using Equation (23) | Established empirical improvement |

## 12. Verification Boundary

**FORMALIZED.** Lean may prove propositions over encoded types, such as closure, preservation, monotonicity, uniqueness, or consistency under explicit assumptions. The kernel checks proof terms; it does not inspect the world [@DeMouraUllrich2021; @Mathlib2020].

**DERIVED.** Engineering tests may show that fixtures execute, receipts bind to versions, mutations are detected, or certificate fields agree. These are runtime and provenance claims. They are not mathematical proofs unless their semantics and execution have been formally connected to a theorem, and they are not legal judgments under any circumstance.

**DERIVED.** Legal authority supplies at least four inputs that code cannot create: the governing norm, an authoritative interpretation where contested, accepted findings of fact, and the institutional power to decide. The infrastructure can preserve those inputs and reject malformed combinations. It cannot manufacture authority.

**CONJECTURE.** Automated screening may help identify missing evidence or inconsistent role descriptions. Any deployment should measure false-negative rates for legally significant omissions and provide a human override with reasons. Until that evidence exists, screening remains advisory.

## 13. Limitations

**DERIVED.** The model is jurisdictionally narrow. It uses current EU instruments as a baseline and does not purport to encode Member State transposition, procedural law, sectoral regimes, contract law, professional negligence, criminal liability, or non-EU systems.

**DERIVED.** The causal equations simplify contested philosophical and evidential questions. Intervention models require a causal graph and stable variables; real AI supply chains may exhibit feedback, strategic behavior, latent confounding, and nonstationarity. Scores can assist inquiry but may also conceal assumptions.

**DERIVED.** The duty and role schemas are only as reliable as their sources. An append-only ledger can faithfully preserve a false statement. Source binding improves auditability, not truth.

**DERIVED.** The framework does not calculate damages, allocate liability, or determine defect. Equations (15)--(17) are usable only after legally authorized inputs are supplied. No formula in this paper is represented as an operative rule of EU law.

**CONJECTURE.** Future work should test the model on public incident records, compare alternative causal representations, evaluate reviewer comprehension, and formally verify only those structural invariants whose meanings can be stated without importing unresolved legal judgments.

## 14. Declarations

### Funding

This research received no external funding.

### Conflict of Interest

The author declares no conflict of interest.

### Data Availability

No personal, confidential, or customer data were used. The analyzed technical materials are the public source code, manifests, workflow definitions, and release artifacts of the `legal-math-modeling` repository. Availability of a repository artifact does not imply that it contains evidence for every legal claim discussed here.

### Ethics

The study did not involve human participants, personal data, or animal subjects. The principal ethical constraint is non-substitution: formal or computational outputs must not be presented as authoritative legal decisions.

### Author Contributions (CRediT)

Laupinco: Conceptualization, Methodology, Formal analysis, Investigation, Writing—original draft, Writing—review and editing, and Project administration.

### AI Usage Disclosure

Generative AI tools assisted with language drafting and structural editing. The author selected the research questions, controlled the legal and proof boundaries, reviewed the mathematical definitions, and remains responsible for the text. AI-generated language was not treated as a legal source, factual finding, proof certificate, or authorship contribution.

## References

The following works are cited through the shared bibliography: [@EU2024AIAct; @EU2024ProductLiability; @Hacker2023; @BuitenEtAl2021; @RibeiroEtAl2016; @WachterEtAl2018; @GuidottiEtAl2018; @Lipton2018; @Hoare1969; @DeMouraUllrich2021; @Mathlib2020; @Reiter1980; @Dung1995; @PrakkenSartor1997; @Tarski1955].
