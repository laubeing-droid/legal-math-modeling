# Explainable Legal Reasoning as a Typed Proof-and-Evidence Interface

**Author:** Laupinco

## Abstract

Legal AI explanations fail when they answer the wrong question well. A feature attribution can describe a model while omitting the legal rule; a proof trace can show derivability while concealing disputed premises; a fluent rationale can sound legally persuasive without being connected to either computation or authority. This paper defines explainable legal reasoning as a typed interface among a claim, its legal source, accepted and disputed facts, inferential steps, counterarguments, and verification evidence. The framework distinguishes fidelity, legal relevance, contestability, provenance, and comprehensibility instead of compressing them into one explanation score. It defines local and global explanation objects, counterfactual witnesses, minimal support sets, attack graphs, provenance closure, and audience-relative presentation. More than ten equations specify these components and their failure conditions. The repository's formal proofs may support selected structural properties, but no Lean theorem establishes explanation quality, audience comprehension, legal adequacy, or the truth of case facts. Those propositions are marked as derived analytical results or conjectures. The central result is negative but useful: explainability cannot authorize a legal conclusion. It can make the path to a candidate conclusion inspectable, challengeable, and reproducible within an explicitly bounded model.

## 中文摘要

法律人工智能的“解释”并非单一对象。特征归因解释模型行为，推导轨迹解释形式结论如何生成，法律理由解释规范与事实如何支持主张，面向当事人的说明则要求可理解和可争辩。本文把解释建模为连接结论、法源、事实、推理步骤、反对意见与验证证据的类型化接口，并分别定义忠实度、法律相关性、来源完整性、可争辩性与受众可理解性。本文公式均为分析性模型或待验证假说；仓库现有 Lean 证明不证明解释质量、法律充分性或人类理解。形式系统负责暴露推理结构，人类法律主体负责确认法源、事实与裁判权限。

**Keywords:** explainable AI; legal reasoning; provenance; counterfactual explanation; argumentation; formal verification

**关键词：** 可解释人工智能；法律推理；来源追踪；反事实解释；论证；形式验证

## 1. Research Questions and Status Labels

The research questions are: What exactly is being explained in a legal-reasoning system? Which mathematical properties make an explanation faithful and contestable? How should model-level and law-level explanations be joined? Which claims can formal verification support, and which require legal or empirical judgment?

**FORMALIZED** denotes a proposition proved for identified repository definitions and assumptions. **DERIVED** denotes a mathematical consequence of definitions in this paper without a corresponding Lean proof. **CONJECTURE** denotes an empirical or normative hypothesis. Explanation-quality formulas in this paper are not Lean-proved.

**DERIVED.** An explanation is not a free-form paragraph. For a candidate conclusion (c), define

\[
E(c)=(c,N,F,R,A,P,V,U),
\tag{1}
\]

where (N) is the cited norm set, (F) the fact set, (R) inference steps, (A) attacks or alternatives, (P) provenance, (V) verification records, and (U) unresolved elements. Omitting (U) is a substantive defect when uncertainty exists.

## 2. Related Work

**DERIVED.** LIME constructs locally interpretable surrogate models, counterfactual methods identify changes associated with a different output, and surveys organize explanation families [@RibeiroEtAl2016; @WachterEtAl2018; @GuidottiEtAl2018]. Lipton shows that “interpretability” can denote incompatible properties [@Lipton2018]. These works motivate a vector-valued account.

**DERIVED.** Abstract and structured argumentation provide attacks, defenses, preferences, and acceptance semantics [@Dung1995; @PrakkenSartor1997; @ModgilPrakken2013]. Legal case models add values and precedential reasoning [@BenchCapon2003; @BenchCaponSartor2003]. An argument graph is therefore a natural explanation substrate, but acceptance in a graph is not institutional legal validity.

**DERIVED.** Formal verification supplies inspectable proof objects. Hoare's program logic separates assumptions from guaranteed postconditions, and Lean checks constructed proof terms [@Hoare1969; @DeMouraUllrich2021; @Mathlib2020]. This supports explanation of derivability, not explanation of why an encoded premise is legally authoritative or factually true.

## 3. Explanation Targets

**DERIVED.** A legal AI system has at least four targets: prediction \(f(x)\), transformation \(T(s)\), derivation \(K\vdash c\), and institutional decision \(J(c)\). Their explanations are not interchangeable:

\[
E_f\neq E_T\neq E_{\vdash}\neq E_J.
\tag{2}
\]

A faithful \(E_f\) may still be irrelevant to \(E_J\); a proof-valid \(E_{\vdash}\) may rely on a contested fact.

**DERIVED.** The explanation contract is target-indexed:

\[
\operatorname{Explains}(E,y,q,a)
\iff E\text{ answers question }q
\text{ about target }y\text{ for audience }a.
\tag{3}
\]

Without (q) and (a), an assertion that a system is “explainable” is underspecified.

## 4. Fidelity and Legal Relevance

**CONJECTURE.** For a local surrogate (g_E) around input (x), predictive fidelity can be measured by

\[
\operatorname{Fid}_{x}(E)=
1-\frac{\sum_{z\in\mathcal N(x)}\pi_x(z)\ell(f(z),g_E(z))}
{\sum_{z\in\mathcal N(x)}\pi_x(z)},
\tag{4}
\]

with a disclosed neighborhood, kernel, and loss. This is a model-behavior metric, not legal adequacy [@RibeiroEtAl2016].

**DERIVED.** Legal relevance is instead a relation between an explanation element and an authorized issue set (I_j):

\[
\operatorname{Rel}_j(E)=
\frac{|\{e\in E:\exists i\in I_j,\operatorname{bearsOn}(e,i)\}|}{|E|}.
\tag{5}
\]

The issue set must come from governing law and legal judgment. Code cannot infer it from term frequency alone.

**DERIVED.** Fidelity and relevance are independent. A high-fidelity feature attribution can focus on variables legally prohibited or irrelevant; a legally relevant rule explanation can be unfaithful to the model that generated the score:

\[
\operatorname{Fid}(E)\uparrow\not\Rightarrow\operatorname{Rel}_j(E)\uparrow,
\qquad
\operatorname{Rel}_j(E)\uparrow\not\Rightarrow\operatorname{Fid}(E)\uparrow.
\tag{6}
\]

## 5. Support, Attack, and Minimality

Let an explanation graph be \(G_E=(Q,\to_s,\to_a)\), with support and attack edges. Nodes are typed as norm, fact, inference, conclusion, exception, authority, or evidence.

**DERIVED.** The support closure for (c) is the least fixed point

\[
S(c)=\mu Z.\bigl(\{c\}\cup\{p\mid \exists q\in Z:p\to_s q\}\bigr).
\tag{7}
\]

Tarski's fixed-point theorem supports the abstract construction when the predecessor operator is monotone [@Tarski1955]. The construction does not verify node truth.

**DERIVED.** A minimal support set \(M\subseteq S(c)\) satisfies

\[
M\vdash c\quad\land\quad
\forall M'\subsetneq M,\;M'\nvdash c.
\tag{8}
\]

Minimality reduces clutter but may hide cumulative context. An interface should allow expansion to the full closure.

**DERIVED.** An explanation is dialectically incomplete if it suppresses a recorded undefeated attacker:

\[
\operatorname{Complete}_{A}(E,c)
\iff
\forall a(a\to_a c\Rightarrow
a\in E\lor\exists d\in E:d\to_a a).
\tag{9}
\]

This condition mirrors defense in abstract argumentation [@Dung1995]. It is relative to recorded attacks, not all arguments that could exist.

## 6. Counterfactual Explanation

**CONJECTURE.** A counterfactual witness for decision (f(x)=y) and target (y') solves

\[
x^{\star}\in\arg\min_z
d(x,z)+\lambda\ell(f(z),y')
+\Omega(z;x),
\tag{10}
\]

where (Omega) encodes feasibility, mutability, and legal constraints [@WachterEtAl2018]. The distance and constraints are normative design choices.

**DERIVED.** A legally usable counterfactual must distinguish actionable and protected attributes. If (P) is the protected-coordinate set, a basic invariance condition is

\[
\forall k\in P,\quad x_k^{\star}=x_k.
\tag{11}
\]

This does not prove fairness. Proxy variables and structural inequality can survive coordinate invariance.

**DERIVED.** Counterfactual explanation is not causal proof:

\[
f(x^{\star})\neq f(x)
\not\Rightarrow
x-x^{\star}\text{ legally caused the original outcome}.
\tag{12}
\]

It identifies sensitivity under a model and intervention definition.

## 7. Provenance and Verification

**DERIVED.** Each explanation element has a provenance tuple

\[
p(e)=(\operatorname{source},\operatorname{version},
\operatorname{time},\operatorname{method},\operatorname{status}).
\tag{13}
\]

Status distinguishes asserted, verified-against-source, disputed, superseded, unknown, and rejected. Source verification cannot upgrade disputed legal content to accepted law.

**DERIVED.** Provenance completeness is

\[
\operatorname{Prov}(E)=
\frac{|\{e\in E:p(e)\text{ has all mandatory fields}\}|}{|E|}.
\tag{14}
\]

A value of one means metadata completeness, not substantive correctness.

**DERIVED.** Proof replay is subject-bound. For subject (s), environment (Gamma_s), and theorem (t),

\[
\operatorname{Replay}(s,t)=1
\iff
\Gamma_s\vdash t
\text{ and the checked artifact identifies }s.
\tag{15}
\]

A theorem checked against another commit or dependency set is not evidence for (s) without a verified equivalence bridge.

**FORMALIZED.** Selected repository claims may be supported by same-subject Lean elaboration and axiom-audit artifacts. This does not formalize Equations (4)--(6), (10)--(12), or audience comprehension.

## 8. Audience-Relative Presentation

**CONJECTURE.** Comprehension should be measured empirically. For audience class (a), define

\[
C_a(E)=\frac1{|Q_a|}\sum_{q\in Q_a}
\mathbf1[\operatorname{answer}_a(q,E)=\operatorname{correct}(q)].
\tag{16}
\]

Reading time or satisfaction alone is insufficient. Questions should test the conclusion, assumptions, uncertainty, alternatives, and available challenge.

**DERIVED.** Explanation selection is a constrained optimization, not maximal disclosure:

\[
E_a^{\star}\in\arg\max_{E'\subseteq E}
\left(C_a(E')+\eta\operatorname{Rel}_j(E')
-\beta\operatorname{Load}(E')\right)
\quad\text{s.t. mandatory items remain.}
\tag{17}
\]

The mandatory set includes decisive premises, unresolved conflicts, provenance, and scope limitations. Compression cannot remove them.

## 9. Explanation Quality Vector

**DERIVED.** The framework reports a vector

\[
\mathbf q(E)=
(\operatorname{Fid},\operatorname{Rel},\operatorname{Prov},
\operatorname{Complete}_A,C_a,\operatorname{Repro}),
\tag{18}
\]

not a single grade. A scalar aggregation conceals tradeoffs unless weights and thresholds are public.

**CONJECTURE.** When a deployment requires triage, a scalar may be used only as an explicitly local policy:

\[
Q_w(E)=\sum_i w_iq_i(E),
\quad w_i\ge0,
\quad\sum_iw_i=1,
\tag{19}
\]

with sensitivity analysis across plausible (w). It is not a universal measure of legal explanation.

**DERIVED.** Fail-closed release requires mandatory dimensions:

\[
\operatorname{Release}(E)=1
\iff
\bigwedge_{i\in M}q_i(E)\ge\tau_i
\land U_{\mathrm{blocking}}=\varnothing.
\tag{20}
\]

An average cannot compensate for missing provenance or a concealed decisive counterargument.

## 10. Analysis and Worked Example

**DERIVED.** Suppose a system recommends denial of a license. A model explanation reports that a compliance-history variable dominated the score. A legal explanation identifies the statutory criteria, the accepted facts mapped to each criterion, the inferential rule, an exception argued by the applicant, and the authority status of each source. A process explanation records which version generated the recommendation and which human reviewed it. These three objects must be linked but not merged.

**DERIVED.** If the history variable was derived from a stale record, a faithful model explanation remains faithful: it correctly reports how the model used bad input. Provenance exposes the data problem. If the record is accurate but the criterion is legally irrelevant, relevance exposes a normative problem. If the rule and data are sound but an exception was hidden, dialectical completeness exposes the argumentative problem.

**CONJECTURE.** A user study should compare this typed explanation with a fluent narrative. Participants should answer questions about decisive premises, authority, uncertainty, and appeal. The primary endpoint is correct comprehension, with calibration between confidence and accuracy. The hypothesis is that typed explanations reduce confident misunderstanding even if users rate fluent narratives as more satisfying.

**DERIVED.** The model also constrains generative rationales. A language model may verbalize nodes already present in (E(c)). It may not create an uncited legal source, convert an unknown fact into an accepted premise, or omit a blocking attack. Generated prose is therefore a view over a structured object, not the authoritative object itself.

## 11. Evidence Ledger

### 10.1 Four Counterexamples to Scalar Explainability

**DERIVED.** Counterexample one concerns faithful irrelevance. Assume a benefits model uses age, reported income, household size, and an internal document-completeness flag. A local surrogate reproduces the model perfectly and identifies the flag as decisive. The explanation therefore has high fidelity under Equation (4). If the governing legal issue is whether statutory income and household criteria are met, however, the internal flag may be merely an administrative proxy. A perfectly faithful explanation of the model does not explain the legal entitlement. The failure is not opacity; it is a mismatch between the model target and the legal question. Adding more feature-attribution detail cannot repair that mismatch.

**DERIVED.** Counterexample two concerns relevant unfaithfulness. A generated rationale cites the correct statutory factors and gives an orthodox doctrinal sequence, but the deployed classifier actually relied on a correlated location variable. The narrative is legally relevant yet causally disconnected from the computation. It may describe how a lawful decision could have been made, not how this recommendation was generated. The design implication is that legal relevance and computational fidelity must be tested separately and joined by explicit links. A post hoc narrative cannot satisfy both dimensions merely because it is plausible.

**DERIVED.** Counterexample three concerns proof-valid error. Let a proof object establish \(F\land(F\rightarrow C)\rightarrow C\). The derivation is valid, reproducible, and minimal. If \(F\) is a misidentified fact or \(F\rightarrow C\) encodes an obsolete rule, the proof remains valid while the candidate conclusion is unusable. This is not a defect in deductive logic. It is evidence that proof validity is conditional and that an explanation must show premise status, source, temporal validity, and authority.

**DERIVED.** Counterexample four concerns comprehensible incompleteness. A two-sentence explanation may allow most readers to repeat the principal reason for a decision. If it omits a recorded exception that could reverse the result, its apparent comprehensibility is achieved by suppressing contestability. Equation (17) therefore constrains compression: audience adaptation may simplify vocabulary or order, but it cannot remove mandatory adverse material.

**CONJECTURE.** These counterexamples predict a systematic failure in one-number explainability benchmarks. Systems optimized against one dimension will exploit unmeasured dimensions: a fidelity benchmark rewards legally irrelevant detail; a satisfaction benchmark rewards confident prose; a brevity benchmark rewards omission; and a legal-relevance benchmark can reward rationalizations. A multi-dimensional evaluation should reduce this gaming, although that claim requires comparative experiments.

### 10.2 Propositions About Typed Explanations

**DERIVED. Proposition 1 (Target non-substitutability).** If two explanation targets have non-equivalent input domains or consequence relations, success on one target does not entail success on the other. A model explanation maps features to behavior, whereas a legal derivation maps authorized norms and accepted facts to a candidate legal conclusion. Because neither domain embeds into the other without an explicit bridge, Equation (2) is not merely a notation choice. A bridge must identify how model variables correspond to legal predicates, how uncertainty is handled, and who authorized the correspondence.

**DERIVED. Proposition 2 (Provenance monotonicity).** Adding a valid provenance field to an existing node cannot decrease metadata completeness under Equation (14), but it can rationally decrease confidence in the claim. A newly identified source may reveal that the node is obsolete, derivative, or disputed. Therefore provenance completeness and substantive support are distinct orders. Systems that equate “more metadata” with “more credible” commit a monotonicity error.

**DERIVED. Proposition 3 (Attack preservation).** Suppose \(E_1\subseteq E_2\), and \(E_2\) adds an undefeated attacker of \(c\). Then a presentation function that maps both objects to the same positive rationale is not dialectically faithful. It loses information relevant to acceptance even if the positive support path is unchanged. This proposition motivates regression tests in which attacks are added and the explanation must change.

**DERIVED. Proposition 4 (No averaging across blockers).** Let provenance completeness be zero because no decisive norm has a source, while other quality dimensions are one. Any weighted average with a positive but non-dominant provenance weight can exceed a release threshold. Equation (20) avoids that result through mandatory per-dimension thresholds. A source-free legal conclusion cannot be rescued by fluent language, local fidelity, or low cognitive load.

**DERIVED. Proposition 5 (Unknown preservation).** If a decisive premise has status unknown, a renderer that states the premise affirmatively is not a simplification of the same explanation. It creates a different object. Truth-status qualifiers are semantic content, so audience adaptation must preserve them even when technical implementation details are omitted.

**CONJECTURE.** A machine-checkable explanation schema will make these propositions enforceable at system boundaries. JSON or typed records can require target, question, audience, sources, status, and attacks before rendering. Schema validity will still not show that the selected legal sources or factors are correct, but it can prevent entire categories of silent omission.

### 10.3 Design Implications for a Legal Reasoning Pipeline

**DERIVED.** The first design implication is to generate explanations from the same typed intermediate representation used by the reasoner. If the reasoner emits a conclusion identifier and a proof or argument trace, the renderer should resolve those identifiers rather than ask a language model to reconstruct reasons from the final answer. This reduces, but does not eliminate, rationalization. The intermediate representation itself may omit relevant information or encode a mistaken legal model.

**DERIVED.** The second implication is to maintain two namespaces: computational predicates and legal predicates. A feature such as `days_since_last_payment` is computational. A predicate such as `material_breach` is legal. A bridge record may assert that a range of the first supports a factual proposition used in evaluating the second. The record must name its source, jurisdiction, time, and review status. Directly naming a model feature `material_breach` conceals the bridge and makes a prediction appear to be a legal finding.

**DERIVED.** The third implication is to represent authority separately from textual retrieval confidence. A retrieval model can estimate that a document passage is relevant to a query. It cannot infer from semantic similarity alone that the passage is binding, in force, applicable, correctly translated, or unmodified by later law. Authority is a typed field supplied or verified through an authorized legal process.

**DERIVED.** The fourth implication is to make negative and unresolved evidence first-class. Most generated explanations are optimized to justify the selected outcome. A contestable system must also retrieve exceptions, contrary authorities, disputed facts, and alternative classifications. The interface can order material by relevance, but it must signal the existence of recorded blockers even when access restrictions prevent full display.

**DERIVED.** The fifth implication is to preserve version identity. Explanations generated after a model or rule update can differ from those available at decision time. A review package therefore stores the original explanation object, the generating versions, and any later reinterpretation as separate records. Replacing the old explanation with a clearer new one destroys evidence about the actual process.

**DERIVED.** The sixth implication concerns human review. A checkbox saying that a person reviewed the output is insufficient. The record should identify which claim, evidence, uncertainty, and alternative the reviewer saw; the permitted actions; the action taken; and the reason. This does not prove meaningful review, but it creates testable evidence and prevents “human in the loop” from functioning as an empty label.

**CONJECTURE.** Explanation rendering can be stratified. A short notice states the result, decisive reasons, uncertainty, and challenge route; an intermediate view shows the typed support and attack graph; an expert view exposes sources, versions, proof objects, and model diagnostics. The hypothesis is that progressive disclosure improves comprehension without sacrificing contestability. The mandatory content must remain visible at every level.

### 10.4 Evaluation Framework

**DERIVED.** Evaluation begins with a frozen claim set. Each case specifies the candidate conclusion, governing issue set, accepted and disputed facts, authoritative and adverse sources, computational output, and known attacks. Evaluators then know what an explanation must reveal. Without a frozen reference, a fluent explanation can be scored against an evaluator's impression rather than a defined contract.

**DERIVED.** The technical suite contains mutation tests. Remove a decisive source; change a premise from accepted to disputed; insert an undefeated attack; substitute a different model version; alter a protected attribute; or break a bridge between a computational and legal predicate. The expected behavior is not always a different conclusion. It is at least a visible change in scope, status, quality vector, or release verdict. A system that returns identical unqualified prose has failed to preserve the mutation.

**DERIVED.** The legal review suite asks domain experts to classify each explanation element as relevant, irrelevant, misleading, incomplete, or jurisdictionally unresolved. Inter-rater disagreement is not simply noise. It may identify contested doctrine or ambiguous issue definitions. The dataset should retain disagreement and reasons rather than reduce them immediately to a majority label.

**CONJECTURE.** The user study should be randomized and task-based. Participants receive either a fluent rationale, a feature attribution, a proof trace, or the typed multi-layer explanation. They answer questions about the decisive rule, facts, uncertainty, adverse material, and challenge route. Measures include correctness, confidence calibration, time, and willingness to seek review. The main hypothesis is that the typed explanation improves detection of invalid premises and omitted counterarguments.

**CONJECTURE.** A legal-professional study should additionally measure action quality. Lawyers might identify the right missing evidence, formulate a relevant objection, or avoid relying on an obsolete source. These outcomes matter more than satisfaction ratings. Because expertise changes how explanations are used, results from lay participants cannot be generalized automatically to judges, regulators, or counsel.

**DERIVED.** Fairness evaluation examines whether explanation quality differs across affected groups. A model may provide equally accurate predictions while generating less actionable or more complex explanations for one group. Researchers should report group-conditioned components of (mathbf q(E)), missingness, and challenge success. A parity metric is descriptive; the legally appropriate fairness standard remains a separate normative input.

**DERIVED.** Reproducibility evaluation checks whether an independent verifier can regenerate the explanation object from the stated subject, inputs, and dependencies. Exact prose need not match if rendering is nondeterministic, but the decisive support, attacks, statuses, and sources must agree. Disagreement is reported rather than normalized away.

### 10.5 Failure Taxonomy and Recovery

**DERIVED.** A fidelity failure occurs when the explanation does not track the actual computation or derivation. Recovery requires access to the executed model, trace, or proof object; rewriting prose is insufficient. A relevance failure occurs when the explanation omits or misstates legally material issues. Recovery requires legal review of the issue mapping. A provenance failure occurs when sources or versions cannot be resolved. Recovery may be impossible for the historical decision and must be recorded as such.

**DERIVED.** A contestability failure occurs when adverse reasons or challenge routes are suppressed. Recovery adds the missing dialectical structure and reassesses any prior release decision. A comprehension failure occurs when users cannot correctly identify reasons, uncertainty, or recourse. Recovery changes presentation and must be re-tested with the intended audience. A confidentiality failure occurs when explanation reveals protected material; recovery requires lawful redaction with a visible withholding record.

**DERIVED.** These failures have different owners. Engineers can repair trace capture and subject binding. Knowledge engineers can repair mappings. Legal authorities must resolve disputed authority and relevance. Product designers can improve presentation. Governance bodies decide access and escalation. Assigning every failure to the “explainability model” obscures responsibility.

**CONJECTURE.** Incident reports should classify failures by this taxonomy and publish aggregate rates. Longitudinal evidence could then show whether a release improves one dimension by degrading another. Until such data exist, claims that the architecture produces better legal explanations remain prospective.

**DERIVED.** Recovery must also preserve the earlier defective explanation. An amended explanation is a new version linked to the original, with the reason, author, time, and affected decision recorded. Silent replacement would make later review unable to distinguish what the decision-maker actually saw from what investigators reconstructed afterward. The corrected version may improve future understanding, but it cannot retroactively supply notice, contestability, or human oversight at the original decision time.

| Claim | Status | Evidence | Exclusion |
|---|---|---|---|
| Explainability has distinct targets | DERIVED | Equations (1)--(3); XAI literature [@Lipton2018; @GuidottiEtAl2018] | No universal taxonomy theorem |
| Local fidelity is measurable after fixing neighborhood and loss | CONJECTURE | Equation (4); LIME [@RibeiroEtAl2016] | Legal relevance |
| Argument defense exposes recorded counterarguments | DERIVED | Equation (9); Dung semantics [@Dung1995] | Completeness beyond recorded graph |
| Counterfactuals expose model sensitivity | CONJECTURE | Equations (10)--(12); [@WachterEtAl2018] | Legal causation or fairness |
| Same-subject proof replay supports bounded formal claims | FORMALIZED where repository artifacts match | Lean sources and release evidence [@DeMouraUllrich2021] | Facts, authority, comprehension |
| Typed explanations improve comprehension | CONJECTURE | Requires the proposed user study | No present empirical result |

## 12. Verification Boundary

**FORMALIZED.** Formal verification may establish that encoded support closure is monotone, a compiler preserves a defined relation, a certificate binds to a subject, or a theorem follows from declared premises. Only actual theorem declarations and audits support this label.

**DERIVED.** Formal verification does not establish source authenticity unless authentication is an explicit verified premise; it does not establish legal applicability unless authorized interpretation is supplied; and it does not establish factual truth, audience comprehension, fairness, or institutional legitimacy.

**DERIVED.** Runtime tests, mutation reports, and receipts are engineering evidence. They can show that selected failures are detected and selected fixtures execute. They do not turn the explanation-quality vector into a theorem.

## 13. Limitations

**DERIVED.** The framework assumes that claims can be decomposed into typed nodes. Some legal reasoning depends on narrative, tacit institutional practice, contested characterization, or holistic judgment that resists lossless decomposition.

**DERIVED.** Minimal support and graph visualizations may create false precision. The recorded graph is a representation chosen by designers and reviewers. Absence of an attack can mean either that no attack exists or that collection failed.

**DERIVED.** Explanation interfaces can disclose confidential, privileged, personal, or security-sensitive information. A deployment needs lawful redaction and access control while preserving a visible account of what was withheld and why.

**CONJECTURE.** Cross-jurisdiction validation, adversarial user studies, accessibility testing, and longitudinal evaluation are required before claiming practical explanation quality.

## 14. Declarations

### Funding

This research received no external funding.

### Conflict of Interest

The author declares no conflict of interest.

### Data Availability

No personal or confidential data were used. Public repository sources and release artifacts provide technical context; they do not provide empirical user-study data.

### Ethics

No human participants or personal data were involved. Any future comprehension study requires appropriate ethics review and informed consent.

### Author Contributions (CRediT)

Laupinco: Conceptualization, Methodology, Formal analysis, Investigation, Writing—original draft, Writing—review and editing, Project administration.

### AI Usage Disclosure

Generative AI assisted language drafting and structural editing. The author controlled the research questions, sources, equations, and epistemic labels and remains responsible for the manuscript. Generated text was not treated as a legal authority, factual finding, or proof.

## References

Cited works are contained in the shared bibliography: [@RibeiroEtAl2016; @WachterEtAl2018; @GuidottiEtAl2018; @Lipton2018; @Dung1995; @PrakkenSartor1997; @ModgilPrakken2013; @BenchCapon2003; @BenchCaponSartor2003; @Hoare1969; @DeMouraUllrich2021; @Mathlib2020; @Tarski1955].
