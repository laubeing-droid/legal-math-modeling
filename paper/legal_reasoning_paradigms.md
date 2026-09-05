# Composing Legal Reasoning Paradigms Without Collapsing Their Semantics

**Author:** Laupinco

## Abstract

Computational legal reasoning is often described through rival paradigms: rules, defaults, arguments, precedents, temporal models, probabilities, and procedures. Treating one as the universal semantics creates avoidable category errors. This paper specifies a typed composition in which each paradigm answers a different question. Horn closure derives support from accepted premises; defeasible logic represents exceptions; argumentation resolves attacks under declared semantics; temporal Kripke structures evaluate time-indexed propositions; case comparison proposes analogies; Bayesian models quantify uncertainty under an explicit probability model; and procedural gates determine which outputs may enter an adjudicative stage. More than ten equations define the local semantics and the bridges between them. Selected structural invariants have counterparts in the repository's Lean development, but the integrated interpretation, factual premises, probability assignments, analogies, and legal conclusions are not thereby proved correct. The contribution is a disciplined architecture: heterogeneous reasoners communicate through typed, status-preserving interfaces rather than a single overloaded confidence score.

## 中文摘要

法律推理同时包含规则演绎、例外、论证攻防、先例类比、时间适用、概率证据与程序权限。本文不把其中任何一种提升为通用法律语义，而是为各范式规定不同输入、输出与证明义务，并通过保留来源、状态和不确定性的类型化桥接进行组合。公式描述局部闭包、缺省撤回、Dung 接受语义、Kripke 时间真值、类比候选、贝叶斯更新和程序门禁。仓库中的 Lean 证明只支持被明确编码的结构性质，不证明具体事实、概率、类比或裁判正确。

**Keywords:** legal reasoning; Horn closure; defeasible logic; argumentation; temporal logic; precedent; Bayesian inference

**关键词：** 法律推理；Horn 闭包；可废止逻辑；论证；时间逻辑；先例；贝叶斯推理

## 1. Research Questions and Claim Status

The questions are: Which legal-reasoning paradigms are genuinely complementary? What information must a bridge preserve? When may one paradigm consume another's output? Which composition claims are formally established?

**FORMALIZED** means proved for named Lean definitions and premises. **DERIVED** means a consequence of definitions here without a claimed Lean theorem. **CONJECTURE** means an empirical, legal, or unproved mathematical proposal.

## 2. Related Work

**DERIVED.** Horn clauses provide a tractable rule substrate [@Horn1951], while Tarski supplies the fixed-point foundation for monotone closure [@Tarski1955]. Default and circumscription logics model conclusions that classical entailment cannot safely preserve under new information [@Reiter1980; @McCarthy1980]. Defeasible logic offers explicit representation results and favorable complexity for propositional fragments [@AntoniouEtAl2001; @Maher2001].

**DERIVED.** Dung's frameworks abstract arguments and attacks, and preference-sensitive extensions add defeat policies [@Dung1995; @PrakkenSartor1997; @ModgilPrakken2013]. Legal case reasoning contributes factors, values, and precedential constraints [@RisslandAshley1987; @BenchCaponSartor2003; @Horty2011]. Temporal logic supplies model-checking semantics for evolving states [@Pnueli1977; @ClarkeEtAl1986; @Kripke1963]. Bayesian legal models organize uncertain evidence [@FentonNeilLagnado2013; @VlekEtAl2015]. No cited paradigm subsumes the institutional authority to decide law and fact.

## 3. Typed Local Semantics

Let a reasoning component have signature

\[
M_i:X_i\times\Theta_i\rightarrow Y_i\times E_i,
\tag{1}
\]

where $X_i$ is typed input, $\Theta_i$ declared policy, $Y_i$ output, and $E_i$ evidence. Composition requires a checked bridge, not mere serialization compatibility.

### 3.1 Monotone Rule Support

For facts (F) and Horn rules (R), define

\[
T_R(S)=F\cup\{h\mid(b_1\land\cdots\land b_n\rightarrow h)\in R,
\{b_1,\ldots,b_n\}\subseteq S\}.
\tag{2}
\]

**DERIVED.** (T_R) is monotone, so its least fixed point is

\[
C_R(F)=\mu T_R=\bigcup_{k\ge0}T_R^k(\varnothing).
\tag{3}
\]

On a finite carrier iteration stabilizes. Closure proves derivability from encoded inputs, not truth or legal authority.

### 3.2 Defeasible Revision

**DERIVED.** A default has prerequisite, justification, and conclusion:

\[
\delta=\frac{\alpha:\beta}{\gamma}.
\tag{4}
\]

It may support $\gamma$ when $\alpha$ holds and $\beta$ remains consistent [@Reiter1980]. New evidence can withdraw support:

\[
K\vdash_d q\quad\centernot\Rightarrow\quad K\cup\{e\}\vdash_d q.
\tag{5}
\]

The output therefore carries status and defeating conditions.

### 3.3 Argumentation

An abstract framework is

\[
AF=(A,\rightharpoonup).
\tag{6}
\]

**DERIVED.** Its characteristic operator is

\[
\Gamma_{AF}(S)=\{a\in A\mid
\forall b(b\rightharpoonup a\Rightarrow
\exists c\in S:c\rightharpoonup b)\}.
\tag{7}
\]

Grounded acceptance is the least fixed point of (Gamma_{AF}) [@Dung1995]. Preferred, stable, credulous, and skeptical answers must retain their semantic profile.

### 3.4 Temporal Semantics

Let (K=(W,R_t,V)) be a temporal Kripke model. Then

\[
K,w\models G\varphi
\iff\forall v(wR_tv\Rightarrow K,v\models\varphi),
\tag{8}
\]

and

\[
K,w\models F\varphi
\iff\exists v(wR_tv\land K,v\models\varphi).
\tag{9}
\]

**DERIVED.** Legal applicability additionally requires jurisdiction, norm version, event time, and authorized interpretation; temporal truth in (K) alone is insufficient.

### 3.5 Analogy

**CONJECTURE.** For a problem (p) and precedent (c), a review-priority score may be

\[
A(p,c)=a(c)\sum_f w_f\,\operatorname{match}_f(p,c)
-\sum_d v_d\,\operatorname{distinction}_d(p,c).
\tag{10}
\]

Authority (a(c)), factors, and material distinctions are legal inputs. The score proposes a case for review; it does not create precedent.

### 3.6 Probability

**CONJECTURE.** Within an explicit model,

\[
P(H\mid E)=\frac{P(E\mid H)P(H)}{P(E)}.
\tag{11}
\]

Bayesian coherence does not select hypotheses, priors, evidence reliability, or legal standards [@FentonNeilBerger2016]. Probability remains separate from normative acceptance.

### 3.7 Procedure and Authority

**DERIVED.** A candidate conclusion may advance only when

\[
\operatorname{Admit}(q)=
\operatorname{AuthorizedInput}(q)\land
\operatorname{RequiredEvidence}(q)\land
\neg\operatorname{BlockingTaint}(q).
\tag{12}
\]

Failure is explicit; unknown is not coerced to pass.

## 4. Bridge Contracts

**DERIVED.** A bridge from (M_i) to (M_j) is

\[
B_{ij}=(\tau_{ij},P_{ij},Q_{ij},\pi_{ij}),
\tag{13}
\]

with translation $\tau$, precondition $P$, promised invariant $Q$, and provenance map $\pi$.

**DERIVED.** A sound bridge obligation is

\[
P_{ij}(x)\land M_i(x)=(y,e)
\Rightarrow Q_{ij}(\tau_{ij}(y),\pi_{ij}(e)).
\tag{14}
\]

This does not say that (y) is legally correct; it states what the translation preserves.

**DERIVED.** Status preservation forbids promotion:

\[
\operatorname{status}(\tau_{ij}(y))
\preceq\operatorname{status}(y).
\tag{15}
\]

Candidate, disputed, assumed, or unknown material cannot become verified solely by crossing a module boundary.

**DERIVED.** Provenance composes contravariantly to output dependence:

\[
\operatorname{Prov}(z)=
\bigcup_{y\leadsto z}\operatorname{Prov}(y)
\cup\{B_{ij}\text{ identity}}.
\tag{16}
\]

An output is auditable only if the source and each bridge are recoverable.

## 5. Composition Architecture

**DERIVED.** A disciplined pipeline begins with source-bound facts and norms. Horn closure derives monotone support. A structured-argument constructor records rules and premises. Attack generation adds conflicts, exceptions, and priority challenges. A declared Dung profile evaluates acceptance. Temporal evaluation restricts propositions to the relevant state. Procedure gates decide whether a candidate can be presented to an authorized reviewer. Analogy and probability remain side modules that propose evidence or comparisons, not automatic premises.

**DERIVED.** The composite is a directed acyclic evidence flow even when local reasoners use fixed points:

\[
\mathcal M=M_n\circ B_{n-1,n}\circ\cdots\circ B_{1,2}\circ M_1.
\tag{17}
\]

Feedback creates a new versioned request rather than rewriting prior evidence. This preserves the distinction between computation at time (t) and later revision.

**DERIVED.** Branch-safe evaluation keeps alternatives:

\[
\operatorname{Eval}(x)=
\{(b,y_b,e_b)\mid b\in\operatorname{Branches}(x)\}.
\tag{18}
\]

Selecting one branch requires a named policy or authorized decision. Enumeration is not endorsement.

**FORMALIZED.** The repository contains formal modules for request identity, outcomes, typed graphs, obligations, finite machines, fact/evidence dependencies, Horn support, argument construction, attack/defeat, Dung profiles, branch queries, procedure, composition, trust, and conditional contraction. The precise theorem inventory and same-subject audit determine which propositions carry this label. Equations (10)--(12) and the overall legal interpretation are not claimed as proved.

## 6. Counterexamples

**DERIVED.** Deduction-only failure: a valid Horn derivation from an obsolete norm is formally correct and legally unusable. Provenance and temporal applicability are therefore mandatory.

**DERIVED.** Probability-only failure: a posterior of (0.9) does not specify a legal standard, admissibility, or burden allocation. Replacing those concepts with a threshold hides normative choices.

**DERIVED.** Argumentation-only failure: grounded acceptance in an incomplete attack graph says nothing about an omitted controlling exception. Graph completeness is an evidence question.

**DERIVED.** Analogy-only failure: a highly similar case on another issue or from an inapplicable jurisdiction cannot supply direct support. Comparability gates precede distance.

**DERIVED.** Temporal-only failure: a proposition true at every modeled future state may still be outside the authority or remedial scope of the decision-maker.

**DERIVED.** Unified-score failure: averaging proof validity, source trust, similarity, probability, and authority permits one dimension to compensate for a blocker in another. The architecture uses typed gates instead.

## 7. Analysis and Design Propositions

**DERIVED. Proposition 1.** Heterogeneous composition is sound only relative to bridge obligations. Matching field names or JSON schemas proves syntactic compatibility, not semantic preservation.

**DERIVED. Proposition 2.** Monotone support and nonmonotone acceptance can coexist without contradiction. The support closure may grow as facts are added, while an argument loses acceptance because the same addition constructs a new attacker.

**DERIVED. Proposition 3.** Formal proof and probabilistic uncertainty answer different questions. A theorem can prove that an update formula is normalized while the input likelihoods remain empirically uncertain.

**DERIVED. Proposition 4.** Procedure is not a final formatting layer. Authority and admissibility constrain which premises may enter earlier reasoners; late filtering cannot undo reasoning already contaminated by prohibited material.

**CONJECTURE.** Typed paradigms will improve error localization. When a result changes, a reviewer can attribute the change to facts, rules, attacks, semantics, time, analogy, probability, or procedure rather than an opaque global score. This requires controlled evaluation.

## 8. Evaluation Framework

**DERIVED.** Unit tests target each local semantics. Bridge tests mutate status, provenance, policy identity, and branch identifiers. Expected behavior is fail-closed rejection or visible qualification. End-to-end fixtures confirm that the selected composition executes but do not prove universal refinement.

**CONJECTURE.** Comparative experiments should evaluate a monolithic language-model baseline, a unified-score symbolic baseline, and the typed composition. Measures include source accuracy, blocking-error detection, adverse-argument recall, calibration, reviewer time, and the ability to locate the responsible module.

**DERIVED.** Ablation removes one paradigm at a time. If removing procedure increases apparent answer rate while increasing unauthorized premises, coverage has not improved. If removing argumentation preserves predictions but hides counterarguments, outcome accuracy alone misses the loss.

### 8.1 Paradigm Conflicts

**DERIVED.** Conflict begins when two components appear to answer the same question but actually operate over different objects. A Horn consequence records support under accepted premises, whereas a defeasible conclusion records support that survives a specified set of exceptions. An argumentation status records acceptability relative to an attack graph and a chosen semantics, not derivability from the underlying rules [@Horn1951; @Reiter1980; @Dung1995]. Treating these outputs as interchangeable removes the conditions that make each statement intelligible. Composition must therefore preserve the question posed, the assumptions admitted, and the mode of defeat, even when every component uses the same surface label, such as “accepted.”

**DERIVED.** A second conflict concerns direction of revision. Monotone closure permits new premises to add consequences without invalidating earlier derivations [@Tarski1955]. Default reasoning and preference-sensitive argumentation permit new information to defeat an earlier position [@Reiter1980; @PrakkenSartor1997]. The conflict is operational rather than contradictory. A growing support set may construct a new counterargument that reduces the acceptance status of an existing claim. A composite system must expose both events: support increased, yet adjudicative acceptability decreased. Reporting only the final label conceals the legally relevant reason for change.

**DERIVED.** Temporal, analogical, and probabilistic components create different forms of relevance. Temporal evaluation asks whether a proposition holds at a legally material state [@Pnueli1977]. Analogy asks whether a prior case is sufficiently comparable for a stated issue and purpose [@BenchCaponSartor2003; @Horty2011]. Probability asks how evidence changes uncertainty under a declared model [@FentonNeilLagnado2013]. None supplies the missing predicates of another. High similarity cannot cure temporal inapplicability, and a high posterior cannot establish authority. Their outputs may inform a later decision only through bridges that name the receiving question.

**CONJECTURE.** The hardest conflict in practice will arise between epistemic convenience and institutional responsibility. Engineers may prefer a single scalar because it sorts candidates and simplifies interfaces. Legal decision makers, however, may need to know that one candidate is textually supported but procedurally barred, while another is factually uncertain but preserved for hearing. A scalar ordering destroys that incomparability unless the ordering policy already embeds the contested legal judgment. The safer design keeps blockers categorical and delegates any authorized trade-off to a recorded decision point.

### 8.2 Composition Invariants

**DERIVED.** Question identity is the first invariant. Every output should carry a compact statement of what was decided: derivability, default survivability, argument acceptability, temporal applicability, evidential probability, analogical priority, or procedural admissibility. A bridge may reformulate that question, but it must record the reformulation. If “likely fact” becomes “accepted premise,” the bridge has changed an epistemic assessment into an institutional act. That transition requires an identified rule and authorized actor, not a routine data conversion.

**DERIVED.** Defeater visibility is the second invariant. A conclusion transmitted from a defeasible or argumentative component must retain active defeaters, defeated defeaters, and unresolved challenges. Merely retaining the winning argument is insufficient because later evidence may reactivate a challenge. This requirement also prevents a receiving Horn component from treating a provisional conclusion as permanently monotone. The interface need not reproduce the entire source engine, but it must retain enough information to explain withdrawal and to reconstruct the relevant challenge relation.

**DERIVED.** Burden polarity is the third invariant. Absence of support for a proposition is not support for its negation, and failure to establish an exception is not automatically proof of the primary claim. The applicable burden rule determines what consequence, if any, follows from an unresolved issue. This rule must travel separately from the evidence state. Otherwise, a missing record can silently change from “unknown” to “false” during translation, and a procedural allocation can be mistaken for a factual finding.

**DERIVED.** Temporal anchoring is the fourth invariant. Each norm, fact, interpretation, and procedural act must retain the time to which it speaks, not merely the time at which it entered the system. Later enactment, discovery, or review does not automatically rewrite earlier applicability. A temporal bridge should preserve event time, legal-effect time, knowledge time, and decision time when those differ. Collapsing them invites retrospective application and makes subsequent correction indistinguishable from alteration of the historical record.

**DERIVED.** Loss accounting completes the invariant set. Some translations are intentionally lossy: a detailed argument graph may be summarized as a review queue, or a probability distribution may be reduced to an interval for presentation. The bridge should identify discarded distinctions and prohibit downstream claims that depend on them. This resembles a program contract in which preconditions and postconditions delimit what a transformation warrants [@Hoare1969]. It is a specification discipline, not a claim that the integrated legal interpretation has been mechanically proved.

**DERIVED.** Decision ownership is a further invariant. Components may recommend, rank, reject, or defer, but an output should identify whether any legally operative choice has occurred and who was entitled to make it. A model-selected branch is not equivalent to a fact finding, statutory interpretation, exercise of discretion, or order. When an authorized reviewer adopts a branch, the adoption should be represented as a new event linked to the computational record. This preserves the difference between reasons made available to a decision maker and reasons institutionally accepted by that decision maker.

### 8.3 Failure Detection and Recovery

**DERIVED.** Failure detection should test semantic expectations, not only schemas. A message can be well formed while carrying the wrong proposition, norm version, issue, or acceptance profile. Detectors should compare the receiving component’s declared input question with the sending component’s output question, verify that required qualifiers remain present, and reject unexplained promotion. A mismatch produces a typed failure record containing the last valid artifact, the bridge involved, and the unmet condition. It does not produce a best-effort legal conclusion.

**DERIVED.** Cross-component cycles require special detection because they can manufacture apparent corroboration. Suppose an analogy module ranks a precedent using facts inferred from an argumentation result, while the argumentation graph treats that ranking as independent support for the same facts. Repetition then masquerades as confirmation. Dependency tracking should identify shared source ancestry and return a double-counting or circular-support status. Recovery breaks the cycle at the earliest unsupported bridge, restores the last acyclic version, and reruns only the dependent branches.

**DERIVED.** Recovery must distinguish correction from reconsideration. Correction repairs an invalid translation, missing provenance link, malformed time anchor, or misidentified authority. It invalidates dependent outputs and replays them from the repaired artifact. Reconsideration adds newly admitted evidence or an authorized policy change. It creates a new version while preserving the earlier result and its then-operative premises. This distinction prevents a later preference from being presented as though the earlier computation had never occurred, and it supports faithful appellate or audit reconstruction.

**DERIVED.** Unresolved legal judgment is a stopping condition with a pr
68,876
oductive output. When applicability, burden allocation, material similarity, or institutional authority cannot be derived from supplied sources, the system should emit a bounded question for an authorized reviewer. The response becomes a new input with named scope. If no response is available, affected branches remain unresolved while independent branches continue. Recovery therefore means restoring valid computation and routing necessary judgment, not coercing every case into a binary result.

### 8.4 Worked Case: Emergency Closure and a Delivery Penalty

**DERIVED.** Consider a hypothetical municipal supply contract requiring delivery by 20 March and written notice of force majeure within five business days after the impediment begins. A port closure operates from 10 through 18 March. The supplier delivers on 24 March and asserts that an email sent on 17 March gave notice. The agency’s portal records no submission, but the supplier produces a mail-server log. An emergency amendment effective 15 March suspends portal-dependent notice periods during verified outages. The legal question is whether the agency may impose the contractual delay penalty.

**DERIVED.** Intake separates admitted, disputed, and authoritative materials. The signed contract, delivery dates, closure order, amendment text, and portal outage record are source-bound artifacts. The authenticity and legal sufficiency of the email remain disputed. A monotone rule component derives only prima facie support: the delivery deadline passed before performance, and the penalty clause is triggered if no valid excuse applies. It does not derive that the penalty is finally payable because the exception and notice conditions have not been resolved.

**DERIVED.** A default component represents the ordinary inference that unexplained late delivery attracts the penalty, with force majeure as a defeating condition. The port closure supports an excuse, but the notice dispute prevents immediate settlement. Structured arguments then expose the contest. The agency argues late performance and missing portal submission. The supplier answers with the closure, server log, and emergency suspension. The agency challenges the log’s authenticity and contends that the amendment does not govern a period that began on 10 March. Preference rules cannot resolve those challenges unless their legal source and scope are supplied.

**DERIVED.** Temporal evaluation prevents two shortcuts. First, it asks whether the five-business-day period had expired before the amendment took effect, applying the contract’s calendar rule rather than ordinary elapsed days. Second, it distinguishes the closure’s start, the email’s alleged transmission, the amendment’s effective time, and the later delivery. If the notice period remained open on 15 March and the amendment covered existing periods, suspension may matter. If either premise is unresolved, the temporal component returns conditional branches rather than selecting an interpretation.

**CONJECTURE.** An analogy component may rank a prior appellate decision in which server logs proved timely submission during an agency outage. The case is useful only if the same issue, comparable filing mechanism, and adequate authority are established [@BenchCaponSartor2003; @Horty2011]. It enters as a candidate for legal review, accompanied by distinctions: the precedent involved a statutory appeal, while the present notice arises under contract. A Bayesian model may separately estimate the probability that the email was sent, using log reliability and outage evidence [@FentonNeilLagnado2013]. That estimate does not decide legal sufficiency or burden.

**DERIVED.** The argument graph now contains at least two outcome branches. In the first, an authorized fact finder accepts the server log, and an authorized legal interpretation applies the amendment to the still-open notice period. The force-majeure defense defeats the penalty argument, subject to any causation requirement. In the second, authenticity remains unproved under the applicable burden rule, or the amendment is held prospective only. The notice defense fails, and the penalty argument survives unless another excuse applies. The graph records why the branches diverge rather than averaging them.

**DERIVED.** Procedure completes the case. Before assessment, the system checks whether the contract officer has authority, whether the supplier received an opportunity to contest authenticity, and whether the controlling texts and evidence are admissible for that stage. If a necessary legal interpretation has not been authorized, the output is a decision packet presenting both branches and the precise unresolved question. If authorization and findings are supplied, the selected branch is recorded with its sources, defeated alternatives, time anchors, and burden rule. The result is complete as a traceable legal recommendation, not as proof that the recommendation is legally correct.

### 8.5 Counterexamples to Naive Composition

**DERIVED.** Duplicate-source amplification defeats apparently modular corroboration. A witness statement supports a fact extractor, which supplies a Bayesian likelihood and also generates an argument. If a later aggregator treats the probability and argument as independent evidence, the same statement counts twice. Provenance preservation alone detects the shared ancestor only if the evaluation checks dependence. The proper response is to model the correlation or retain separate, nonadditive assessments. Two pipelines do not create two sources.

**DERIVED.** Exception flattening produces a different error. A default that tenants usually occupy their registered residence is exported as an unconditional Horn fact. A later argument based on hospital records cannot retract it because the translation erased the default’s justification and defeating condition. The final contradiction appears to be a dispute between equal facts, although one side was never categorical. Recovery requires returning to the lossy bridge, restoring provisional status, and rebuilding downstream attacks. Adding a priority after the fact merely conceals the corrupted premise.

**DERIVED.** Semantic-profile laundering occurs when credulous acceptance under one argumentation semantics is exported simply as “accepted,” then consumed by a procedure requiring skeptical support. The graph may contain mutually exclusive extensions, so the exported claim lacks the stability the procedure assumes [@Dung1995]. No malformed data exposes the error. A profile-aware detector must compare the source acceptance mode with the receiving threshold. If the threshold is unmet, recovery preserves the claim as a contested branch rather than deleting it or upgrading it.

### 8.6 Evaluation Implications

**CONJECTURE.** Evaluation should use paired perturbations that preserve surface plausibility while changing one semantic dimension. Examples include substituting an expired norm, adding an undefeated exception, changing skeptical acceptance to credulous acceptance, shifting an event across an effective date, duplicating a source through two modules, or withholding the rule that allocates a burden. A suitable system should change only outputs dependent on that dimension and should identify the responsible bridge. Ordinary answer accuracy cannot reveal whether the right result arose from the wrong semantics.

**DERIVED.** Metrics should separate detection, containment, recovery, and explanation. Detection measures whether the system identifies the injected conflict. Containment measures whether unaffected branches remain usable without allowing tainted artifacts to advance. Recovery measures whether correction or authorized reconsideration produces the expected new version without rewriting history. Explanation measures whether reviewers can locate the premise, policy, and bridge responsible for the change. These measures operationalize compositional discipline more directly than a single end-to-end score.

**CONJECTURE.** Human evaluation should assign reviewers both ordinary files and adversarially altered files, with the alteration hidden but ethically disclosed at study level. Outcomes should include decision time, missed blockers, unwarranted certainty, successful challenge reconstruction, and disagreement about the legally material issue. Reviewers should also indicate whether the system presented a question they were institutionally entitled to answer. Stratification by legal experience can reveal whether explicit semantic boundaries aid novices, experts, or both.

**DERIVED.** Reproducibility requires freezing the case materials, bridge policies, semantic profiles, temporal interpretation inputs, probability model, and procedure configuration for each run. Reported success should be tied to that bundle and to the tested perturbations. A passing run establishes behavior on those cases, not universal legal correctness, complete argument construction, or formal verification. The strongest evaluation claim available from this design is narrower: under disclosed conditions, the composition detected specified category errors, contained their propagation, and preserved reviewable alternatives.

## 9. Evidence Ledger

| Claim | Status | Evidence | Exclusion |
|---|---|---|---|
| Finite Horn support has least-fixed-point semantics | DERIVED and FORMALIZED only for matching repository definitions | [@Horn1951; @Tarski1955] and named Lean artifacts | Truth of premises |
| Defeasible acceptance may retract | DERIVED | [@Reiter1980; @AntoniouEtAl2001] | Correct exception policy |
| Dung profiles produce semantics-relative acceptance | DERIVED and bounded FORMALIZED where audited | [@Dung1995] | Completeness of arguments |
| Probability can organize evidence | CONJECTURE | [@FentonNeilLagnado2013; @VlekEtAl2015] | Legal proof standard |
| Typed composition improves review | CONJECTURE | Proposed evaluation | Present empirical validation |

## 10. Verification Boundary

**FORMALIZED.** Only named, elaborated declarations and their audited assumptions support formalized claims. A build, test, receipt, or narrative label alone is not a proof.

**DERIVED.** No kernel establishes the governing law, accepted facts, relevance weights, priors, complete case corpus, or institutional authority. Those are explicit inputs or unresolved questions.

**DERIVED.** Runtime receipts can bind an external execution to a subject and fixture. They demonstrate that run, not semantic equivalence for all inputs.

## 11. Limitations

**DERIVED.** The architecture increases explicit modeling work and may not capture holistic legal judgment. Local correctness does not guarantee complete composition. Jurisdictional variation limits reusable authority and procedure models.

**CONJECTURE.** Future work should formally prove additional bridge invariants, empirically test reviewer outcomes, and study failure under incomplete sources. Expansion must not weaken the boundary between proposal and judgment.

## 12. Declarations

### Funding

No external funding was received.

### Conflict of Interest

The author declares no conflict of interest.

### Data Availability

No personal or confidential data were used. Public repository artifacts provide technical context; no empirical dataset is claimed.

### Ethics

No human participants or personal data were involved. Future user studies require ethics review.

### Author Contributions (CRediT)

Laupinco: Conceptualization, Methodology, Formal analysis, Investigation, Writing—original draft, Writing—review and editing, Project administration.

### AI Usage Disclosure

Generative AI assisted language drafting and structural editing. The author controlled sources, formulas, status labels, and legal boundaries and remains responsible for the manuscript.

## References

Cited works are in the shared bibliography: [@Horn1951; @Tarski1955; @Reiter1980; @McCarthy1980; @AntoniouEtAl2001; @Maher2001; @Dung1995; @PrakkenSartor1997; @ModgilPrakken2013; @RisslandAshley1987; @BenchCaponSartor2003; @Horty2011; @Pnueli1977; @ClarkeEtAl1986; @Kripke1963; @FentonNeilLagnado2013; @VlekEtAl2015; @FentonNeilBerger2016].
