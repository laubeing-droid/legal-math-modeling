# Legal Analogy as Constrained Comparison

**Author:** Laupinco

## Abstract

Legal analogy is neither nearest-neighbor classification nor deduction from a fixed rule. It compares a current dispute with precedents through legally characterized factors, competing reasons, authority, and values, while preserving the possibility of distinction. This paper proposes a formal architecture for auditable analogical reasoning. Cases are typed bundles of findings rather than raw documents; similarity is a vector, not a scalar fact; precedential support depends on both relevant commonality and legally significant difference; and every proposed analogy remains open to counterargument. The model defines factor incidence, directional similarity, authority weighting, value-sensitive defeat, a fortiori support, distinction cost, precedent aggregation, stability, and explanation sufficiency in more than ten displayed equations. These definitions are analytical and are not Lean theorems. The repository may formally establish selected structural invariants, but it does not prove that a case is legally analogous, that a factor is relevant, or that an outcome is correct. Those judgments require authoritative legal input.

## 中文摘要

本文把法律类比建模为受约束的比较，而非文本相似度或最近邻预测。案件首先被表示为经法律确认的因素、理由、价值与裁判结果；类比强度区分有利共同点、不利共同点、可区分差异、法院层级与时间；反方可以通过指出关键差异或竞争先例攻击类比。全部公式属于分析性推导或待验证模型，现有 Lean 证明不证明具体案件相似、因素相关或裁判正确。机器负责保留比较路径与反对意见，有权限的人类法律主体负责确定法源、事实、相关性与先例效力。

**Keywords:** legal analogy; precedent; case-based reasoning; factors; argumentation; formal verification

**关键词：** 法律类比；先例；案例推理；因素；论证；形式验证

## 1. Research Questions and Epistemic Labels

The paper asks: How can a system represent legal comparison without treating lexical proximity as legal similarity? How can it expose distinctions and conflicting precedents? Which invariants are machine-checkable, and which inputs require legal authority?

**FORMALIZED** is reserved for propositions actually proved over identified repository definitions. **DERIVED** marks consequences of definitions in this paper. **CONJECTURE** marks empirical or normative hypotheses. No formula below proves the legally correct analogy in a real dispute.

## 2. Related Work

**DERIVED.** HYPO modeled adversarial reasoning with dimensions, precedents, distinctions, and hypotheticals [@RisslandAshley1987]. Later theory connected cases, rules, and social values [@BenchCaponSartor2003]. Value-based and preference-sensitive argumentation explain how audiences can disagree rationally [@BenchCapon2003; @ModgilPrakken2013]. Horty's reason model treats precedent as a constraint on priorities among reasons [@Horty2011]. Teitelbaum supplies a formal and empirical weighted model of analogical influence [@Teitelbaum2015]. These sources reject the idea that surface resemblance alone determines outcome.

**DERIVED.** Abstract argumentation provides a neutral attack-and-defense layer [@Dung1995]. Defeasible systems explain how conclusions can be withdrawn when exceptions or superior reasons appear [@PrakkenSartor1997; @Reiter1980]. The present proposal uses these structures as an audit language, not as judicial authority.

## 3. Case Representation

Let a case be

\[
c=(j,t,F^+,F^-,I,O,V,S),
\tag{1}
\]

where (j) is jurisdiction and court, (t) decision time, (F^+) and (F^-) factors favoring opposing outcomes, (I) issues, (O) holdings or outcomes, (V) values, and (S) sources.

**DERIVED.** Factor incidence is ternary:

\[
\phi(c,f)\in\{1,0,?\},
\tag{2}
\]

where unknown is not absence. A factor enters comparison only if its factual and legal characterization is source-bound.

**DERIVED.** The current problem (p) and precedent (c) are comparable on issue (i) only if

\[
\operatorname{Comp}(p,c,i)=
\operatorname{SameIssue}(p,c,i)\land
\operatorname{CompatibleLaw}(p,c,i)\land
\neg\operatorname{Overruled}(c,i).
\tag{3}
\]

Compatibility and overruling are legal inputs, not text-mining outputs.

## 4. Directional Similarity

**DERIVED.** Shared factors are partitioned by the side they support:

\[
S_y(p,c)=\{f\mid\phi(p,f)=\phi(c,f)=1
\land\operatorname{favours}(f)=y\}.
\tag{4}
\]

Differences are also directional:

\[
D_y(p,c)=\{f\mid\phi(p,f)\neq\phi(c,f),
\operatorname{favours}(f)=y\}.
\tag{5}
\]

**CONJECTURE.** An auditable similarity score may be

\[
\operatorname{sim}_y(p,c)=
\sum_{f\in S_y}w_f-
\sum_{f\in D_{\neg y}}v_f,
\quad w_f,v_f\ge0.
\tag{6}
\]

Weights must be justified from legal authority or empirical design. Learned weights do not become legal relevance.

**DERIVED.** Symmetry is not required:

\[
\operatorname{sim}_y(p,c)\neq
\operatorname{sim}_y(c,p),
\tag{7}
\]

because the precedent constrains a later case and the direction of missing or added factors can matter.

## 5. Authority, Time, and Values

**DERIVED.** Precedential authority is kept separate:

\[
A_j(c,i,t)\in\{0,\alpha,1,?\},
\tag{8}
\]

representing none, persuasive, binding, or unresolved authority. The parameter $\alpha$ is contextual, not universal.

**CONJECTURE.** For empirical ranking, temporal attenuation may be

\[
T(c,p)=e^{-\lambda(t_p-t_c)},\qquad\lambda\ge0,
\tag{9}
\]

but binding authority cannot be discounted merely for age. Equation (9) is appropriate only where legal doctrine permits time to affect persuasive weight.

**DERIVED.** A value-based defeat relation follows Bench-Capon's insight:

\[
a\triangleright_{\pi}b
\iff a\to b\land
\neg(\operatorname{val}(b)\succ_{\pi}\operatorname{val}(a)),
\tag{10}
\]

where $\pi$ is an authorized or explicitly hypothetical value ordering [@BenchCapon2003].

## 6. A Fortiori Support and Distinction

**DERIVED.** A precedent supporting (y) provides an a fortiori argument when the current case contains all known pro-(y) factors and no additional known anti-(y) factor:

\[
F_y(c)\subseteq F_y(p)
\land F_{\neg y}(p)\subseteq F_{\neg y}(c)
\Rightarrow c\preceq_y p.
\tag{11}
\]

This formal ordering is conditional on factor completeness and relevance.

**DERIVED.** A distinction witness is a factor (d) satisfying

\[
d\in D(p,c)\land
\operatorname{material}(d,i)=1
\land\operatorname{changesReasonBalance}(d)=1.
\tag{12}
\]

Materiality and balance are legal judgments. The system can display their sources and opponents.

**CONJECTURE.** A transparent distinction score is

\[
\operatorname{Dist}(p,c)=
\sum_{d\in D(p,c)}m_dv_d,
\tag{13}
\]

with disclosed materiality (m_d) and weight (v_d). It prioritizes review; it does not decide whether a court may distinguish.

## 7. Multiple Precedents and Conflict

**CONJECTURE.** Candidate support for outcome (y) can be ranked by

\[
W_y(p)=\sum_{c\in C_y}
A_j(c)T(c,p)\operatorname{sim}_y(p,c)
-\sum_{c\in C_{\neg y}}A_j(c)T(c,p)\operatorname{sim}_{\neg y}(p,c).
\tag{14}
\]

This is an empirical decision-support score, not a holding.

**DERIVED.** Conflicts must remain visible:

\[
\operatorname{Conflict}(p)=
\{(c_1,c_2)\mid O(c_1)\neq O(c_2),
\operatorname{Comp}(p,c_1)=\operatorname{Comp}(p,c_2)=1\}.
\tag{15}
\]

The set cannot be removed merely because one precedent receives a higher score.

**CONJECTURE.** Stability under plausible weights measures sensitivity:

\[
\operatorname{Stab}(y)=
\Pr_{w\sim\mathcal W}
[y=\arg\max_z W_z^{(w)}(p)].
\tag{16}
\]

The distribution $\mathcal W$ must be disclosed. Stability is not correctness.

## 8. Argumentation and Explanation

**DERIVED.** Construct an argument (a_c) for each precedent analogy and (d_{c,k}) for each distinction. The attack graph is

\[
AF_p=(Arg_p,Att_p),
\qquad(d_{c,k},a_c)\in Att_p.
\tag{17}
\]

Other precedents, exceptions, and authority challenges may also attack.

**DERIVED.** An explanation for a recommended analogy is sufficient only if it contains the precedent, shared factors, differences, authority, outcome, value assumptions, attacks, and source status:

\[
E(a_c)\supseteq
\{c,S(p,c),D(p,c),A_j(c),O(c),V(c),Att(a_c),S_c\}.
\tag{18}
\]

Fluent prose that omits a material distinction fails this contract.

**FORMALIZED.** Repository theorems may prove selected graph, compiler, or closure invariants for encoded structures. No existing proof is claimed to establish the factor sets, weights, authority values, or outcomes in Equations (1)--(18).

## 9. Analysis and Worked Example

**DERIVED.** Suppose precedent (c_1) grants relief where confidential information, restricted access, and unauthorized acquisition are established. Problem (p) shares confidentiality and unauthorized acquisition but lacks a confirmed access restriction; it also adds independent development. A lexical system may rank (c_1) highly. The typed model records two differences, one unknown and one favoring the opposing party. The proponent cites shared factors and authority; the opponent offers distinction arguments. Unknown access restriction cannot be treated as absent or satisfied.

**DERIVED.** If a second precedent (c_2) denies relief where independent development is established, the system adds a conflicting analogy. It may calculate sensitivity under alternative relevance weights, but must not hide (c_2). An authorized lawyer or court determines whether the cases share the governing issue, whether independent development is material, and which precedent controls.

**CONJECTURE.** Evaluation should compare four systems: text retrieval, untyped factor scoring, typed analogy without attacks, and the full contestable model. Outcomes should include precedent recall, material-distinction recall, source accuracy, user comprehension, calibration, and time. Agreement with historical outcomes is not enough because historical decisions may be contested and datasets may encode selection bias.

## 10. Evidence Ledger

### 9.1 Counterexamples to Naive Similarity

**DERIVED.** Counterexample one is lexical similarity without issue identity. Two opinions may use the same vocabulary of consent, notice, and reliance while addressing different causes of action or procedural questions. A text embedding can place them close together even though one decision cannot support the proposition for which the other is cited. Equation (3) therefore precedes similarity scoring. Issue compatibility is a legal gate, not another small feature weight.

**DERIVED.** Counterexample two is factual similarity with reversed legal significance. The same fact can favor different parties under different doctrines. Secrecy efforts may support protection of information in one dispute and support notice or control in another. A bag-of-factors representation that ignores the `favours` relation in Equations (4)--(5) treats shared words as shared reasons. Directional typing prevents that particular error.

**DERIVED.** Counterexample three is the dominant distinction. Suppose a problem shares nine factors with a precedent, but differs on a jurisdictionally required element. A Jaccard score can be extremely high while the analogy fails at a threshold issue. Materiality cannot be recovered by counting. Equation (12) gives a single legally decisive distinction the capacity to attack an otherwise strong analogy.

**DERIVED.** Counterexample four is authority inversion. A recent lower-court decision may be textually and factually closer than an older binding decision. A ranking that folds authority into an opaque learned score may return the recent case first and encourage an invalid inference. Equation (8) keeps authority visible and permits a hard applicability constraint where the legal system requires it.

**DERIVED.** Counterexample five is outcome leakage. A model trained to predict holdings may learn that particular factors correlate with the winner, then present those correlations as reasons why the party should win. Predictive association becomes a circular explanation of legal significance. The architecture avoids this by requiring the factor-to-reason and reason-to-outcome links to have sources independent of the predicted label.

**DERIVED.** Counterexample six is hidden conflict. A system presents the closest supporting case but omits an equally comparable opposing precedent. The selected analogy may be accurate in isolation, yet the explanation is misleading as a representation of the available legal landscape. Equation (15) requires compatible conflicting precedents to remain visible even when ranking selects one candidate.

**CONJECTURE.** These counterexamples predict that pure retrieval accuracy will correlate only weakly with legally adequate analogical assistance. Systems should be tested on issue mismatch, decisive distinction, authority conflict, and adverse-precedent mutations, not only on whether they retrieve cases cited by a reference opinion.

### 9.2 Propositions and Design Consequences

**DERIVED. Proposition 1 (Gate-before-score).** If comparability is false, multiplying a similarity score by a small authority or issue weight does not repair the analogy. A nonzero score still invites ranking and may be presented as support. Hard incompatibilities therefore operate as gates, while graded considerations operate as weights. The distinction between a gate and a weight is part of the legal model and must be explicit.

**DERIVED. Proposition 2 (Unknown non-equivalence).** For a material factor (f), (phi(p,f)=?) is not equivalent to (phi(p,f)=0). If unknown is coerced to absence, an a fortiori comparison under Equation (11) may be triggered incorrectly. The safe output is a conditional analogy: the precedent supports the result if the unresolved factor receives a stated characterization.

**DERIVED. Proposition 3 (More shared factors need not strengthen support).** Adding a shared factor can weaken an analogy when that factor activates a competing doctrine, changes issue characterization, or supplies an exception. Monotonicity holds only inside a frozen factor language with fixed directional relevance and no rule interaction. Real legal analogy cannot assume that background without authorized modeling.

**DERIVED. Proposition 4 (Authority and similarity are non-compensatory in binding systems).** If a binding precedent controls an issue, many weakly authoritative similar cases cannot numerically outweigh it merely by accumulation. Equation (14) is therefore appropriate only after the system's authority rules determine whether aggregation is permitted. A general summation formula cannot encode every doctrine of precedent.

**DERIVED. Proposition 5 (Distinguishing is an argument, not a distance).** Distance identifies difference. Distinguishing asserts that a difference is legally material to the precedent's reason or holding. The latter requires a warrant and can be attacked. A user interface should never label the largest numeric difference “the distinction” without showing the materiality claim.

**DERIVED. Proposition 6 (Stable prediction can coexist with unstable reasons).** Alternative weight settings may yield the same winning outcome while selecting different decisive precedents and values. Outcome stability under Equation (16) does not imply explanatory stability. Evaluation must compare both result and reason structure.

**CONJECTURE.** These propositions can be implemented as schema and mutation gates. Tests can change an unknown factor to false, insert a binding adverse precedent, or add a material distinction and require an observable change in the candidate argument. Passing the tests would establish behavior for the fixtures, not universal legal adequacy.

### 9.3 A Typed Construction Pipeline

**DERIVED.** Stage one is source acquisition. The system stores the authoritative case text or an admissible surrogate, citation, court, date, procedural posture, subsequent treatment, and acquisition method. A case identifier without the underlying source is a locator, not verified legal content. Later stages may operate provisionally but must preserve that status.

**DERIVED.** Stage two is issue segmentation. A judgment can decide several questions, and a holding on one issue cannot be transferred automatically to another. Each extracted proposition is linked to the passages and procedural context that support it. Human legal review confirms or disputes the issue mapping.

**DERIVED.** Stage three is factor annotation. Annotators record the underlying factual proposition, its evidential status, the legal factor it is said to instantiate, the side or value it favors, and the source for that characterization. Disagreement produces parallel annotations rather than a silently resolved label. Inter-annotator agreement is reported by field because agreement on fact extraction does not imply agreement on legal relevance.

**DERIVED.** Stage four constructs candidate analogies. The system applies comparability gates, derives shared and differing factor sets, and retrieves supporting and opposing precedents. It does not yet choose a legal result. Candidate generation should favor recall because later attack construction needs adverse material.

**DERIVED.** Stage five constructs arguments. A supporting argument identifies the precedent, issue, outcome, common factors, authority, and warrant connecting the commonality to the proposed treatment. A distinction identifies a difference and a warrant for materiality. Competing precedents attack through inconsistent treatment or incompatible priorities. Authority challenges and later negative treatment attack the availability or weight of a precedent.

**DERIVED.** Stage six computes only declared semantics. If a Dung-style grounded extension is used, the output means accepted under that abstract attack graph and semantics [@Dung1995]. If a value-based audience is used, acceptance is relative to its ordering [@BenchCapon2003]. The interface states those qualifiers instead of saying that an argument “is legally valid.”

**DERIVED.** Stage seven renders a contestable explanation using Equation (18). The output states which inputs were legally reviewed, which were computationally extracted, which remain disputed, and which result from a hypothetical value order. Users can expand every factor to its source and every defeat to its warrant.

**DERIVED.** Stage eight records human action. A lawyer or judge may accept, reject, modify, or ignore the candidate analogy. The record distinguishes agreement with the system's result from agreement with its reasons. The institutional decision does not retroactively validate every intermediate model claim.

### 9.4 Evaluation Protocol

**DERIVED.** A useful benchmark must freeze more than outcomes. For each problem, it should identify the relevant issue, candidate precedent pool, authority relations, known supporting and distinguishing factors, adverse authorities, and annotation disagreements. Without that reference, a system can retrieve the recorded outcome for the wrong reason and receive full credit.

**DERIVED.** Retrieval is evaluated with issue-conditioned recall. A retrieved case counts only for the issue and proposition for which it is legally relevant. Separate measures report supporting-precedent recall, adverse-precedent recall, and overruled-or-inapplicable citation rate. These errors have different legal consequences and should not be averaged into one top-(k) score.

**DERIVED.** Factor quality is evaluated at three layers: source-span accuracy, factual characterization, and legal-direction annotation. A system can copy the correct sentence but assign the wrong factor, or assign the right factor to the wrong side. Error analysis must retain these distinctions.

**DERIVED.** Argument quality is evaluated by warrant completeness, material-distinction recall, authority accuracy, and attack coverage. A candidate with many supporting similarities but no response to a known decisive distinction is incomplete. Expert reviewers should be able to add a missing attack, and the system should recompute without deleting the original record.

**CONJECTURE.** Prospective evaluation should measure professional action rather than historical outcome agreement alone. Participants can be asked to select additional evidence, identify a controlling authority, formulate a distinction, or revise a draft argument. The hypothesis is that contestable factor graphs improve issue spotting and adverse-authority detection, while possibly increasing review time.

**CONJECTURE.** Robustness tests vary factor granularity. A broad factor such as “reasonable security efforts” may hide several narrow factors with opposing implications. The system should report when its recommendation changes under plausible decompositions. Sensitivity is evidence of model dependence, not a reason to choose the decomposition that produces a preferred result.

**DERIVED.** Temporal testing uses historical cutoffs. A system evaluating a dispute at time (t) must not use cases or negative treatment published after (t), except in a clearly labeled retrospective analysis. This prevents information leakage and permits honest evaluation of what assistance was available at the relevant time.

**DERIVED.** Cross-jurisdiction testing keeps authority rules separate. A case from another jurisdiction may be persuasive comparative material but cannot inherit the authority value assigned in its origin system. Researchers should report performance within each jurisdiction before pooling.

### 9.5 Extended Worked Analysis

**DERIVED.** Return to the trade-secret-style example. Assume the problem contains confirmed confidentiality, commercial value, and acquisition by a former collaborator. Restricted access is disputed, independent development is asserted, and the alleged disclosure occurred after a contractual relationship ended. Precedent (c_1) favors protection on confidentiality, restricted access, and unauthorized acquisition. Precedent (c_2) denies relief where independent development is well documented. Precedent (c_3) concerns confidentiality but a different issue: enforceability of a contractual clause.

**DERIVED.** Equation (3) excludes (c_3) from direct support on the misappropriation issue while permitting it to appear in a separate contractual analysis. Equations (4)--(5) show that (c_1) shares two favorable factors but differs on restricted access and independent development. The system creates two distinction candidates rather than subtracting anonymous distance points.

**DERIVED.** The unknown access factor produces conditional branches. In branch (b_1), restricted access is established; in (b_2), it is not; in (b_3), the decision remains unresolved. Each branch reuses the same source graph while changing only the declared premise. The interface does not report the most favorable branch as the answer.

**DERIVED.** If (c_2) has lower authority but addresses independent development directly, it remains an adverse analogy. A legal reviewer may conclude that (c_1) controls, distinguish (c_2), or treat the conflict as unresolved. The system records the warrant and source for that action. It does not learn a permanent weight from one review without a governance decision.

**CONJECTURE.** Generating hypotheticals can expose the boundary. The system asks how the argument changes if independent-development records are dated before acquisition, if access controls were merely nominal, or if the collaborator retained authorized access. Useful hypotheticals modify legally characterized factors one at a time. Unconstrained language generation may invent facts and is therefore unsuitable as the authoritative case representation.

**DERIVED.** The example shows why an analogy score is subordinate to an argument object. The score can prioritize candidates, while the object supplies sources, shared reasons, differences, attacks, authority, and uncertainty. A reviewer can reject the numeric weighting yet still use the structured comparison.

### 9.6 Governance Implications

**DERIVED.** Factor vocabularies are governed legal artifacts. Adding, merging, or redefining a factor changes the comparison space and may alter past results. Every vocabulary release requires version identity, rationale, affected cases, reviewer, and migration policy. Historical analyses retain the version used at the time.

**DERIVED.** Training data cannot be treated as neutral merely because cases are public. Publication practices, appeal rates, settlement, legal representation, and reporting conventions shape the observable corpus. Evaluation should describe selection and avoid translating historical frequency directly into normative weight.

**DERIVED.** Users need an appeal path for annotations and mappings. A challenge may concern source accuracy, factor presence, direction, materiality, issue identity, authority, or value ordering. Those challenge types route to different reviewers. A generic thumbs-down control is not adequate contestability.

**CONJECTURE.** An independent audit can sample high-influence precedents, decisive distinctions, and unresolved factors. Risk-based sampling may outperform uniform review, but it can miss systematic low-score exclusions. Audit reports should disclose the sampling rule and retain a random component.

**DERIVED.** The model's central governance rule is separation of proposal from decision. Retrieval proposes cases; annotation proposes factors; scoring proposes priority; argumentation proposes acceptability under declared semantics; a legally authorized actor decides what, if anything, those proposals establish. Preserving that sequence is more important than maximizing automation.

**DERIVED.** Publication should include negative retrieval evidence. If a search found no controlling case, the report states databases, jurisdictions, dates, queries, filters, and cutoff time. “No case found” is not “no case exists.” This distinction matters when a novel analogy is justified partly by an asserted absence of precedent.

**DERIVED.** Citation integrity is another boundary. A quoted proposition must resolve to the cited page and must not exceed the scope of the holding or reasoning used. Headnotes, summaries, embeddings, and generated descriptions are locators or aids until checked against the authoritative source. A citation verifier can detect missing identifiers and textual mismatch; legal reviewers still decide whether the proposition is dictum, holding, distinguishable reasoning, or obsolete law.

**CONJECTURE.** Governance should monitor asymmetric error. Missing an adverse binding precedent is generally more serious than returning an additional weakly relevant supporting case. Benchmarks can attach different reporting weights to these errors, but the choice must be justified by the deployment context. The system should publish the unweighted counts alongside any weighted score so that policy choices remain visible.

**DERIVED.** When the model cannot resolve a gate, it produces a research task rather than a recommendation. Examples include uncertain subsequent treatment, ambiguous issue identity, disputed factor characterization, or unavailable source text. Routing uncertainty to research is a productive output. Forcing every problem into a ranked result manufactures precision and weakens the evidence ledger.

**DERIVED.** Finally, auditability requires stable identifiers for cases, issues, factors, arguments, and sources. Human-readable names may change; stable identifiers preserve links across corrections. Identity is an engineering property, not evidence that two legal concepts are substantively equivalent. Merging identifiers requires an explicit reviewed mapping, while splitting a factor requires a migration record showing which earlier comparisons are affected.

| Claim | Status | Evidence | Does not establish |
|---|---|---|---|
| Legal analogy uses similarities and distinctions | DERIVED | HYPO and case theory [@RisslandAshley1987; @BenchCaponSartor2003] | A universal legal test |
| Values can parameterize defeat | DERIVED | [@BenchCapon2003; @ModgilPrakken2013] | Correct social value order |
| Precedent constrains reason priorities | DERIVED | [@Horty2011] | Applicability in every jurisdiction |
| Weighted analogy can be studied empirically | CONJECTURE | [@Teitelbaum2015], Equations (6), (14), (16) | Legal correctness |
| Attack graphs expose distinctions | DERIVED | [@Dung1995], Equation (17) | Exhaustiveness of collected attacks |
| Selected structural invariants can be machine-proved | FORMALIZED only where repository theorem evidence matches | Lean source and certificate | Case similarity or lawful outcome |

## 11. Verification Boundary

**FORMALIZED.** A proof assistant can establish properties of the encoded comparison operator, such as monotonicity under stated factor additions, closure termination on finite sets, or preservation by a compiler. It proves the proposition represented, under explicit premises.

**DERIVED.** It cannot establish that a judicial statement is controlling law, that a factual characterization is true, that two legal issues are compatible, or that a value ordering is legitimate unless those propositions are provided as premises. Doing so would move legal judgment into unverified input while leaving a misleading aura of proof.

**DERIVED.** Runtime fixtures can show that examples execute and receipts bind to versions. Mutation tests can show that selected perturbations are detected. Neither is proof that the analogy is legally acceptable.

## 12. Limitations

**DERIVED.** Factor representation can oversimplify narrative and institutional context. Different jurisdictions assign different force to precedent. Published cases are a selected sample, and outcome labels can hide procedural posture.

**DERIVED.** Weight learning risks circularity: training on outcomes may reproduce historical decisions and then present reproduction as a normative reason. Unknown and disputed factors require explicit treatment.

**CONJECTURE.** Cross-jurisdiction studies, adversarial factor annotation, inter-rater analysis, and prospective evaluation are needed before operational use. No empirical validation is reported here.

## 13. Declarations

### Funding

This research received no external funding.

### Conflict of Interest

The author declares no conflict of interest.

### Data Availability

No case dataset or personal data were used. Public repository sources provide the technical context; cited publications are available through their publishers.

### Ethics

No human participants or personal data were involved. Future user or case studies require ethics, confidentiality, and lawful-data review.

### Author Contributions (CRediT)

Laupinco: Conceptualization, Methodology, Formal analysis, Investigation, Writing—original draft, Writing—review and editing, Project administration.

### AI Usage Disclosure

Generative AI assisted language drafting and structural editing. The author controlled sources, formulas, claim labels, and legal boundaries and remains responsible for the manuscript. Generated text was not treated as law, evidence, or proof.

## References

Cited works are in the shared bibliography: [@RisslandAshley1987; @BenchCaponSartor2003; @BenchCapon2003; @ModgilPrakken2013; @Horty2011; @Teitelbaum2015; @Dung1995; @PrakkenSartor1997; @Reiter1980].
