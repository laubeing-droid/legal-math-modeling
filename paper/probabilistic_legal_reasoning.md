# Probabilistic Legal Reasoning Under a Formal Interface Boundary

**Author:** Laupinco

## Abstract

**DERIVED.** Probabilistic reasoning can clarify how uncertain evidence bears on competing factual hypotheses, but mathematical validity does not by itself establish evidentiary admissibility, discharge a burden of proof, determine a legal standard, or authorize judgment. This paper develops a bounded model in which priors, likelihoods, posterior distributions, source dependence, and model uncertainty are explicit assumptions rather than hidden features of a formal legal system. The formal interface considered here is deliberately narrow: in Lean, `EdgeKind.probabilityKernel` creates baseline obligations, including `observationDeclaration`, through `ULM04.requiredObligations`; `requiredObligations_nonempty` and the request, failure, trust, and authority interface theorems establish structural properties of that interface. They do not formalize probability measures, Bayesian updating, calibration, legal proof thresholds, or probabilistic inference. A complete hypothetical dispute involving service and filing documents demonstrates how likelihoods differ from posterior probabilities, how dependent records can be double counted, and how source and model uncertainty alter conclusions. Counterexamples expose base-rate neglect, omitted hypotheses, and apparently strong but correlated evidence. The proposed evaluation protocol combines calibration analysis, proper scoring rules, dependence stress tests, and a human-maintained evidence ledger. The result is an architecture in which probabilistic assessment remains revisable and empirically testable while admissibility, burdens, standards of proof, and final legal judgment remain separate normative operations.

## 中文摘要

**DERIVED.** 概率推理可以说明不确定证据如何改变若干竞争性事实假设的相对可信度，但数学上的后验概率并不自动等同于证据可采性、举证责任履行、证明标准满足或裁判结论。本文提出一个受严格接口边界约束的模型：先验、似然、条件依赖、来源可靠性与模型不确定性均作为显式假设处理，而不冒充形式系统已经证明的语义。Lean 仓库中的 `EdgeKind.probabilityKernel` 仅通过 `ULM04.requiredObligations` 产生包括 `observationDeclaration` 在内的基线义务；相关非空性以及请求、失败、信任和权限接口定理只证明结构性接口性质，不证明概率测度、贝叶斯定理、校准、法律证明门槛或概率化法律推断。本文以虚构的送达与提交争议为完整案例，展示两个具有共同来源的文件如何造成重复计数，并通过竞争假设、来源不确定性、模型平均与敏感性分析修正过度自信。最后提出以证据台账、适当评分规则、校准检验和人工法律判断相分离的评估方案。

**Keywords:** probabilistic legal reasoning; Bayesian evidence; formal interfaces; source dependence; calibration; legal proof

**中文关键词：** 概率法律推理；贝叶斯证据；形式接口；来源依赖；校准；法律证明

## 1 Research Questions and Epistemic Labels

**CONJECTURE.** The central research question is whether probabilistic assessments can assist legal fact analysis without being mistaken for formally verified legal conclusions. Four subsidiary questions follow. How should competing hypotheses be specified before evidence is evaluated? How should analysts represent dependence between documents derived from a common source? Which aspects of probabilistic analysis can be tested empirically? Where must a formal interface stop so that mathematical output does not silently decide admissibility, burden allocation, proof standards, or judgment?

**DERIVED.** This paper uses epistemic labels as scope controls. `DERIVED.` marks ordinary mathematical consequences of stated assumptions, including applications of probability axioms, Bayes’ theorem, likelihood ratios, model averaging, and scoring rules. `CONJECTURE.` marks proposed empirical procedures, institutional interpretations, or possible legal uses whose adequacy depends on data, jurisdiction, governance, and human judgment. Neither label asserts that the corresponding proposition has been mechanized in Lean.

**FORMALIZED.** The formal claims are narrower. `EdgeKind.probabilityKernel` is an edge tag whose baseline obligations are generated through `ULM04.requiredObligations`, including `observationDeclaration`. The repository also establishes `requiredObligations_nonempty` and request, failure, trust, and authority interface theorems. These results concern the existence and behavior of interface obligations; they do not prove probability semantics, evidentiary weight, or legal correctness [@LegalMathModeling2026].

**CONJECTURE.** The paper therefore treats probabilistic output as an assessment artifact rather than a judgment artifact. An assessment may expose assumptions, compare hypotheses, and identify which observations most affect uncertainty. A legal decision additionally requires determinations about relevance, admissibility, burdens, institutional authority, applicable standards, procedural fairness, and justified exercise of judgment. Collapsing these layers would convert a useful analytic aid into an unauthorized decision rule.

## 2 Related Work

**DERIVED.** Bayesian approaches to legal evidence emphasize the distinction between a likelihood—how expected an observation is under a hypothesis—and a posterior probability—the probability assigned to the hypothesis after combining the observation with priors and alternatives. Bayesian networks make conditional dependence visible and can reduce the informal multiplication of evidential weights [@FentonNeilLagnado2013; @VlekEtAl2015]. Their mathematical usefulness nevertheless depends on whether the represented hypotheses, dependencies, and numerical inputs are adequate.

**DERIVED.** Work on legal proof has shown that likelihood ratios can be informative while still being vulnerable to transposed conditionals and neglected alternatives. A high probability of evidence given a hypothesis is not the same as a high probability of the hypothesis given the evidence. Likewise, a likelihood ratio compares specified hypotheses; it does not establish that the favored hypothesis is true or that the comparison set is complete [@FentonNeilBerger2016; @TaroniEtAl2014].

**DERIVED.** Argumentation and nonmonotonic reasoning provide complementary accounts of defeasible legal reasoning. Abstract argumentation studies conflict and acceptability among arguments, while legal argumentation models represent rules, exceptions, priorities, and adversarial defeat [@Dung1995; @PrakkenSartor1997]. Default logic similarly captures conclusions that may be withdrawn after new information arrives [@Reiter1980]. These approaches need not assign numerical probabilities, and probabilities need not represent argumentative validity or defeat.

**DERIVED.** Formal methods distinguish semantic claims from the interfaces and proof obligations through which systems manipulate them. Fixed-point semantics, abstract interpretation, and Hoare-style reasoning illustrate how rigor depends on an explicitly defined semantic domain and sound transformation rules [@Tarski1955; @CousotCousot1977; @Hoare1969]. Lean and its mathematical ecosystem can support machine-checked definitions and proofs when those definitions and proofs actually exist [@DeMouraUllrich2021; @Mathlib2020]. An edge name alone supplies no such semantics.

**CONJECTURE.** Explainability research cautions that an intelligible presentation can be mistaken for a faithful account of a model or for a justification of its use. Post hoc explanations may conceal omitted variables, unstable dependencies, or institutional assumptions [@Lipton2018; @GuidottiEtAl2018]. In high-impact settings, an explanation should also permit meaningful contestation rather than merely make an output appear understandable [@WachterEtAl2018]. An evidence ledger is proposed here as a contestable record of inputs and assumptions, not as proof that t
36,548
he assessment is legally acceptable.

## 3 Probability Model

### 3.1 Hypothesis Space and Priors

**DERIVED.** Let \(\mathcal H=\{H_1,\ldots,H_m\}\) be a finite, mutually exclusive, and collectively exhaustive hypothesis set for a defined factual question. A prior distribution assigns nonnegative mass summing to one. This elementary construction is conditional on the chosen hypothesis space; if a materially plausible hypothesis is omitted, normalization can create artificial confidence among the remaining hypotheses.

\[
\mathcal H=\{H_1,\ldots,H_m\},\qquad
\pi_i=P(H_i),\qquad
\pi_i\ge 0,\qquad
\sum_{i=1}^{m}\pi_i=1.
\tag{1}
\]

**CONJECTURE.** In legal applications, priors should not be smuggled in through labels such as “ordinary,” “credible,” or “official.” A proposed prior may come from a stipulated reference class, historical data, expert elicitation, or an intentionally broad interval. Each choice is contestable. Where no defensible reference class exists, reporting conclusions over a prior range is preferable to presenting one precise number as institutionally neutral.

### 3.2 Observations, Sources, and Dependence

**DERIVED.** Let \(E=(E_1,\ldots,E_n)\) denote observations and \(S\) a latent or uncertain source state, such as reliable generation, clerical copying, shared transcription error, or reconstruction after the event. A joint model can factor through \(S\), but this factorization is an assumption about dependence. It is not implied merely because observations appear in separate files.

\[
P(H_i,S,E)
=
P(H_i)\,P(S\mid H_i)
\prod_{j=1}^{n}P(E_j\mid H_i,S,E_{<j}).
\tag{2}
\]

**DERIVED.** Conditional independence is a substantive modeling claim. Two documents may be physically distinct yet probabilistically dependent because one copied the other, both were produced from the same database entry, or both reflect a common witness. Conversely, records generated through genuinely separate processes may provide more incremental information. File count therefore cannot substitute for a causal account of document generation.

### 3.3 Posterior Updating and Likelihood

**DERIVED.** Given a specified model and evidence \(E\) with positive marginal probability, Bayes’ theorem updates the prior distribution. The denominator normalizes across all modeled hypotheses. It follows from ordinary probability theory, not from the Lean interface described in this paper.

\[
P(H_i\mid E)
=
\frac{P(E\mid H_i)\pi_i}
{\sum_{k=1}^{m}P(E\mid H_k)\pi_k}.
\tag{3}
\]

**DERIVED.** A likelihood ratio compares how well an observation discriminates between two hypotheses. It is a function of the evidence under those hypotheses, not a posterior probability and not the probability that either hypothesis is true. Its interpretation is incomplete without prior odds and an adequately specified alternative.

\[
LR_{a:b}(E)
=
\frac{P(E\mid H_a)}
{P(E\mid H_b)}.
\tag{4}
\]

**DERIVED.** For two hypotheses, posterior odds equal prior odds multiplied by the likelihood ratio. This identity reveals base-rate neglect: treating the likelihood ratio as if it were posterior odds silently replaces actual prior odds with one. It also reveals why an impressive likelihood ratio may yield a modest posterior when the favored hypothesis had a sufficiently low prior probability.

\[
\frac{P(H_a\mid E)}{P(H_b\mid E)}
=
\frac{P(H_a)}{P(H_b)}
\frac{P(E\mid H_a)}{P(E\mid H_b)}.
\tag{5}
\]

### 3.4 Double Counting and Conditional Dependence

**DERIVED.** A diagnostic dependence factor can compare a modeled joint likelihood with the product that independence would imply. A value of one represents conditional independence under \(H_i\); other values indicate that multiplication of marginal likelihoods would misstate the joint evidential contribution. The factor is descriptive within a model and does not identify the causal mechanism by itself.

\[
\kappa_i
=
\frac{P(E_1,E_2\mid H_i)}
{P(E_1\mid H_i)P(E_2\mid H_i)}.
\tag{6}
\]

**CONJECTURE.** Analysts should document the production chain before eliciting \(\kappa_i\) or any equivalent conditional probabilities. Useful questions include who created each record, which source fields were reused, whether timestamps were generated independently, whether a later document could have copied an earlier one, and whether a common software or clerical process could produce correlated error. The answers remain factual claims requiring evidentiary support.

### 3.5 Competing Hypotheses

**DERIVED.** Multi-hypothesis normalization prevents a binary comparison from absorbing probability that belongs to an unmodeled alternative. Posterior mass is distributed over the declared set according to each prior-weighted likelihood. Adding a plausible hypothesis can therefore change the posterior even when the likelihoods of existing hypotheses remain unchanged.

\[
P(H_i\mid E)
=
\frac{\pi_i L_i(E)}
{\sum_{k=1}^{m}\pi_kL_k(E)},
\qquad
L_i(E)=P(E\mid H_i).
\tag{7}
\]

**CONJECTURE.** Hypothesis design should occur before numerical fitting and should permit adversarial amendment. A proponent may distinguish timely performance, late performance, clerical misdating, and nonperformance, while an opponent may identify a common-cause reconstruction hypothesis. The aim is not to enumerate every imaginable story but to avoid a comparison in which the favored account wins because realistic competitors were excluded.

### 3.6 Uncertainty About Sources and Models

**DERIVED.** If source reliability \(S\) is uncertain, the evidential likelihood is obtained by marginalizing over source states. This prevents the analyst from treating a disputed source characterization as settled. The resulting value remains conditional on the declared source states and their probabilities.

\[
P(E\mid H_i)
=
\sum_{s\in\mathcal S}
P(E\mid H_i,S=s)\,P(S=s\mid H_i).
\tag{8}
\]

**DERIVED.** Model uncertainty can be represented by averaging across candidate models \(M_r\). Each model may encode different dependency structures, reference classes, or source mechanisms. Model averaging does not prove that the candidate set is complete; it only propagates uncertainty over the included models.

\[
P(H_i\mid E)
=
\sum_{r=1}^{R}
P(H_i\mid E,M_r)\,P(M_r\mid E).
\tag{9}
\]

**CONJECTURE.** A practical report should show results under several defensible models rather than conceal modeling disagreement inside a single posterior. One model may treat two documents as conditionally independent, another as generated by a common source, and a third as partially dependent. If conclusions change materially, that instability is itself decision-relevant information, though its legal significance remains for authorized judgment.

### 3.7 Sensitivity

**DERIVED.** Local sensitivity measures how a reported posterior changes with an input parameter \(\theta\), such as a prior, error rate, or dependence coefficient. A derivative identifies direction and local magnitude, while interval analysis is often more understandable when inputs are only defensible within ranges.

\[
S_{i,\theta}
=
\frac{\partial P(H_i\mid E,\theta)}
{\partial\theta},
\qquad
\Delta_i[\theta_-,\theta_+]
=
\max_{\theta\in[\theta_-,\theta_+]}P(H_i\mid E,\theta)
-
\min_{\theta\in[\theta_-,\theta_+]}P(H_i\mid E,\theta).
\tag{10}
\]

**CONJECTURE.** Sensitivity analysis should focus on disputed or influential inputs. Exhaustively perturbing every parameter may obscure rather than clarify. A concise analysis should identify which assumptions can reverse the ranking of hypotheses, move a posterior across a decision-relevant region, or materially widen uncertainty. Any connection to a legal threshold must be separately justified rather than inferred from numerical movement alone.

## 4 Interface to Formal Legal Reasoning

**FORMALIZED.** In the relevant Lean interface, `EdgeKind.probabilityKernel` creates baseline obligations through `ULM04.requiredObligations`, and those obligations include `observationDeclaration`. This establishes that use of the edge kind carries an observation-related declaration requirement. It does not define observations as random variables, assign a sigma-algebra, construct a probability measure, or prove any stochastic-kernel law [@LegalMathModeling2026].

**FORMALIZED.** The theorem `requiredObligations_nonempty` establishes that the required-obligation collection is nonempty. Nonemptiness is a structural property: it prevents an edge from being presented as obligation-free. It does not show that an obligation has been discharged, that the declared observation is true, or that a probability calculation is mathematically or legally valid.

**FORMALIZED.** The request and failure interface theorems constrain how requests and failures are represented or propagated at the formal boundary. The trust and authority interface theorems similarly constrain trust or authority relationships expressible by that interface. These theorems do not prove Bayes’ theorem, likelihood-ratio validity, source independence, posterior convergence, calibration, proof thresholds, or probabilistic legal inference.

**DERIVED.** Consequently, a probabilistic engine may be placed behind the formal interface only as an external producer of declared assessment artifacts. Its computations require an independently specified probability model and ordinary mathematical validation. The formal edge and its obligations can record that an observation-related declaration is required, but the semantic truth of the observation and the correctness of the model remain outside the proved interface.

**CONJECTURE.** The safest integration pattern is asymmetric. The probabilistic component may submit a request containing hypotheses, observations, model identifiers, assumptions, and results; the formal interface may demand declarations and represent failure, trust, or authority conditions. Acceptance at this boundary should mean only that the artifact satisfies the declared interface contract, not that a court should admit the evidence or accept the posterior.

**CONJECTURE.** Legal reasoning should consume probabilistic output through an explicit separation function. Let \(Q\) be a quantitative assessment, \(A\) an admissibility determination, \(B\) a burden allocation, \(T\) an applicable proof standard, and \(R\) a set of legal reasons. Final judgment \(J\) is not identified with \(Q\), and no universal function \(\Phi\) is asserted as existing law.

\[
J=\Phi(Q,A,B,T,R,\text{authorized legal judgment}),
\qquad
J\ne Q.
\tag{11}
\]

## 5 Complete Worked Case Study

### 5.1 Hypothetical Record

**CONJECTURE.** Consider a wholly hypothetical procedural dispute. Party P asserts that a notice was served on Day 1 and that a related filing was lodged on Day 8. Party R disputes both the asserted service event and the reliability of the filing date. Document \(D_1\) is a scanned service receipt. Document \(D_2\) is a docket entry that may have been populated from the same uploaded scan. No actual jurisdiction, procedural rule, deadline, or legal consequence is asserted.

**CONJECTURE.** Three hypotheses are used. \(H_1\): service occurred on Day 1 and filing occurred on Day 8. \(H_2\): a filing occurred, but the claimed service date is unsupported or reconstructed. \(H_3\): neither asserted date is reliably established because both documents reflect a later clerical reconstruction. These hypotheses simplify reality, but the third prevents the analysis from becoming a forced binary contest between complete acceptance and complete rejection.

**CONJECTURE.** For demonstration, suppose the priors are \((0.35,0.40,0.25)\). These values are not legal presumptions and are not empirical claims. They merely permit transparent calculation. Suppose the marginal likelihoods for \(D_1\) under \(H_1,H_2,H_3\) are \((0.80,0.55,0.15)\), and those for \(D_2\) are \((0.75,0.65,0.20)\). Every number is hypothetical and contestable.

### 5.2 Naive Independence Analysis

**DERIVED.** If the documents were conditionally independent under each hypothesis, their joint likelihoods would be \((0.6000,0.3575,0.0300)\). Multiplying by the priors gives unnormalized weights \((0.2100,0.1430,0.0075)\). Normalization yields a posterior of approximately \((0.5825,0.3967,0.0208)\). The arithmetic is valid under independence, but the factual premise is doubtful because \(D_2\) may derive from \(D_1\).

\[
P_{\mathrm{ind}}(H_i\mid D_1,D_2)
=
\frac{\pi_iP(D_1\mid H_i)P(D_2\mid H_i)}
{\sum_k\pi_kP(D_1\mid H_k)P(D_2\mid H_k)}.
\tag{12}
\]

**DERIVED.** This result illustrates double counting. Under the independence model, the second document appears to provide fresh evidence. If it merely records information copied from the uploaded receipt, its evidential contribution is smaller. The error is not that multiplication is mathematically invalid; the error is applying a product factorization whose conditional-independence assumption does not match the proposed production process.

### 5.3 Source-Dependent Analysis

**CONJECTURE.** Now suppose a source investigation indicates that the docket entry was usually generated after staff read the uploaded receipt. On that assumption, use directly elicited joint likelihoods \((0.68,0.48,0.12)\). The larger joint likelihood under \(H_3\) reflects the possibility that one reconstruction generated both documents. Again, these are teaching values, not estimates about any real registry or filing system.

**DERIVED.** Prior weighting gives \((0.238,0.192,0.030)\), with total \(0.460\). The posterior becomes approximately \((0.5174,0.4174,0.0652)\). Accounting for dependence reduces the posterior of \(H_1\), increases the relative support for \(H_2\), and more than triples the posterior mass assigned to \(H_3\) compared with the independence analysis.

\[
P_{\mathrm{dep}}(H_1,H_2,H_3\mid D_1,D_2)
=
\frac{(0.35\cdot0.68,\;0.40\cdot0.48,\;0.25\cdot0.12)}
{0.35\cdot0.68+0.40\cdot0.48+0.25\cdot0.12}
\approx
(0.5174,0.4174,0.0652).
\tag{13}
\]

**DERIVED.** The posterior \(0.5174\) is not the likelihood of the documents under \(H_1\), which is \(0.68\). Nor is it the probability that the documents are authentic, the probability that a court should admit them, or the probability that any legal deadline was satisfied. It is the normalized probability of \(H_1\) within the stipulated hypothesis set, priors, joint likelihoods, and model.

### 5.4 Source Reliability Uncertainty

**CONJECTURE.** Suppose the production-chain evidence does not establish whether the docket entry was copied from the receipt. Define two candidate models: \(M_I\), conditional independence, and \(M_D\), dependence through a common source. Assigning equal posterior model weights is merely illustrative. Model averaging then gives a posterior for \(H_1\) near \(0.5500\), halfway between the two model-specific results.

\[
P(H_1\mid D_1,D_2)
=
0.5\,P(H_1\mid D_1,D_2,M_I)
+
0.5\,P(H_1\mid D_1,D_2,M_D)
\approx 0.5500.
\tag{14}
\]

**DERIVED.** Model averaging communicates a different uncertainty from uncertainty among factual hypotheses. The values \(P(H_i\mid E,M_r)\) concern hypotheses within a model; the weights \(P(M_r\mid E)\) concern uncertainty about the modeling structure. Merging both levels into one unexplained posterior would conceal whether uncertainty arises from conflicting evidence, uncertain sources, or disagreement about dependence.

### 5.5 Sensitivity and Legal Separation

**DERIVED.** Let \(\lambda\in[0,1]\) interpolate between the independence joint likelihoods and the dependence joint likelihoods. The posterior for \(H_1\) falls from approximately \(0.5825\) at \(\lambda=0\) to \(0.5174\) at \(\lambda=1\). This interval quantifies sensitivity to one modeling choice; it does not resolve which endpoint better represents the documents.

\[
P_\lambda(H_1\mid D_1,D_2)
=
\frac{0.35(0.6000+0.0800\lambda)}
{0.35(0.6000+0.0800\lambda)
+0.40(0.3575+0.1225\lambda)
+0.25(0.0300+0.0900\lambda)}.
\tag{15}
\]

**CONJECTURE.** An authorized legal decision-maker would still have separate questions. Is either document admissible? Which party bears which burden? What standard governs the disputed event? Are presumptions, sanctions, stipulations, or procedural defaults applicable? Does the relevant standard permit or require a numerical interpretation? The hypothetical posterior answers none of these questions and should not be relabeled as satisfaction of a legal proof threshold.

**CONJECTURE.** The appropriate case report would therefore state the hypothesis set, disclose the hypothetical or elicited priors, describe the common-source issue, present both dependence models, and identify the posterior range. It would separately record admissibility and legal-standard determinations as unresolved unless supplied by authorized legal judgment. This preserves the analytic value of probability without converting an assessment into a ruling.

## 6 Counterexamples and Sensitivity Analysis

### 6.1 Likelihood–Posterior Confusion

**DERIVED.** Suppose evidence \(E\) has \(P(E\mid H)=0.99\) and \(P(E\mid\neg H)=0.10\), producing a likelihood ratio of \(9.9\). If the prior probability of \(H\) is \(0.001\), the posterior is only about \(0.0098\). Saying that \(H\) is “99% likely” transposes the conditional and ignores the base rate.

\[
P(H\mid E)
=
\frac{0.99(0.001)}
{0.99(0.001)+0.10(0.999)}
\approx 0.0098.
\tag{16}
\]

**CONJECTURE.** In a legal report, the reference class underlying the prior may itself be controversial. The counterexample does not establish that a low prior should govern any real dispute. It establishes only that a likelihood cannot be reported as a posterior without the omitted prior and alternative-hypothesis assumptions.

### 6.2 Duplicate Records

**DERIVED.** Suppose ten database exports reproduce one originating entry. Treating them as ten independent observations raises the same likelihood contribution to the tenth power, potentially manufacturing extreme posterior odds. If the exports are deterministic copies, the evidential content is closer to one observation plus evidence about preservation and transmission. Multiplicity of containers is not multiplicity of independent sources.

**CONJECTURE.** A source graph should therefore distinguish an observation from its manifestations. Original entry, scan, email attachment, docket display, and litigation exhibit may be separate objects but one informational lineage. Whether later handling adds evidence—such as an independent timestamp or authenticated custody event—is a factual matter for the ledger, not something inferable from file count.

### 6.3 Omitted Competitors

**DERIVED.** A binary analysis comparing \(H_1\) with \(H_2\) assigns all normalized mass to those two hypotheses. Introducing \(H_3\), a common-cause error or reconstruction account, can substantially reduce both posteriors even when their likelihood ratio remains unchanged. Pairwise discrimination therefore cannot establish completeness of the hypothesis space.

**CONJECTURE.** Adversarial review should ask whether the alternatives include innocent error, shared-source contamination, ambiguous timing, and mixed hypotheses in which only part of an asserted narrative is correct. This is not a demand for unlimited possibility generation. It is a safeguard against defining the contest so narrowly that normalization masquerades as factual certainty.

### 6.4 Model and Parameter Sensitivity

**DERIVED.** Sensitivity may arise from priors, likelihoods, source-state probabilities, dependency structure, or model weights. A posterior stable under small parameter changes can remain wrong if every candidate model shares the same omitted mechanism. Conversely, a wide sensitivity interval does not show that probability is useless; it accurately reports that the available assumptions do not support a precise conclusion.

**CONJECTURE.** Reports should distinguish local sensitivity, global scenario variation, and structural uncertainty. Local derivatives address nearby numerical changes. Scenario analysis compares substantively different accounts of source generation. Structural criticism asks whether the variables and dependencies are appropriate at all. Only the first is primarily computational; the latter two require documentary investigation and domain judgment.

## 7 Evaluation and Calibration Protocol

### 7.1 Target and Dataset

**CONJECTURE.** Evaluation should begin with a prospectively defined prediction target and outcome-resolution rule. Cases should be assessed before outcomes are known, with timestamps sufficient to prevent retrospective editing. The dataset should preserve unresolved cases rather than silently excluding them, because selective resolution may distort apparent performance. No evaluation result should be interpreted as legal validity without separate institutional analysis.

**CONJECTURE.** Training, calibration, and evaluation cases should be separated by time or institution when deployment involves temporal or institutional transfer. Random splitting may leak repeated sources, templates, parties, or document-generation processes across partitions. Grouped splits are especially important where multiple records descend from one source event, since leakage would reward the same double counting that the model is meant to avoid.

### 7.2 Calibration and Discrimination

**DERIVED.** Calibration concerns agreement between predicted probabilities and observed frequencies over a defined population. If cases assigned probability near \(p\) resolve positively near frequency \(p\), the predictions are calibrated for that population and binning scheme. Calibration does not imply useful discrimination, causal adequacy, fairness, or legally appropriate use.

**DERIVED.** Discrimination measures ranking ability, whereas calibration evaluates probabilistic scale. A model may rank cases well but be systematically overconfident, or be calibrated because it predicts a nearly constant base rate while distinguishing cases poorly. Both properties should be reported, and neither should be translated into a legal proof standard.

### 7.3 Proper Scoring Rules

**DERIVED.** For binary outcomes \(y_t\in\{0,1\}\) and predictions \(p_t\), the Brier score is the mean squared probabilistic error. Lower values are better under the stated sampling process. Decomposition may help distinguish reliability, resolution, and outcome uncertainty, but the score remains sensitive to the evaluated population and target definition.

**DERIVED.** The logarithmic score penalizes confident errors strongly and is strictly proper when predictions and outcomes satisfy its assumptions. Predictions of exactly zero or one create unbounded loss when contradicted, which makes unjustified certainty visible. Operational clipping may be necessary for computation, but clipping rules must be disclosed because they alter the reported score.

**CONJECTURE.** A pre-registered evaluation should report Brier and log scores, calibration plots with uncertainty intervals, discrimination metrics, subgroup results where justified, and comparisons with simple baselines. It should also audit whether apparently independent cases share documents, institutions, or data-generation pipelines. Statistical performance cannot compensate for an invalid legal target or unauthorized decision use.

### 7.4 Dependence and Robustness Tests

**CONJECTURE.** Robustness evaluation should include duplicate-source ablation, leave-one-source-family-out testing, alternative hypothesis sets, prior-range analysis, and competing dependency structures. The system should be tested on cases where the number of documents increases without new independent information. A well-designed model should avoid becoming arbitrarily confident merely because one source was copied many times.

**CONJECTURE.** Human review should compare the evidence ledger with the numerical graph. Reviewers should be able to challenge whether two records are independent, whether a source state was omitted, and whether the outcome label resolves the same proposition that the model predicted. Disagreement should trigger model revision or parallel reporting, not an assertion that the calculation has settled the factual dispute.

### 7.5 Monitoring

**CONJECTURE.** Post-deployment monitoring should detect changes in base rates, source systems, document templates, missingness, and resolution practices. Recalibration may correct probabilistic scale after drift, but it cannot repair an obsolete hypothesis space or an invalid target. Material process changes should therefore trigger structural review in addition to numerical recalibration.

## 8 Evidence Ledger

**CONJECTURE.** The evidence ledger records provenance, assumptions, challenges, and the boundary between observations and interpretations. It should be append-oriented and reviewable, but its existence does not authenticate its contents. Each row supports contestation by showing where a numerical input originated and which unresolved issue could change it.

| Ledger item | Status | Hypothetical entry | Epistemic role | Required challenge |
|---|---|---|---|---|
| Proposition | CONJECTURE | Service on Day 1 and filing on Day 8 | Defines \(H_1\) | Is the proposition too compound? |
| Alternative | CONJECTURE | Filing occurred; service date unsupported | Defines \(H_2\) | Are partial-event alternatives represented? |
| Common-cause alternative | CONJECTURE | Later clerical reconstruction | Defines \(H_3\) | What evidence supports this mechanism? |
| Observation \(D_1\) | CONJECTURE | Scanned service receipt | Evidential input | Origin, custody, date, alterations |
| Observation \(D_2\) | CONJECTURE | Docket entry | Evidential input | Independent generation or copied field |
| Source link | CONJECTURE | \(D_2\) may derive from \(D_1\) | Dependence assumption | Workflow records and staff evidence |
| Prior vector | CONJECTURE | \((0.35,0.40,0.25)\) | Demonstration assumption | Reference class or elicitation basis |
| Independence likelihoods | DERIVED | \((0.6000,0.3575,0.0300)\) | Model \(M_I\) | Is factorization defensible? |
| Dependent likelihoods | CONJECTURE | \((0.68,0.48,0.12)\) | Model \(M_D\) | How were joint values elicited? |
| Posterior range for \(H_1\) | DERIVED | \(0.5174\)–\(0.5825\) | Sensitivity result | Which models deserve weight? |
| Admissibility | CONJECTURE | Unresolved | Legal determination | Applicable authority and objections |
| Burden | CONJECTURE | Unresolved | Legal allocation | Which party bears what burden? |
| Standard of proof | CONJECTURE | Unresolved | Normative rule | Is numerical translation authorized? |
| Final judgment | CONJECTURE | Not produced | Authorized legal act | Reasons, procedure, and decision-maker |

## 9 Verification Boundary

**FORMALIZED.** The verified boundary includes the `probabilityKernel` edge tag, the inclusion of `observationDeclaration` among baseline obligations generated by `ULM04.requiredObligations`, `requiredObligations_nonempty`, and the request, failure, trust, and authority interface theorems. These are the only propositions in this paper presented as formalized repository claims [@LegalMathModeling2026].

**FORMALIZED.** None of those interface results proves the existence of probability measures or stochastic kernels. None proves Bayes’ theorem, a likelihood ratio, Bayesian-network semantics, calibration, Brier scoring, logarithmic scoring, posterior convergence, a legal proof threshold, or a probabilistic legal inference. The name `probabilityKernel` must not be treated as a theorem about probability.

**DERIVED.** Equations (1)–(10), (12)–(16), and the numerical calculations are ordinary mathematics conditional on their displayed assumptions. Their correctness can be checked algebraically or with an independently implemented calculator. Such checking would verify arithmetic and mathematical implication, not the truth of priors, likelihoods, source accounts, hypotheses, or legal premises.

**CONJECTURE.** Equation (11) is an architectural separation, not a mathematical or legal theorem. It signals that assessment, admissibility, burdens, proof standards, reasons, authority, and judgment are distinct inputs or operations. The appropriate form of \(\Phi\), if any, depends on applicable law and authorized human judgment and should not be inferred from the formal interface.

**CONJECTURE.** Verification should therefore be reported in layers: interface theorem verified; arithmetic reproduced; empirical calibration measured; source claims supported or disputed; legal authority supplied or absent; and final judgment made or withheld. Passing one layer must not silently upgrade another. In particular, a type-correct request is not an authenticated observation, and a calibrated posterior is not a lawful judgment.

## 10 Limitations

**CONJECTURE.** The finite hypothesis model may oversimplify narratives that overlap, evolve, or contain continuous quantities. Mutually exclusive hypotheses can be difficult to formulate when events are only partially disputed. Enlarging the model improves expressiveness but increases elicitation demands and may create false precision if likelihoods cannot be supported.

**CONJECTURE.** Priors and likelihoods may be unavailable, contested, or institution-specific. Expert elicitation can expose assumptions but is vulnerable to anchoring and shared bias. Historical datasets may reflect selective litigation, settlement, recording practices, and changing institutions. Calibration measured on one population may not transfer to another.

**CONJECTURE.** Source dependence can be more complex than a shared-parent relationship. Documents may interact through copying, partial automation, human review, and feedback from earlier assessments. A Bayesian network can represent such relations only after they are identified and parameterized. Graphical sophistication does not cure missing provenance or unreliable inputs.

**CONJECTURE.** Proper scoring rules reward probabilistic accuracy for defined outcomes, but legally important qualities also include procedural fairness, reason-giving, contestability, rights protection, and legitimate authority. A system could achieve favorable scores while predicting an inappropriate target or reinforcing defective institutional practices. Evaluation must therefore remain subordinate to a justified use specification.

**CONJECTURE.** This paper proposes no universal numerical proof threshold and makes no real legal rule assertion. Jurisdictions may describe proof standards in qualitative, normative, or institutionally specific terms that resist numerical reduction. Even where probabilities are considered, the mapping from assessment to decision requires legal authority and judgment not supplied by the probability model.

## 11 Declarations

### Funding

No external funding was received for this theoretical paper.

### Conflict of Interest

The author declares no conflict of interest.

### Data Availability

No empirical dataset was used. All numerical values and records in the worked case are hypothetical and included in the paper.

### Ethics

The paper uses no human participants, personal data, real case records, or identifiable parties. The worked case is fictional.

### Author Contributions (CRediT)

Laupinco: Conceptualization, Methodology, Formal Analysis, Investigation, Writing—Original Draft, Writing—Review and Editing.

### AI Usage Disclosure

Generative AI assisted with drafting and structural organization. The author remains responsible for the paper’s arguments, citations, mathematical assumptions, boundary claims, and final text.

## References

**DERIVED.** Bibliographic records for all cited works are maintained in `paper/references.bib`. The works actually cited in this paper are listed below by their bibliography keys.

- [@LegalMathModeling2026]
- [@FentonNeilLagnado2013]
- [@VlekEtAl2015]
- [@FentonNeilBerger2016]
- [@TaroniEtAl2014]
- [@Dung1995]
- [@PrakkenSartor1997]
- [@Reiter1980]
- [@Tarski1955]
- [@CousotCousot1977]
- [@Hoare1969]
- [@DeMouraUllrich2021]
- [@Mathlib2020]
- [@Lipton2018]
- [@GuidottiEtAl2018]
- [@WachterEtAl2018]
