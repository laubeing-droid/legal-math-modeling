# Conservative Multi-Agent Legal Reasoning: Observation, Verification, Authority, Receipts, Trust, and Taint

**Author:** Laupinco

## Abstract

**DERIVED.** This paper develops a conservative architecture for multi-agent legal reasoning in which computation may preserve, transform, verify, and aggregate claims without silently upgrading their epistemic, institutional, or legal status. The architecture separates observations from propositions, verifier acceptance from source truth, authority from consensus, task-bound human-action records from reusable credentials, trust aggregation from evidential corroboration, and taint propagation from voting outcomes. Its central invariants prohibit failure erasure, authority escalation by agreement, cross-task reuse of research receipts, and cleansing of contaminated inputs through repetition or majority vote. A typed outcome model, obligation-indexed verification layer, authority lattice, receipt-validity predicate, trust meet, and taint join jointly define the permitted composition of agents and stages. A complete worked case follows a disputed statutory-deadline calculation through observation, branching, deterministic verification, human legal judgment, and evidence-ledger recording. Counterexamples show how superficially plausible systems violate the invariants through lossy mapping, verifier overclaiming, branch conflation, credential reuse, and provenance laundering. The Lean anchors named in the paper concern only internal formal properties of the specified model. They do not establish source authenticity, substantive-law validity, runtime conformance, probabilistic calibration, agent independence, explanation quality, or legal correctness. Those external properties require separate empirical evidence, authoritative legal judgment, and traceable receipts.

## 中文摘要

**DERIVED.** 本文提出一种保守型多智能体法律推理架构，目的不是把模型输出包装成法律结论，而是限制系统在组合、验证与汇总过程中能够声称什么。架构严格区分观察记录与事实真伪、验证器接受与实体法正确、智能体共识与制度权限、一般身份凭证与绑定具体任务的人类研究回执、信任汇合与证据相互印证，以及多数表决与污染消除。形式模型包含带失败状态的结果类型、非空义务集合、验证器可靠性条件、权限等级与签发规则、回执的任务、输入、期限及撤销约束、信任向量的逐项下确界，以及污染标签的逐项上确界。核心不变量禁止映射抹除失败、共识提升权限、跨任务复用回执，并禁止重复或多数投票清洗受污染输入。文中以争议性法定期限计算为完整案例，展示请求身份、分支身份、确定性日期运算、人类法律判断和证据账本如何协同。所列 Lean 锚点仅证明模型内部命题，不证明资料真实、现行法内容、外部运行实现、概率校准、智能体独立性、解释质量或法律正确性；这些事项仍须经验验证、权威资料与具名法律责任人确认。

**Keywords:** conservative composition; multi-agent legal reasoning; formal verification; authority control; provenance receipts; trust lattice; taint propagation

**中文关键词：** 保守组合；多智能体法律推理；形式验证；权限控制；研究回执；信任格；污染传播

## 1 Research Questions and Epistemic Labels

**DERIVED.** The paper asks four questions. First, which properties of a legal-reasoning pipeline can be expressed as compositional invariants? Second, how can the system prevent agreement, repetition, or transformation from upgrading a claim’s status? Third, how should human authority be represented so that authorization is specific to a task, its inputs, and its validity interval? Fourth, where must formal proof stop because the relevant proposition concerns sources, institutions, empirical performance, or substantive law rather than the internal semantics of a program?

**DERIVED.** Three epistemic labels govern every substantive claim. **FORMALIZED.** denotes a definition or theorem statement established inside the stated Lean model. **DERIVED.** denotes an interpretation obtained by applying those formal objects to an explicitly described workflow, without treating the interpretation as a machine-checked theorem. **CONJECTURE.** denotes an empirical, sociotechnical, probabilistic, or normative proposition that the formal model does not prove. The labels classify the basis of a statement, not its rhetorical importance.

**DERIVED.** A formalized proposition never implies that a cited source is authentic, that extracted text is faithful, that a legal rule is currently in force, that an external implementation refines the model, or that a legal conclusion is correct. The distinction resembles the separation between a program logic and the truth of the environment assumptions supplied to it [@Hoare1969]. Formal verification can constrain derivations from premises while remaining silent about whether the premises accurately describe the world.

**CONJECTURE.** A multi-agent implementation may improve accuracy, diversity, calibration, reviewer speed, efficiency, or robustness only under empirically validated conditions concerning task distribution, error dependence, model selection, incentives, interfaces, and review practice. No such improvement follows from agent count or architectural plurality alone. Each claimed benefit therefore requires prospective empirical validation against declared baselines and failure costs.

## 2 Related Work

**DERIVED.** The architecture inherits the idea that nonmonotonic reasoning must distinguish support from defeat. Default logic permits defeasible conclusions when exceptions are absent [@Reiter1980], while abstract argumentation represents attacks and admissibility without identifying acceptance with factual truth [@Dung1995]. Legal argumentation further connects defeasible rules, burdens, and dialogical structure [@PrakkenSartor1997; @ModgilPrakken2013]. The present model adopts the conservative lesson that a procedurally undefeated claim may remain false, unauthorized, or legally irrelevant.

**DERIVED.** Order-theoretic semantics provides the vocabulary for monotone operators, meets, joins, and fixed points [@Tarski1955]. Abstract interpretation shows how sound approximation depends on an explicit relation between concrete and abstract domains [@CousotCousot1977]. This paper applies a narrower discipline: trust is combined by meet, taint by join, and neither operator is allowed to smuggle in a claim about source truth. The resulting lattices track permissions and contamination rather than probabilities.

**DERIVED.** Classical logical foundations also caution against equivocation between syntax and world truth. Horn-clause reasoning supplies a disciplined fragment for rule application [@Horn1951], but a valid derivation proves only what follows from encoded premises. Likewise, causal and Bayesian legal models make dependence assumptions explicit [@FentonNeilLagnado2013; @VlekEtAl2015; @FentonNeilBerger2016]. The present architecture deliberately leaves probabilities and calibration outside its Lean boundary because neither is recoverable from symbolic provenance labels alone.

**DERIVED.** Explainability research distinguishes local surrogate behavior, interpretability claims, and counterfactual accounts [@RibeiroEtAl2016; @Lipton2018; @GuidottiEtAl2018; @WachterEtAl2018]. An evidence ledger can expose which inputs, transformations, and receipts supported an output, but such exposure is not automatically a good explanation. Legibility, causal adequacy, contestability, and usefulness to legal professionals remain separately evaluated properties.

**DERIVED.** Lean and Mathlib support machine-checked definitions and proofs over precisely stated objects [@DeMouraUllrich2021; @Mathlib2020]. The permitted anchors in this paper name proof obligations within a legal-mathematical model [@LegalMathModeling2026]. Their role is modest: they constrain internal composition. They do not convert observations into facts, code into deployed behavior, or a formal conclusion into authorized legal advice.

## 3 Formal Architecture

### 3.1 Requests, Observations, and Branches

**DERIVED.** A request is identified by a stable `RequestId` and an immutable input commitment. A branch is identified by a `BranchId`, its parent request, its parent branch if any, and the assumption delta that created it. Two branches may contain identical text while remaining distinct because their derivational histories differ. Conversely, a branch identifier cannot legitimize altered inputs merely because a label was copied.

\[
\operatorname{RequestIdentity}(r)
=
\bigl(\operatorname{id}(r),\operatorname{commit}(\operatorname{inputs}(r))\bigr)
\tag{1}
\]

**FORMALIZED.** The repository defines observation preservation parametrically. For observation maps \(o_A:A\to O\), \(o_B:B\to O\), and transformation \(f:A\to B\), `Preserves` requires equality of observed values. The theorem `preserves_comp`, instantiated as `COMP_C02_observation_preservation`, proves that this equality composes. It does not itself select which legal features the observation map must expose.

\[
\operatorname{Preserves}(o_A,o_B,f)
\iff
\forall x\in A,\quad o_B(f(x))=o_A(x)
\tag{2}
\]

**DERIVED.** OCR normalization may preserve an observation while changing its representation, provided the original is addressable, the transformation is recorded, and uncertainty is not discarded. The preserved proposition is “this process produced this representation from that recorded input,” not “the representation is an exact transcription” or “the document’s assertions are true.”

**DERIVED.** Branch identity prevents mutually inconsistent assumptions from being merged without an explicit reconciliation stage. A conclusion belongs to the pair of request and branch identities under which it was derived. Cross-branch reuse is permitted only if the reused proposition declares its assumption dependencies and those dependencies are satisfied in the receiving branch.

\[
\operatorname{BranchIdentity}(b)
=
\bigl(
\operatorname{requestId}(b),
\operatorname{branchId}(b),
\operatorname{parent}(b),
\Delta_b
\bigr)
\tag{3}
\]

### 3.2 Outcomes and Failure Preservation

**FORMALIZED.** The repository's `Outcome α` has exactly three constructors: `complete`, `partialResult`, and `failure`. A partial payload carries a value and a nonempty set of open obligations. `Outcome.map` transforms complete and partial payload values while retaining their constructor; `map_never_upgrades_failure` preserves the exact failure object.

\[
\operatorname{Outcome}(\alpha)
=
\operatorname{Complete}(\alpha)
\mid
\operatorname{Partial}(\alpha,O),\ O\neq\varnothing
\mid
\operatorname{Failure}(E)
\tag{4}
\]

**DERIVED.** A summarizer applied to a failed retrieval therefore returns a summarized failure record, not an apparently ordinary legal proposition. This rule closes a common laundering path in which downstream text generation forgets that an upstream parser, source fetch, or verifier failed.

### 3.3 Obligations and Verification

**FORMALIZED.** Every modeled normal-form edge has a required-obligation set containing `typeSafety`; its kind and declared claims can add further obligation kinds. The theorem `requiredObligations_nonempty` proves nonemptiness for every `NFEdge`. It does not prove that this modeled list exhausts the requirements of real legal practice.

\[
\forall e:\operatorname{NFEdge},\quad
\mathsf{typeSafety}\in\operatorname{requiredObligations}(e)
\land
\operatorname{requiredObligations}(e)\neq\varnothing
\tag{5}
\]

**FORMALIZED.** `VerifierSound` is parameterized by an independently stated goal on proof subjects. Acceptance must imply both that the evidence kind is supported and that the goal holds for the evidence subject. `Sat` separately binds an exact required obligation, exact subject, evidence kind, and successful Boolean check. Theorems `sat_sound` and `CORE_24_sat_sound` derive the goal only when the soundness premise is supplied.

\[
\operatorname{VerifierSound}(G,V)
\iff
\forall ev,\ V.verify(ev)=\top
\Rightarrow
ev.kind\in V.supported\land G(ev.subject)
\tag{6}
\]

**DERIVED.** A deterministic calendar verifier can establish that a date was computed according to an encoded counting rule. It cannot establish that the encoded rule governs the dispute, that a holiday table is authoritative, or that a court would classify the initiating event as the parties assume. Those propositions require separate sources and legal judgment.

### 3.4 Authority and Issuance

**FORMALIZED.** `AuthorityLevel` contains four ordered levels from `untrustedProposal` through `admittedFormalInput`. The function `authorityRank` maps levels to natural numbers, and `canIssue` compares a level with the required level for an `ArtifactKind`. The formal order is a supplied institutional policy; confidence, fluency, model identity, and vote count are not inputs to the rank.

\[
\operatorname{canIssue}(a,d)
\iff
\operatorname{authorityRank}(a)\geq
\operatorname{requiredRank}(d)
\tag{7}
\]

**FORMALIZED.** For `AuthorityReceipt`, `receiptValid` means exactly a one-rank promotion: the target rank equals the source rank plus one. Separately, `consensus_does_not_escalate` proves that a list containing repeated copies of one authority level cannot exceed that level. Neither theorem infers that a named real person possesses the modeled level.

\[
\operatorname{receiptValid}(r)
\iff
rank(r.to)=rank(r.from)+1,
\qquad
\operatorname{consensusRank}([l]^n)\leq rank(l)
\tag{8}
\]

**DERIVED.** One hundred research agents cannot jointly sign a filing if none can issue that filing. They may produce candidate analysis, objections, and source packets, but the disposition remains unauthorized until a properly empowered actor supplies a valid receipt.

### 3.5 Human Research Receipts

**FORMALIZED.** `HumanResearchReceipt` records a task identifier, input digest, reviewer string, one of three modeled actions, issue day, expiry day, and a Boolean revocation field. `receiptBindsTask` checks task and digest together; `receiptCurrentlyValid` checks the inclusive time window and absence of revocation.

\[
R=
\langle
taskId,inputDigest,reviewer,action,issuedDay,expiryDay,revoked
\rangle
\tag{9}
\]

**DERIVED.** The cross-task theorem rejects use when the request identifier differs. The cross-input theorem rejects use when the input commitment differs. The expiry theorem rejects use after the validity interval. The revocation theorem rejects use after an effective revocation. These theorems make authorization non-fungible across matters and changing evidentiary records.

\[
\operatorname{receiptBindsTask}(R,\tau,d)
\land\operatorname{receiptCurrentlyValid}(R,t)
\iff
R.taskId=\tau\land R.inputDigest=d
\land R.issuedDay\leq t\leq R.expiryDay
\land R.revoked=\mathsf{false}
\tag{10}
\]

**DERIVED.** A lawyer’s approval of a deadline calculation does not authorize a revised calculation after a new service record appears. Even if the visible conclusion remains unchanged, the input-bound receipt must be renewed because the reviewed evidentiary basis has changed.

### 3.6 Trust Vectors

**FORMALIZED.** `TrustVector` has five non-interchangeable coordinates named `source`, `text`, `fact`, `proof`, and `authority`, each valued in `Fin 3`. `TrustVector.meet` takes the coordinatewise minimum. Theorems `trust_meet_le_left` and `trust_meet_le_right`, exposed through `COMP_C01`, prove that the meet cannot exceed either input vector.

\[
(T_1\sqcap T_2)_j=\min(T_{1j},T_{2j})
\tag{11}
\]

**DERIVED.** The meet is deliberately pessimistic. A highly authoritative legal interpretation attached to an uncertain source transcript remains limited by transcript provenance; an exact transcript attached to an unauthorized interpretation remains limited by authority. The vector avoids collapsing unlike deficits into a single reassuring score.

**FORMALIZED.** Each trust coordinate is an ordinal element of `Fin 3`, not a calibrated probability. The formal meet theorem therefore establishes only order-theoretic non-upgrade. It does not assign a likelihood of truth to any proposition.

### 3.7 Taint Propagation and Stage Outputs

**FORMALIZED.** The repository taint carrier has two values, `clean` and `tainted`. `joinTaint` returns clean only for two clean inputs; `taintOfInputs` folds this operation over a list; and `stageOutput` assigns that folded taint to its output. Concrete interpretations such as source uncertainty or stale authority require an external mapping into this two-point carrier.

\[
\operatorname{taintOfInputs}(x_1,\ldots,x_n)
=
\bigvee_{i=1}^{n}\operatorname{taint}(x_i),
\qquad
\operatorname{taint}(\operatorname{stageOutput}(xs,c))
=
\operatorname{taintOfInputs}(xs)
\tag{12}
\]

**FORMALIZED.** If a distinguished input is tainted, `majority_cannot_clean` proves that the list's folded taint is tainted. `repetition_does_not_clean` proves that inserting a second copy of that input leaves the already-tainted fold unchanged. The model contains no general remediation operator; any cleaning procedure therefore lies outside these theorems.

\[
x.taint=\mathsf{tainted}
\Rightarrow
\operatorname{taintOfInputs}(x::xs)
=
\operatorname{taintOfInputs}(x::x::xs)
=
\mathsf{tainted}
\tag{13}
\]

**CONJECTURE.** Multiple genuinely independent acquisition channels might reduce some source-error risks, but independence, comparative accuracy, and robustness require empirical validation. The formal taint join does not infer independence from different agent names, prompts, vendors, or executions.

## 4 Composition Invariants

**DERIVED.** The first invariant is observational non-upgrade: composition preserves observation identity and never turns “observed” into “true.” If stages \(f\) and \(g\) each satisfy `Preserves`, `preserves_comp` permits the conclusion that \(g\circ f\) preserves the observation relation. `COMP_C02_observation_preservation` packages this constraint for the architecture’s admissible pipelines.

**DERIVED.** The second invariant is failure monotonicity. Mapping, formatting, translating, or summarizing an outcome cannot erase a non-success constructor. Recovery must be an explicit operation that consumes evidence addressing the recorded failure and returns a new outcome linked to the old one.

**DERIVED.** The third invariant is obligation visibility. Any disposition-relevant output carries a nonempty required-obligation set and a ledger entry for every obligation: satisfied, failed, blocked, or unresolved. Missing evidence is represented as unresolved rather than inferred from silence.

**DERIVED.** The fourth invariant is non-escalating authority. Consensus selects or combines proposals but cannot mint institutional power. A valid issuer may adopt a consensus product, yet the resulting authority derives from that issuer’s receipt, not from the number of contributing agents.

**DERIVED.** The fifth invariant is receipt specificity. `HumanResearchReceipt` records a task identifier, input digest, reviewer, action, issue day, expiry day, and revocation flag. `receiptBindsTask` checks only task and input equality; `receiptCurrentlyValid` checks only the time window and revocation flag. A receipt that fails either predicate cannot be repaired by textual similarity, actor seniority, or prior acceptance in another matter. Neither predicate binds a separate request or branch object, and satisfaction is not itself proof of external authorization.

**DERIVED.** The sixth invariant is conservative trust composition. The composite trust vector is no higher than either input vector in each required dimension. Improvements require new evidence that changes the relevant coordinate through an authorized update rule; they do not arise from averaging.

**DERIVED.** The seventh invariant is taint persistence. Taint survives majority, repetition, paraphrase, and format conversion. A remediation stage must identify the taint class, cite the discharge procedure, preserve the prior record, and issue a linked replacement artifact.

\[
\operatorname{AdmissibleCompose}(x,y)
\Rightarrow
\begin{cases}
T(x\circ y)\preceq T(x)\sqcap T(y),\\
Q(x\circ y)\succeq Q(x)\vee Q(y),\\
A(x\circ y)\leq \max(A(x),A(y)).
\end{cases}
\tag{14}
\]

**DERIVED.** Together, these invariants create a one-way ratchet against silent epistemic inflation. They do not forbid correction or improvement; they require that improvement be represented as a new evidence-bearing event rather than as an unrecorded side effect of composition.

## 5 Complete Worked Case Study

**DERIVED.** Consider request `R-Deadline-17`: determine the last permissible filing date after service of an administrative decision. The committed input package contains a scanned service certificate, a machine-readable statute snapshot, a holiday table, and the instruction that the result is research support rather than an automatically issuable legal opinion. Two observed dates appear plausible because the handwritten day is ambiguous.

**DERIVED.** The ingestion stage creates observation `O1` for the scan and `O2` for OCR output. `O1` records pixels, locator, retrieval time, and acquisition method. `O2` records the OCR text “14 March” with character-level uncertainty and links to `O1`. Observation preservation allows normalization of spacing but prohibits replacing uncertainty with an unqualified date.

**DERIVED.** The system creates branch `B14`, assuming service on 14 March, and branch `B19`, assuming service on 19 March. Their request identity is shared, but their branch identities and assumption deltas differ. No vote is taken between them because the ambiguity concerns source reading, not preference aggregation.

**DERIVED.** A rule-extraction agent records the observed statutory phrase, while a separate parser represents a thirty-day period, exclusion of the triggering day, and extension when the final day is a designated non-business day. These records are observations and candidate interpretations. They are not yet findings that the statute snapshot is authentic, current, applicable, or correctly construed.

**DERIVED.** For each branch, the deterministic calendar stage computes a candidate date using integer day arithmetic and the supplied holiday table. The verifier checks the encoded transition sequence, terminal-day adjustment, and trace completeness. `CORE_24_sat_sound` supports only the conditional proposition that accepted traces satisfy the encoded `Sat` specification.

\[
d_{\mathrm{candidate}}(b)
=
\operatorname{adjustBusinessDay}
\left(
\operatorname{serviceDate}(b)+30
\right)
\tag{15}
\]

**DERIVED.** Suppose `B14` yields 13 April before adjustment and 14 April after adjustment, while `B19` yields 18 April with no adjustment. The exact dates here are case inputs to the theoretical example, not claims about any jurisdiction’s law. Both results retain the source-uncertainty taint because correct arithmetic cannot determine which handwritten date was recorded.

**DERIVED.** The obligation ledger for each branch contains: scan provenance, OCR uncertainty review, rule-text locator, current-law confirmation, applicability determination, calendar-trace verification, holiday-table authority, and human disposition approval. Arithmetic verification satisfies only the calendar-trace obligation. The other entries remain separately visible.

**DERIVED.** A source-reviewing human compares the scan with a registry record and concludes that 19 March is the better transcription. The reviewer supplies a source-resolution receipt tied to `R-Deadline-17`, the committed inputs including the registry record, branch `B19`, and a defined validity interval. This evidence discharges the handwriting ambiguity for that input package but does not authorize the final legal disposition.

**DERIVED.** A reviewer then assesses applicability, confirms the governing materials for the defined research time, and issues a `HumanResearchReceipt` that records the action “candidate deadline: 18 April, subject to the stated scope.” The record can satisfy task/input binding and current-validity predicates; external institutional policy must separately establish the reviewer's authority. If a later filing rule, amended holiday notice, or corrected service record changes the package, `receiptBindsTask` fails for the new digest unless a new receipt is issued; `receiptCurrentlyValid` is controlled only by dates and revocation.

**DERIVED.** The rejected `B14` branch is retained rather than deleted. Its ledger records why it was superseded and which evidence resolved the ambiguity. Retention supports later contestation: a reviewer can reconstruct whether the difference arose from transcription, rule choice, calendar arithmetic, or authorization.

**DERIVED.** The final artifact contains the request and branch identities, observations, candidate rule interpretation, deterministic trace, verifier result, trust vector, joined taint, discharged and unresolved obligations, receipts, and disposition scope. It does not state merely “the agents agreed that the deadline is 18 April.”

**CONJECTURE.** Compared with an unstructured single-output workflow, this architecture may improve error localization, reviewer speed, accuracy, calibration, or robustness in deadline research, but every such claim requires empirical validation. The case study demonstrates representational discipline, not comparative performance.

## 6 Counterexamples and Failure Recovery

**DERIVED.** Counterexample one is lossy outcome mapping. A retrieval stage returns `Failed(timeout)`, but a summarizer emits “no adverse authority found.” This violates `map_never_upgrades_failure`. Recovery requires preserving the failure, rerunning retrieval under an explicit recovery event, and distinguishing “search completed with no result” from “search did not complete.”

**DERIVED.** Counterexample two is verifier inflation. A date trace passes the calendar verifier, and the system labels the deadline legally correct. This exceeds `VerifierSound`: acceptance entails `Sat` for the encoded arithmetic specification only. Recovery downgrades the label, identifies unverified applicability and authority obligations, and seeks appropriate legal review.

**DERIVED.** Counterexample three is consensus escalation. Five research agents select the same statutory interpretation, and an aggregator labels it authorized advice. This violates `consensus_does_not_escalate`. Recovery preserves the consensus as a proposal packet and requires an actor satisfying `canIssue` to adopt, reject, or qualify it through a valid receipt.

**DERIVED.** Counterexample four is receipt reuse. The application maps requests `R1` and `R2` to distinct task identifiers `T1` and `T2`; a human receipt bound to `T1` is then attached to `T2` because the questions look similar. The cross-task theorem invalidates that reuse at the task-identifier layer. If `T1` is retained but changed exhibits produce a different `inputDigest`, the cross-input theorem independently invalidates reuse. Recovery requires a new review against the new task and input commitments.

**DERIVED.** Counterexample five is a stale receipt. A receipt satisfied the model predicate when created but has expired or been revoked before publication. The expiry and revocation theorems make `receiptCurrentlyValid` false; a fail-closed release policy should therefore reopen its human-review obligation. This is a model-level blocking condition, not a theorem that publication is legally unauthorized.

**DERIVED.** Counterexample six is provenance laundering by repetition. Ten agents summarize the same defective OCR text and vote for the same reading. `repetition_does_not_clean` and `majority_cannot_clean` preserve the OCR taint. Recovery requires a new observation channel or manual comparison with the source, not more transformations of the same input.

**DERIVED.** Counterexample seven is branch conflation. One branch assumes electronic service and another assumes postal service, yet their conclusions are merged because their terminal dates coincide. The merge is invalid unless assumption dependencies are reconciled. Recovery retains both identities and issues a conclusion conditional on the unresolved service mode.

**DERIVED.** Counterexample eight is trust averaging. High authority and low provenance are averaged into a medium global score, concealing the decisive provenance defect. `TrustVector.meet` prevents compensation across dimensions. Recovery reports the vector and routes the deficient coordinate to a targeted evidence-gathering step.

\[
\operatorname{Recover}(x,e)=y
\Rightarrow
\operatorname{linksTo}(y,x)
\land
\operatorname{discharges}(e,\operatorname{defect}(x))
\land
\operatorname{preservesHistory}(y)
\tag{16}
\]

**DERIVED.** Recovery is consequently not deletion, relabeling, or majority override. It is a traceable transition supported by evidence matched to a specific defect. If no admissible evidence exists, the correct state remains failed, blocked, or unresolved.

## 7 Evaluation Protocol

**DERIVED.** Evaluation separates formal conformance, implementation refinement, empirical performance, and legal assessment. Formal conformance checks the stated Lean theorems. Implementation refinement tests whether runtime code realizes the formal interfaces and transition rules. Empirical performance measures observed behavior on declared tasks. Legal assessment is conducted by suitably authorized persons against governing materials.

**DERIVED.** A conformance suite should test request immutability, branch separation, observation preservation, nonempty obligations, failure-preserving maps, receipt scope, authority bounds, trust meets, taint joins, and recovery links. Negative tests should deliberately attempt cross-task receipt reuse, consensus escalation, failure erasure, and taint cleaning by repetition.

**CONJECTURE.** Whether the architecture improves accuracy, correctness, diversity, independence, calibration, efficiency, reviewer speed, or robustness requires empirical validation using preregistered comparators, representative matters, blinded review where feasible, and reported uncertainty. Agent independence must be measured rather than assumed from separate prompts or process identifiers.

**CONJECTURE.** A useful study could compare an unstructured baseline, a single-agent ledger system, and the conservative multi-agent architecture. Outcomes could include unsupported-claim rate, obligation-detection recall, review time, correction latency, authority violations, and residual legal error. The metrics’ validity, operational definitions, and institutional relevance themselves require empirical validation.

**DERIVED.** Probability estimates are accepted only as external observations accompanied by their estimation method and calibration evidence. Lean proofs in this architecture neither generate nor certify calibrated probabilities. Explanation quality is likewise evaluated by human-centered protocols, not inferred from ledger completeness.

**CONJECTURE.** The evidence ledger may help reviewers locate defects more quickly, but reviewer-speed and explanation-quality claims require empirical validation across expertise levels, case complexity, interface design, and organizational incentives. A slower review may be appropriate where the ledger reveals obligations that a faster workflow ignored.

## 8 Evidence Ledger

**DERIVED.** The evidence ledger is append-oriented and keyed by request and branch identity. Each entry records the claim identifier, producing actor or stage, input references, transformation, outcome state, required obligations, verifier results, authority rank, receipt references, trust vector, taint set, timestamp, and supersession link.

| Claim | Status | Formal or evidential anchor | What it does not establish |
|---|---|---|---|
| Observation preservation composes | FORMALIZED | `preserves_comp`; `COMP_C02_observation_preservation` | Adequacy of the chosen observation |
| Failure survives payload mapping | FORMALIZED | `map_never_upgrades_failure` | Recovery or external runtime conformance |
| Required obligations are nonempty | FORMALIZED | `requiredObligations_nonempty` | Completeness of the obligation taxonomy |
| Verifier acceptance entails the stated goal under soundness | FORMALIZED | `sat_sound`; `CORE_24_sat_sound` | Soundness of an arbitrary executable verifier |
| Trust meet cannot improve either input | FORMALIZED | `trust_meet_le_left/right`; `COMP_C01` | Probabilistic reliability or calibration |
| Same-level consensus does not raise authority | FORMALIZED | `consensus_does_not_escalate` | Correct assignment of real-world authority |
| Human receipt is task-, input-, time-, and revocation-sensitive | FORMALIZED | `receipt_not_reusable_across_tasks/inputs`; expiry and revocation theorems | Competence or correctness of the human judgment |
| Repetition and majority do not wash taint | FORMALIZED | `majority_cannot_clean`; `repetition_does_not_clean` | A validated real-world remediation method |
| Multi-agent performance benefits | CONJECTURE | Proposed comparative evaluation | Accuracy, independence, calibration, efficiency, or robustness |

**DERIVED.** Ledger inclusion is not endorsement. A false proposition, failed verifier run, revoked receipt, or rejected branch remains recordable evidence about the process. Current disposition status is computed from valid linked entries rather than inferred from the mere presence of a document.

**DERIVED.** Evidence references identify what was inspected and how it entered the workflow. They do not establish authenticity by themselves. A locator, timestamp, or digital signature may support a specified provenance obligation, but source truth depends on the semantics and institutional reliability of the acquisition process.

**DERIVED.** For the worked case, the ledger connects the ambiguous scan, OCR output, two branches, rule representation, calendar traces, source-resolution receipt, final human-action record, and supersession of `B14`. A later reviewer can isolate whether disagreement concerns the observed record, encoded rule, arithmetic, or recorded human disposition.

**DERIVED.** The ledger must not replace substantive reasons with opaque status badges. Any `satisfied` entry identifies the obligation, evidence, verifier or issuer, and scope. Any `unresolved` entry remains visible in exported dispositions unless an explicit policy bars issuance altogether.

## 9 Verification Boundary

**FORMALIZED.** Inside the Lean boundary lie datatype invariants and conditional theorems: composition of `Preserves`; `Outcome.map` failure non-upgrade; nonempty required obligations; verifier soundness relative to `Sat`; trust-meet lower bounds; authority and consensus bounds; receipt task, input, time, and revocation validity; taint joins; and request or branch identity constraints.

**DERIVED.** Outside the Lean boundary lie source authenticity, completeness of retrieved law, semantic fidelity of OCR, present legal force, choice-of-law analysis, factual findings, institutional authority assignments, external runtime refinement, probability, calibration, agent independence, explanation quality, and legal correctness. These propositions require evidence or judgment not supplied by the internal proof.

**DERIVED.** Even a theorem named `CORE_24_sat_sound` should be read syntactically: for the formal verifier and specification denoted by those definitions, acceptance entails satisfaction. The name does not establish twenty-four real-world safeguards, deployed execution, or correctness under undisclosed assumptions.

**DERIVED.** The boundary follows a general verification principle: a proof establishes a conclusion only under its formal premises and semantics. Enlarging the theorem name, agent count, test suite, or documentation cannot strengthen premises that were never encoded.

## 10 Limitations

**DERIVED.** The architecture depends on correct modeling of claim classes, obligations, authority ranks, taint categories, and receipt scopes. It can expose missing evidence only when the corresponding obligation exists. An incomplete specification may therefore be internally sound yet practically inadequate.

**DERIVED.** Trust meets and taint joins are intentionally coarse. They preserve deficits but do not quantify their likelihood, interaction, or materiality. They may require domain-specific refinement where one defect subsumes another or where remediation has graded effects.

**CONJECTURE.** Conservative propagation may increase review workload, delay issuance, or generate excessive unresolved states in some institutions; these efficiency and reviewer-speed effects require empirical validation. Interface design and obligation granularity may materially affect the burden.

**CONJECTURE.** Human receipts may improve accountability or legal correctness only if issuers understand the reviewed materials, possess genuine authority, and resist automation bias. Those conditions and any resulting improvement require empirical validation. A signed receipt can record responsibility without proving that the judgment was competent.

**DERIVED.** The model does not settle contested jurisprudential questions about what counts as legal authority, valid interpretation, or institutional legitimacy. It represents an organization’s declared authority structure and prevents computational escalation beyond it.

## 11 Declarations

### Funding

No external funding was received for this work.

### Conflict of Interest

The author declares no conflict of interest.

### Data Availability

No empirical dataset was generated or analyzed. The worked case is a theoretical example and does not represent a real legal matter.

### Ethics

This theoretical study involved no human participants, personal data, clinical intervention, or adjudication of an actual case.

### Author Contributions (CRediT)

Laupinco: Conceptualization; Formal Analysis; Methodology; Investigation; Writing—Original Draft; Writing—Review and Editing.

### AI Usage Disclosure

Generative AI assisted in drafting and organizing the manuscript. The author remains responsible for the paper’s claims, citations, formal specifications, and final text. No AI output is presented as legal advice or as proof of substantive legal correctness.

## References

**DERIVED.** Full bibliographic records for cited works are listed in `paper/references.bib`. Actually used citation keys are: [@LegalMathModeling2026], [@Dung1995], [@PrakkenSartor1997], [@ModgilPrakken2013], [@Reiter1980], [@Horn1951], [@Tarski1955], [@CousotCousot1977], [@FentonNeilLagnado2013], [@VlekEtAl2015], [@FentonNeilBerger2016], [@RibeiroEtAl2016], [@Lipton2018], [@GuidottiEtAl2018], [@WachterEtAl2018], [@DeMouraUllrich2021], [@Mathlib2020], and [@Hoare1969].
