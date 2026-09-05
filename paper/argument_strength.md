# Argument Strength Without Scalar Laundering: A Formal Boundary for Legal Computation

**Author:** Laupinco

## Abstract

Computational legal systems often speak of “argument strength” as if it were a single observable quantity. The `legal-math-modeling` repository does not prove such a scalar semantics. Instead, it formalizes several non-equivalent structures: request-bound Horn support, well-founded structural arguments, typed attacks with witnesses, a Boolean defeat policy, Dung extension semantics, a five-coordinate ordinal trust vector combined by meet, a rational linear deviation score attached read-only to normative solutions, and generic metric contraction theorems under explicit hypotheses. This paper uses those structures to separate what is machine-checked from what remains a modeling proposal. `FORMALIZED` claims correspond to current Lean definitions or theorems. `DERIVED` claims are paper-level consequences or finite examples. `CONJECTURE` claims introduce a scalar or probabilistic strength interpretation absent from the formal package. We show that structural validity, dialectical acceptability, evidence trust, empirical fit, and institutional authority cannot be safely collapsed into one compensatory number. A high empirical score cannot repair a missing legal authority; a strong proof coordinate cannot authenticate a source; an accepted argument need not be probable; and an unattacked argument need not be normatively persuasive. We propose a typed, noncompensatory reporting vector as a future design while preserving the repository’s proved non-upgrade and read-only invariants. The result is a rigorous account of argument-strength infrastructure that avoids claiming a Lean theorem for substantive persuasive force.

## 中文摘要

“论证强度”常被误写成单一可观测分数，但 `legal-math-modeling` 并未证明这种标量语义。仓库实际形式化的是若干不可互换的结构：请求绑定的 Horn 支持、良基结构论证、带见证的类型化攻击、布尔击败政策、Dung 扩展语义、按坐标 meet 聚合的五维序数信任向量、只读附着于规范解的有理数偏差分数，以及满足明确前提时的一般度量收缩定理。本文把当前 Lean 定义或定理标为 `FORMALIZED`，把纸面推导标为 `DERIVED`，把统一强度函数、概率解释或法律说服力模型标为 `CONJECTURE`。核心结论是：结构良态、辩证接受、证据信任、经验拟合与制度权限不能通过一个补偿性数字安全合并。

**Keywords:** argument strength; legal argumentation; trust vector; defeat policy; noncompensatory aggregation; formal methods; Lean

## 1. Research questions and method

This study asks what the repository actually proves about strength-like quantities, whether acceptance can be treated as a measure of strength, how trust coordinates compose, what role an empirical score may play, and which additional premises would be required for a scalar model. The method is evidence-first. A theorem is read from its formal carrier and premises. An intuitive interpretation is not allowed to strengthen that theorem.

Three labels govern the manuscript. `FORMALIZED` means the proposition is represented by a current Lean definition or theorem. `DERIVED` means the statement is an exact mathematical restatement, finite calculation, or architectural consequence without a dedicated theorem. `CONJECTURE` means the repository lacks a proof or sometimes lacks even the proposed carrier. These labels prevent a score implemented in code, a successful test, or a familiar name from being treated as proof of legal validity.

## 2. Related work

Abstract argumentation evaluates sets through conflict and defense [@Dung1995]. Structured legal argumentation adds priorities, attack types, burdens, and rule provenance [@PrakkenSartor1997; @BenchCapon2003; @BenchCaponSartor2003; @ModgilPrakken2013]. Value-based approaches show why acceptability may depend on audiences or ordering rather than an intrinsic scalar [@BenchCapon2003]. Nonmonotonic accounts explain why new attacks can withdraw prior acceptance [@Horty2011]. Probabilistic legal reasoning, by contrast, concerns uncertainty and evidential likelihood [@TaroniEtAl2014; @FentonNeilLagnado2013].

These traditions do not license free conversion between semantics. A Dung extension is not a posterior probability. A priority is not an empirical confidence. A proof term is not evidence that its factual premises are true. The present repository reflects this separation through distinct carriers rather than one universal score.

## 3. Five different meanings of strength

Let (a) be a canonical argument. At least five concepts might be called its strength:

$$
\Sigma(a)=
(S_{support}(a),S_{struct}(a),S_{dialectic}(a),
S_{trust}(a),S_{empirical}(a)).
\tag{1}
$$

Equation (1) is `CONJECTURE` as a unified reporting carrier. Its components refer to existing structures, but the tuple is not defined in Lean. Support asks whether premises and conclusions lie within a fixed Horn closure. Structural validity asks whether the support hypergraph is well founded and request-bound. Dialectical status asks whether the argument belongs to extensions under a selected defeat semantics. Trust records separate source, text, fact, proof, and authority coordinates. Empirical fit is an attached score that cannot rewrite the normative solution.

A scalar reduction would require

$$
Strength(a)=\Phi(\Sigma(a))\in\mathbb R.
\tag{2}
$$

Equation (2) is `CONJECTURE`. No such $\Phi$ exists in the ULM package. Without an independently justified aggregation rule, weights, calibration data, and decision threshold, calling any number “argument strength” is a policy choice.

## 4. Support is not strength

For a finite Horn system (H=(U,F_0,R)),

$$
T_H(S)=F_0\cup
\{head(r)\mid r\in R,\ premises(r)\subseteq S\}.
\tag{3}
$$

Iteration yields the least fixed support closure

$$
C_H=T_H^{|U|}(\varnothing),\qquad
T_H(C_H)=C_H,\qquad
T_H(S)=S\Rightarrow C_H\subseteq S.
\tag{4}
$$

Equations (3)–(4) are `FORMALIZED` in `HornDefinitions.lean`, `HornFixedPoint.lean`, and `ULM07HornSupport.lean`. A position candidate satisfies

$$
CandidateWF(H,c)\Longleftrightarrow
c.request=H.request\land c.support\subseteq C_H.
\tag{5}
$$

This is also `FORMALIZED`. None of these formulas orders candidates by persuasive force. The closure answers whether declared positive rules derive atoms. A conclusion supported through ten rules is not thereby stronger than one supported through a single decisive rule. Any path-count score is `CONJECTURE` and may reward duplicated or irrelevant structure.

## 5. Structural validity is not comparative weight

A canonical argument (a) has base premises (B_a), root (r_a), and labelled support hyperedges (E_a). Direct dependence is

$$
p\prec_a q\Longleftrightarrow
\exists e\in E_a, p\in premises(e)\land conclusion(e)=q.
\tag{6}
$$

`FORMALIZED`: `ArgumentWF` requires request equality, nonempty edge premises, availability, dependency inclusion, root reachability, and \(WellFounded(\prec_a)\). Relative construction coverage is

$$
Coverage(Expected,Actual)\Longleftrightarrow Actual=Expected.
\tag{7}
$$

with a `FORMALIZED` Boolean checker sound and complete for this finite equality.

These predicates are binary. An argument either satisfies the stated structural contract or it does not. Defining

$$
S_{struct}(a)=
\mathbf 1[ArgumentWF(a)]
\tag{8}
$$

is `DERIVED` notation for a Boolean classification, not a theorem that well-formed arguments are equally persuasive. A malformed argument should be rejected rather than assigned a slightly lower score. This is a boundary condition, not a compensable feature.

## 6. Attacks and the Boolean defeat policy

A typed attack $\alpha$ is well formed when

$$
AttackWF(\alpha)\Longleftrightarrow
\alpha.witness\neq ""\land
\alpha.attacker.request=\alpha.target.request.
\tag{9}
$$

The resolved defeat relation is

$$
D_\pi=\{(attacker_\alpha,target_\alpha)\mid
\alpha\in Attacks\land\pi.succeeds(\alpha)=\top\}.
\tag{10}
$$

Both are `FORMALIZED` in `ULM09AttackDefeat.lean`. The theorem `resolved_defeat_has_wf_source` proves that every pair in $D_\pi$ has a real well-formed source attack. It does not define a numerical attack weight or prove that $\pi$ makes the correct legal decision.

One might propose

$$
\pi.succeeds(\alpha)=
\mathbf 1[W(attacker_\alpha)>W(target_\alpha)].
\tag{11}
$$

Equation (11) is `CONJECTURE`. The actual policy is any function from typed attacks to `Bool`. A proper refinement would specify (W), ties, authority, exceptions, burden direction, and the evidence required for comparison. The current provenance theorem would still be useful, but it would not prove the new comparison rule.

## 7. Dialectical acceptability is set-valued

For a fixed (AF=(A,D)), defense is

$$
Defends(S,a)\Longleftrightarrow
\forall b\in A,\ (b,a)\in D\Rightarrow
\exists c\in S,\ (c,b)\in D.
\tag{12}
$$

The characteristic function and grounded extension are

$$
F_{AF}(S)=\{a\in A\mid Defends(S,a)\},
\tag{13}
$$

$$
G=F_{AF}^{|A|}(\varnothing),\qquad
F_{AF}(G)=G,\qquad
F_{AF}(S)=S\Rightarrow G\subseteq S.
\tag{14}
$$

These are `FORMALIZED` in `ULM10DungProfiles.lean`. Complete, preferred, and stable semantics are also formally defined, and preferred extensions are proved to exist. Acceptability is therefore profile- and extension-dependent.

A profile-relative membership vector may be written

$$
S_{dialectic}(a,p)=
(\mathbf 1[Common_p(a)],\mathbf 1[Possible_p(a)],
\mathbf 1[Refuted_p(a)]).
\tag{15}
$$

Equation (15) is `DERIVED` from `FORMALIZED` query predicates, not a probability distribution. Its coordinates need not sum to one. In an inconsistent branch an argument’s conclusion can be accepted and refuted. Collapsing the vector to a scalar loses whether acceptance is skeptical, credulous, contested, excluded, or incomplete.

## 8. Trust is a coordinatewise order

The repository defines

$$
\tau(a)=
(\tau_{source},\tau_{text},\tau_{fact},
\tau_{proof},\tau_{authority})\in\{0,1,2\}^5.
\tag{16}
$$

Each coordinate is a `Fin 3` ordinal. Composition is

$$
(\tau\wedge\sigma)_i=\min(\tau_i,\sigma_i).
\tag{17}
$$

The proved non-upgrade law is

$$
\tau\wedge\sigma\preceq\tau,\qquad
\tau\wedge\sigma\preceq\sigma.
\tag{18}
$$

Equations (16)–(18) are `FORMALIZED` in `ULM14CoverageTrust.lean`. The meet is noncompensatory. Strong proof assurance cannot raise weak source assurance; authoritative input cannot repair a failed run check because run status lives in another field.

A weighted average

$$
\bar\tau=\sum_{i=1}^{5}\lambda_i\tau_i,\qquad
\lambda_i\ge0,\quad\sum_i\lambda_i=1
\tag{19}
$$

is `CONJECTURE` and is intentionally absent. It would permit compensation: four high coordinates could hide one fatal zero. If used for ranking, it must not replace the vector or the meet theorem.

## 9. Assurance fields do not collapse

An assurance envelope stores specification status, implementation assurance, run-check status, coverage, legal-input status, scope, open specification references, formal assumptions, trusted-computing-base references, and notices. Envelopes combine only when scopes agree. Open carriers combine by union:

$$
Open(C_1\sqcup C_2)=Open(C_1)\cup Open(C_2),
\tag{20}
$$

$$
Pending(L_1\sqcup L_2)=Pending(L_1)\cup Pending(L_2).
\tag{21}
$$

These equations and retention theorems are `FORMALIZED` in `ULM14CoverageTrust.lean`. A strength report must therefore remain incomplete when required evidence is missing. Adding a favorable argument cannot delete an unrelated implementation failure or pending legal input.

The assurance envelope is not a strength score. It describes whether different evidence channels are available within one scope. `DERIVED`: two arguments with equal semantic status can have different assurance envelopes. `CONJECTURE`: a universal total order ranks all such envelopes without losing decision-relevant distinctions.

## 10. Empirical scores are read-only annotations

The repository’s empirical artifact contains a set of normative solutions, rational score, and label. Attachment satisfies

$$
Attach(S,s).normativeSolutions=S.
\tag{22}
$$

This is `FORMALIZED` by `empirical_is_read_only`. The only declared score formula is

$$
D(w,x)=\sum_{i=1}^{n}w_ix_i.
\tag{23}
$$

Its decomposition is `FORMALIZED` by reflexivity in `ULM15IncrementalEmpiricalBanach.lean`. It establishes the arithmetic expression, not measurement validity.

A proposed empirical strength model might define

$$
S_{empirical}(a)=D(w,features(a)).
\tag{24}
$$

Equation (24) is `CONJECTURE`. The repository does not define `features(a)`, learn (w), specify a target variable, or prove calibration. Even if those steps were completed, equation (22) requires the normative solution to remain unchanged by attachment unless an authorized, separately specified policy consumes the score.

## 11. Metric structure and conditional convergence

For positive weights (w_i>0), the repository defines

$$
d_w(x,y)=\max_i\frac{|x_i-y_i|}{w_i}.
\tag{25}
$$

It proves nonnegativity, symmetry, triangle inequality, and point separation. These are `FORMALIZED` in `WeightedSupNorm.lean`. A theorem unfortunately named `weightedSupDist_complete` proves nonnegativity and \(d_w(x,y)=0\Leftrightarrow x=y\); it does not establish topological completeness.

For coordinate map (T), the hypotheses

$$
|T(x)_i-T(y)_i|\le\sum_jL_{ij}|x_j-y_j|,\qquad
\sum_jL_{ij}w_j\le q w_i
\tag{26}
$$

imply

$$
d_w(Tx,Ty)\le qd_w(x,y).
\tag{27}
$$

This implication is `FORMALIZED` in `ContractionCondition.lean`. The generic Banach module then proves, assuming a nonempty complete metric space and a contracting (f),

$$
\exists!x^*,\ f(x^*)=x^*,\qquad f^n(x)\to x^*,
\tag{28}
$$

and

$$
d(f^n(x),x^*)\le
\frac{K^n}{1-K}d(x,f(x)).
\tag{29}
$$

These are `FORMALIZED` conditional theorems. `CONJECTURE`: an actual legal-strength updater is contracting. No Lean definition connects argument strength to (T), (d_w), or a complete weighted vector space.

## 12. Why accepted does not mean strong

Consider \(A=\{a\}\), \(D=\varnothing\). `DERIVED`: \(a\) belongs to the grounded extension because it is unattacked. Nothing in the framework states that its premises are credible or its conclusion important. If the canonical argument is structurally well formed, the semantics evaluates it; the semantics does not independently audit the legal source.

Now let (A=\{a,b\}), (D=\{(b,a)}). `DERIVED`: grounded acceptance selects (b), even if a hypothetical external score gives (S(a)=100) and (S(b)=1). The Dung graph has no access to those numbers. Introducing them requires modifying the defeat policy or semantics and proving a new relation.

Conversely, an argument can have a high trust vector but be defeated by a valid exception. Trust of provenance does not entail dialectical survival. It can also be accepted in one preferred extension and rejected in another. Therefore

$$
Accepted_p(a)\not\Rightarrow Strength(a)\ge\theta,
\qquad
Strength(a)\ge\theta\not\Rightarrow Accepted_p(a)
\tag{30}
$$

is `DERIVED` as a non-entailment under the current language: `Strength` and \(\theta\) are not defined there. It is a warning against silently importing a scalar interpretation.

## 13. A noncompensatory proposal

A future report could preserve a typed vector

$$
Report(a)=
(WF_a,Support_a,ProfileStatus_a,\tau_a,
Assurance_a,Empirical_a,Authority_a).
\tag{31}
$$

Equation (31) is `CONJECTURE`. A gate would first require binary conditions such as structural well-formedness, exact request identity, no unresolved mandatory obligation, and valid authority. Only after those gates could an empirical ranking be displayed.

One possible partial order is componentwise dominance:

$$
R_1\preceq R_2\Longleftrightarrow
\forall i,\ R_{1,i}\preceq_i R_{2,i},
\tag{32}
$$

with incomparable reports left incomparable. This is `CONJECTURE`. It aligns with the current trust meet but requires orders for semantic and assurance components. It avoids manufacturing a total ranking when one argument has better source trust and another has stronger dialectical acceptance.

If a scalar is needed solely for user-interface sorting, it should be marked as a projection:

$$
SortKey(a)=\psi(Report(a)),
\qquad SortKey\text{ does not alter }Outcome(a).
\tag{33}
$$

This is `CONJECTURE`, with the second clause modeled after the `FORMALIZED` read-only empirical invariant. The projection should disclose weights, missing values, version, and scope.

## 14. Authority and consensus

The broader formal core ranks authority levels and requires a one-step receipt for promotion:

$$
receiptValid(r)\Longleftrightarrow
rank(r.to)=rank(r.from)+1.
\tag{34}
$$

For repeated agents at one authority level,

$$
consensusRank([l]^n)\le rank(l).
\tag{35}
$$

These are `FORMALIZED` in `ReceiptAuthority.lean`. More votes from equally situated models do not generate higher formal authority. Likewise, the taint module proves that duplicating or taking a majority over tainted input cannot make it clean.

Thus

$$
n\cdot\text{model agreement}\not\Rightarrow
\text{admitted formal input}
\tag{36}
$$

is `DERIVED` from those exact non-escalation properties. It is not a claim that ensembles never improve prediction. It says prediction agreement cannot itself issue the authority receipt required by the formal hierarchy.

## 15. Worked comparison without a scalar

Consider two structurally well-formed arguments (a) and (b) under one request. Argument (a) concludes the query through an admitted premise and one rule. Argument (b) concludes a refuter through two admitted premises and two rules. Suppose the policy resolves (b)'s rebuttal against (a) as a defeat. `FORMALIZED`: if the corresponding objects satisfy the ULM premises, both arguments preserve the request, the defeat has a witnessed source, and the resolved framework contains only declared endpoints. `DERIVED`: rule count alone does not decide which argument survives because the semantic graph uses defeat, not path length.

Assume a trust report gives

$$
\tau(a)=(2,2,2,2,1),\qquad
\tau(b)=(2,2,1,2,2).
\tag{37}
$$

Neither vector dominates the other componentwise. Argument (a) has stronger fact trust and weaker authority trust; (b) has the reverse. Their meet is

$$
\tau(a)\wedge\tau(b)=(2,2,1,2,1).
\tag{38}
$$

Equation (38) is `DERIVED` by evaluating the `FORMALIZED` meet. A weighted average could rank the arguments, but the result would depend on weights not supplied by the formal model. Leaving them incomparable preserves the actual information.

Now suppose empirical annotations assign (D_a=0.8) and (D_b=0.6). These numbers do not alter the normative solution sets because `attachEmpirical` is read-only. It would be invalid to reverse the defeat solely because (D_a>D_b) unless the policy explicitly consumes that score and its legal and empirical validity is established. `FORMALIZED`: attachment leaves solutions unchanged. `CONJECTURE`: the two numbers measure any meaningful outcome.

Finally suppose (a) is common under grounded semantics but only possible under preferred semantics. The profile is part of the request and branch identity. A user interface cannot report “strength 1.0” while omitting the profile without discarding the quantifier and branch. `DERIVED`: the same structural argument can have different dialectical statuses under different profiles. This is not instability in the object; it is a change in evaluation semantics.

The example demonstrates why the report vector is preferable to a scalar. It can say that (a) is well formed, supported, defeated or accepted under a named profile, associated with a five-coordinate trust vector, annotated by an empirical score, and awaiting or holding authority. Each statement has its own evidence. No arithmetic is needed to pretend that all dimensions share one unit.

## 16. Failure modes of scalarization

The first failure mode is compensation across hard gates. Suppose a score assigns positive weights to structural validity, source trust, and empirical fit. A malformed argument might receive a high total because its empirical feature is large. This is unacceptable where well-formedness is a precondition rather than a preference. A safe aggregation must use a gate:

$$
Eligible(a)=ArgumentWF(a)\land RequestBound(a)
\land RequiredEvidenceSatisfied(a).
\tag{39}
$$

Equation (39) is `CONJECTURE` as a combined predicate, though its components reflect formal structures. Only eligible arguments could enter optional ranking.

The second failure is unit confusion. Trust coordinates are ordinal, deviation scores are rational, extension status is logical, and authority is categorical. Adding them assumes cardinal scales and exchange rates between concepts. The expression

$$
0.2\tau_{source}+0.2\tau_{proof}+0.6D
\tag{40}
$$

is `CONJECTURE` and dimensionally ungrounded unless the scales have been validated. A larger ordinal label does not establish a linear increment in trust.

The third failure is double counting. Source quality may influence fact admission, attack policy, and empirical features. Summing all three can count the same evidence repeatedly. The current ULM does not define statistical independence or causal pathways, so independence-based aggregation is `CONJECTURE`.

The fourth failure is branch erasure. A score may average acceptance across incompatible preferred extensions. Yet branch non-mixing is `FORMALIZED`. An average can be displayed as an external analysis only if it preserves the extension family and does not assert that its components co-occur.

The fifth failure is missingness laundering. If an unknown coordinate is replaced by zero, it may be confused with verified low trust. If it is ignored, the average may rise. The assurance envelope instead retains pending references and open obligations as sets. Missingness is a state, not a number.

The sixth failure is authority substitution. Many model votes or a high-confidence classifier cannot issue a formal-input receipt. `FORMALIZED`: consensus of repeated equal-level agents does not increase authority rank. A scalar that increases with vote count must therefore remain predictive metadata, not authority evidence.

The seventh failure is temporal drift. A score learned on one version or as-of date may be applied after a source is superseded. The broader formal core rejects inactive source versions, but no score-calibration theorem handles temporal transfer. A strength score without version and scope is `CONJECTURE` and operationally unsafe.

## 17. Requirements for a future strength theory

A credible future theory must begin with a target. Possible targets include probability that an adjudicator accepts a claim, comparative priority under a specified doctrine, robustness of acceptance under bounded graph perturbation, quality of evidential support, or user-rated explanation usefulness. These targets are not interchangeable.

For a probabilistic target (Y), calibration would require

$$
\Pr(Y=1\mid \widehat p\in B)\approx
\mathbb E[\widehat p\mid\widehat p\in B]
\tag{41}
$$

over declared bins (B). Equation (41) is background-style `CONJECTURE`; no such dataset or theorem exists in the repository. Even perfect predictive calibration would not prove normative correctness.

For robustness, one might define

$$
Robust_p(a,k)=
\mathbf 1[\forall AF'\in N_k(AF),\ a\in Common_p(AF')].
\tag{42}
$$

Equation (42) is `CONJECTURE`. It requires a graph neighborhood (N_k), a perturbation policy, and exact semantics. Graph similarity cannot supply (N_k) by default because the repository’s earlier similarity score is not a metric.

For doctrinal priority, a typed order might be

$$
a\succ_{R,J,t} b,
\tag{43}
$$

indexed by rule set (R), jurisdiction (J), and time (t). Equation (43) is `CONJECTURE`. Its facts and authority must be source-bound, and its induced defeat policy needs proof obligations.

For evidential strength, a Bayesian or likelihood formulation would require hypotheses, evidence variables, dependencies, and validated likelihoods [@FentonNeilLagnado2013; @TaroniEtAl2014]. Nothing in the current `TrustVector` supplies those probabilities. Treating ordinal trust as a prior would be an unsupported conversion.

Finally, any strength theory must specify its interaction with normative output. A conservative requirement is

$$
Rank(a)\text{ may order presentation but may not change }Outcome
\text{ without an authorized rule}.
\tag{44}
$$

Equation (44) is `CONJECTURE`, motivated by the formal read-only empirical theorem. This preserves a path for research while keeping normative authority explicit.

## 18. Engineering acceptance criteria

A production strength component should be rejected unless it records request, branch, profile, feature definition, model version, target, training scope, missingness, and authority. Its output should be an `Outcome` rather than an unqualified number. Missing required inputs should produce a partial payload with nonempty obligations; invalid subjects or failed computation should produce failure.

Reference fixtures should test noncompensation. Lowering one trust coordinate must not be hidden by raising another when the formal meet is used. A failed run check must remain failed after aggregation. An incomplete semantic family must not receive a strength based only on discovered extensions unless the report explicitly limits its claim. Changing profile or policy must change subject identity.

Mutation tests should invert attack direction, drop a witness, erase an assumption dependency, replace a trust meet with maximum, let an empirical attachment overwrite normative solutions, or treat a missing authority as a default approval. Detecting these mutations gives engineering confidence that implementations respect the intended boundary. It does not prove the weights or legal policy correct.

The component should expose an evidence ledger alongside every output. The ledger identifies which fields are `FORMALIZED` consequences, which arise from runtime checks, which are empirical, and which depend on human legal judgment. A single confidence number without that ledger fails the acceptance criterion because it cannot show what evidence the number represents.

## 19. Evidence ledger

| Claim | Status | Source anchor | Boundary |
|---|---|---|---|
| Horn support is a finite least fixed point | `FORMALIZED` | `ULM07HornSupport` | No comparative strength |
| Canonical arguments have well-founded support | `FORMALIZED` | `ULM08.ArgumentWF` | No persuasive ranking |
| Resolved defeats have witnessed typed sources | `FORMALIZED` | `ULM09.resolved_defeat_has_wf_source` | Policy legality not proved |
| Grounded and preferred semantics are exact finite references | `FORMALIZED` | `ULM10DungProfiles` | Acceptance is not probability |
| Trust meet cannot exceed either input | `FORMALIZED` | `ULM14.trust_meet_le_left/right` | Ordinal coordinates only |
| Empirical attachment preserves normative solutions | `FORMALIZED` | `ULM15.empirical_is_read_only` | Score validity not proved |
| Deviation is a finite weighted sum | `FORMALIZED` | `ULM15.deviationScore_decomposes` | No learned weights or target |
| Scalar argument strength (Strength(a)) | `CONJECTURE` | none | No Lean carrier or calibration |
| Weighted strength determines defeat | `CONJECTURE` | none | Actual policy is arbitrary Bool |
| Ensemble agreement raises authority | rejected by `FORMALIZED` boundary | `consensus_does_not_escalate` | Predictive gain is a separate question |

## 20. Validation boundary

The formal package proves structural predicates and conditional mathematical results. It does not observe persuasion, estimate probabilities, validate evidence sources, or choose legal weights. `ArgumentWF` is not a psychometric scale. Dung membership is not an empirical frequency. `TrustLevel` is not a calibrated probability. `deviationScore` is not validated merely because the sum is formalized. Banach convergence is conditional on premises not proved for an argument-strength updater.

A production claim needs several independent evidence channels. Formal evidence checks the reference proposition. Runtime evidence checks an implementation on the exact subject. Empirical evidence evaluates a defined target using appropriate data. Legal evidence supplies sources and authorized interpretations. Human evaluation may test whether explanations or rankings are useful. No channel can be silently substituted for another.

## 21. Limitations

The model lacks a typed theory of evidential force, priority magnitude, burden thresholds, relevance, and value preferences. Attack witnesses are nonempty strings rather than verified evidence terms. The defeat policy has no laws. The trust scale has only three ordinal levels and no calibration. The empirical score is rational but semantically uninterpreted. No dataset links features to legally reviewed outcomes in this formal package.

The Dung reference semantics is finite and set-valued. It does not rank arguments within an extension. Powerset enumeration may be computationally expensive. The generic metric results are not connected to the Dung carrier. The authority hierarchy proves non-escalation but does not establish that a particular issuer is institutionally valid.

These limitations mean that the title “argument strength” names a research problem, not a solved scalar. The contribution is a disciplined decomposition and a set of non-laundering invariants.

## 22. Reproducibility protocol

To reproduce a strength claim, first identify its carrier. For support, recompute the Horn closure. For structure, inspect every `ArgumentWF` field. For dialectical status, record the profile and exact extension family. For trust, report all five ordinal coordinates and their scope. For empirical score, disclose features, weights, target, and the read-only relation to normative output. For authority, identify the receipt and issuer.

Next classify the claim. A current theorem receives `FORMALIZED`; a finite example receives `DERIVED`; a scalar interpretation receives `CONJECTURE`. Do not infer numerical meaning from ordinal levels or theorem names. In particular, do not call `weightedSupDist_complete` a complete-space theorem.

Finally, report missing obligations and failed checks without averaging them into a score. This protocol preserves falsifiability: a reader can inspect which component supports which sentence and can reject the proposed aggregation without disputing the proved structural invariants.

## 23. Interpretation rules for publication

Any publication using this framework should state strength claims in a typed sentence. “Argument (a) is supported” means its declared support is contained in the finite Horn closure for the named request. “Argument (a) is well formed” means the `ArgumentWF` fields have been supplied. “Argument (a) is accepted” must name a profile and, for non-singleton families, whether the quantifier is skeptical or credulous. “Argument (a) is trusted” must report all five coordinates and their provenance. “Argument (a) predicts an outcome” must state an empirical target and validation design. “Argument (a) is legally authoritative” must name the authority and scope.

These sentences cannot be replaced by “(a) has strength 0.87” unless a documented projection explains which sentence the number abbreviates. If the number combines several meanings, the underlying vector and hard gates must remain available. Otherwise readers cannot distinguish a high empirical estimate from a valid proof or an authorized legal finding.

The same rule applies to comparisons. The statement (a>b) is incomplete unless the ordering is named. It may mean that (a) has a higher empirical score, dominates (b) coordinatewise in trust, defeats (b) under a policy, occurs in more extensions, or has a higher presentation rank. These relations can disagree without contradiction. The repository proves some of them only as Boolean or set relations and does not prove a total comparative order.

Reports should also preserve negative information. If an argument is structurally invalid, the proper output is rejection or failure, not a low strength. If evaluation is incomplete, the output must carry open obligations, not an estimated acceptance. If a legal input is pending, the trust report must not hide it. If an empirical target is undefined, no default score should be fabricated.

This publication discipline is `DERIVED` from the formal carriers and evidence boundaries. It is not itself a Lean theorem, but it makes the theorem statements auditable. It also keeps room for plural theories of legal persuasion: researchers may propose competing strength models without rewriting the meaning of the existing formal predicates.

For archival reproducibility, the report should retain the exact source commit, theorem anchor, runtime subject, policy version, and branch key. A later paper can then distinguish a changed strength proposal from a changed formal object. Without this provenance, identical-looking numbers from different versions are not comparable. Version binding does not validate the score, but it prevents accidental substitution and makes independent criticism possible.

## 24. Conclusion

The repository does not prove a universal numerical strength of legal arguments. It proves something more precise: support closure, structural well-formedness, defeat provenance, finite extension semantics, non-upgrading trust composition, read-only empirical attachment, and conditional metric results. Treating those structures as separate prevents a high number from laundering a missing premise, failed implementation, incompatible branch, or absent authority. A future scalar or vector model may be useful, but it remains `CONJECTURE` until its carrier, aggregation, calibration, legal role, and refinement evidence are established.

## Declarations

**Funding.** No external funding was received.

**Conflict of Interest.** The author declares no competing interests.

**Data Availability.** Formal sources and public artifacts are available in the `legal-math-modeling` repository [@LegalMathModeling2026]. No private case data are used.

**Ethics.** No human participants or private legal records were used. The proposed reporting structures do not constitute legal advice or automated authority.

**CRediT Author Statement.** Laupinco: Conceptualization, Methodology, Software, Formal Analysis, Investigation, Writing—Original Draft, Writing—Review and Editing.

**AI Disclosure.** AI assistance was used for drafting and consistency checking. The author reviewed every claim label, formula, source anchor, and limitation and remains responsible for the manuscript.

## References

References are maintained in `paper/references.bib` [@LegalMathModeling2026; @Dung1995; @PrakkenSartor1997; @BenchCapon2003; @BenchCaponSartor2003; @ModgilPrakken2013; @Horty2011; @TaroniEtAl2014; @FentonNeilLagnado2013; @DeMouraUllrich2021; @Mathlib2020].
