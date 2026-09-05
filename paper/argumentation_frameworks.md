# Request-Bound Structured Argumentation and Finite Dung Semantics

**Author:** Laupinco

## Abstract

This paper reconstructs the argumentation component of `legal-math-modeling` as a formally bounded pipeline from rule support to semantic extensions. The pipeline does not treat a set of premises as an argument, an asserted conflict as an attack, an attack as a defeat, or a semantic extension as an adjudicated legal outcome. A canonical argument is a finite labelled support hypergraph whose dependencies are well founded, request-bound, available, and connected to a root conclusion. A typed attack carries a kind and a nonempty witness. A separate defeat policy resolves validated attacks before a finite Dung framework is constructed. The repository then defines grounded, complete, preferred, and stable semantics, proves a finite grounded fixed point and leastness result, proves existence of preferred extensions, and supplies powerset reference enumerators with soundness and completeness theorems. Extension families are bound to scenarios, assumptions, profiles, and branch identities; skeptical, credulous, refuted, undecided, inconsistent, and excluded query states remain distinct. Every claim is labelled `FORMALIZED`, `DERIVED`, or `CONJECTURE`. The formal results establish structural and semantic invariants for declared finite inputs. They do not prove that the premises are true, the attack policy is legally correct, every argument has been generated, or any semantic extension is legally authoritative.

## 中文摘要

本文重构 `legal-math-modeling` 的论证层：从 Horn 支持闭包，经结构化论证与类型化攻击，进入有限 Dung 语义，再到分支绑定查询。模型明确区分前提集合、论证、攻击、击败、语义扩展与裁判结果。规范论证是带标签的有限支持超图；类型化攻击必须具有非空见证并绑定同一请求；攻击只有经过外部击败政策才进入 Dung 图。仓库形式化了 grounded、complete、preferred、stable 语义，证明 grounded 最小不动点与 preferred 扩展存在，并给出有限 powerset 参考枚举器的可靠性和完备性。本文逐项标注 `FORMALIZED`、`DERIVED`、`CONJECTURE`。这些证明不证明事实真实、攻击政策合法、生产生成器全量完备，也不把语义扩展等同于司法裁判。

**Keywords:** abstract argumentation; structured arguments; Dung semantics; legal reasoning; skeptical acceptance; credulous acceptance; Lean

## 1. Research questions and proof labels

The study asks five questions. What mathematical identity should an argument have when duplicate storage and traversal order are irrelevant but rule labels and dependency paths matter? What conditions exclude fabricated subproofs, cyclic derivations, and cross-request support? How should typed attacks become binary defeats without hiding the policy decision? Which finite semantic results are actually proved? Finally, how should a query report distinguish disagreement, refutation, exclusion, and incomplete evaluation?

The answers are stated relative to the repository’s finite normal form [@LegalMathModeling2026]. `FORMALIZED` identifies Lean definitions or theorems. `DERIVED` identifies paper-level consequences, worked instances, or faithful mathematical restatements without a dedicated theorem. `CONJECTURE` identifies claims not established in Lean. This convention is essential because an argumentation formalism can be mathematically correct while its facts, rules, priorities, or institutional uses remain legally contestable.

## 2. Related work

Dung’s abstract argumentation framework models arguments as nodes and attacks as a binary relation [@Dung1995]. Legal argumentation often requires more structure: premises, rules, exceptions, burdens, preferences, and attack types matter [@PrakkenSartor1997; @BenchCapon2003; @BenchCaponSartor2003; @ModgilPrakken2013]. Case-based reasoning adds analogical relations that cannot be inferred from Dung edges alone [@RisslandAshley1987]. Nonmonotonic legal reasoning warns that adding information can defeat a previously justified conclusion [@Horty2011].

The present architecture preserves the Dung abstraction only after structured inputs have passed a bridge. This resembles systems in which an attack succeeds as a defeat only after preference or authority resolution. Yet the repository does not formalize a general preference logic. Its `DefeatPolicy` is a supplied Boolean function. The Lean theorem proves provenance of resolved defeats, not the legal merit of the supplied policy.

## 3. From Horn support to position candidates

Let a finite Horn system be (H=(U,F_0,R)), with immediate-consequence operator

$$
T_H(S)=F_0\cup
\{head(r)\mid r\in R,\ premises(r)\subseteq S\}.
\tag{1}
$$

`FORMALIZED`: `HornDefinitions.TH` implements (1) and proves monotonicity. Iteration begins from no derived atoms:

$$
I_0=\varnothing,\qquad I_{n+1}=T_H(I_n).
\tag{2}
$$

The finite support closure is

$$
C_H=I_{|U|},\qquad T_H(C_H)=C_H,\qquad
T_H(S)=S\Rightarrow C_H\subseteq S.
\tag{3}
$$

`FORMALIZED`: `ULM07HornSupport.supportClosure_fixed` and `supportClosure_least` establish the fixed-point and leastness clauses. Each atom also carries the request key, and every member of the closure is proved request-bound.

A position candidate (c) is valid relative to (H) exactly when

$$
CandidateWF(H,c)\Longleftrightarrow
c.request=H.request\land c.support\subseteq C_H.
\tag{4}
$$

`FORMALIZED`: `generateCandidates` filters a finite pool by (4), and membership implies candidate well-formedness. This is candidate soundness relative to the supplied pool and support closure. It is not a theorem that the pool contains every legally relevant position. Such global generation completeness is `CONJECTURE`.

Horn support and argument acceptance must not be conflated. \(q\in C_H\) says that \(q\) is derivable in the declared monotone rule system. It does not say that an argument concluding \(q\) survives undercut, rebuttal, exception, authority, scope, or procedural attack.

## 4. Canonical arguments as support hypergraphs

A support hyperedge has a request, a rule identifier, a finite nonempty premise set, and one conclusion. Several hyperedges may share a conclusion, representing alternative support routes. A canonical argument is

$$
a=(request_a,root_a,B_a,E_a),
\tag{5}
$$

where (B_a) is the finite set of base premises and (E_a) the finite set of labelled support hyperedges. `FORMALIZED`: this is the carrier in `ULM08ArgumentConstruction.CanonicalArgument`. Identity is structural: it includes the full finite hypergraph. Finsets quotient duplicate storage and traversal order, but distinct rule labels or support edges remain distinct.

Direct dependence is

$$
p\prec_a q\Longleftrightarrow
\exists e\in E_a,\ p\in premises(e)\land conclusion(e)=q.
\tag{6}
$$

Reachability and availability are

$$
Reach_a(x)\Longleftrightarrow
x=root_a\lor \operatorname{TransGen}(\prec_a)(x,root_a),
\tag{7}
$$

$$
Available_a(x)\Longleftrightarrow
x\in B_a\lor\exists e\in E_a,\ conclusion(e)=x.
\tag{8}
$$

Equations (6)–(8) are `FORMALIZED`. They prevent an edge from citing an intermediate node that neither appears as a base premise nor arises as another actual edge conclusion.

The well-formedness predicate entails

$$
\begin{aligned}
ArgumentWF(a)\Rightarrow{}& root_a.request=request_a,\quad Available_a(root_a),\\
&\forall e\in E_a,\ premises(e)\neq\varnothing,\\
&\forall e\in E_a\ \forall p\in premises(e),\ Available_a(p),\\
&\forall x\in B_a,\ Reach_a(x),\quad WellFounded(\prec_a).
\end{aligned}
\tag{9}
$$

`FORMALIZED`: the actual structure additionally proves request equality and dependency-subset conditions for base and edge premises. Because (prec_a) is well founded, a concrete argument cannot contain an infinite descending support chain. The global rule graph may still be cyclic; the theorem concerns each concrete derivation.

## 5. Relative construction coverage

The repository avoids an unbounded completeness claim. It defines

$$
Coverage(Expected,Actual)\Longleftrightarrow Actual=Expected.
\tag{10}
$$

`FORMALIZED`: a Boolean equality checker is sound and complete for (10). It also proves

$$
Actual=Expected\land
(\forall a\in Expected,ArgumentWF(a))
\Rightarrow
\forall a\in Actual,ArgumentWF(a).
\tag{11}
$$

This is useful for a frozen finite fixture whose expected carrier has been independently justified. It does not prove that the expected carrier is complete with respect to law, a natural-language corpus, or an unrestricted rule language. The checker does not decide `WellFounded`. Therefore “the production argument generator is complete” is `CONJECTURE` unless a runtime refinement theorem binds that generator to the formal carrier.

## 6. Typed attacks and directed refutation

The attack vocabulary contains rebut, undermine, undercut, exception, authority, scope, and procedure attacks. A typed attack is

$$
\alpha=(attacker_\alpha,target_\alpha,kind_\alpha,witness_\alpha).
\tag{12}
$$

Its well-formedness condition is

$$
AttackWF(\alpha)\Longleftrightarrow
witness_\alpha\neq ""\land
attacker_\alpha.request=target_\alpha.request.
\tag{13}
$$

Both are `FORMALIZED` in `ULM09AttackDefeat.lean`. The witness is a nonempty string, so the theorem establishes presence, not semantic adequacy. `CONJECTURE`: every nonempty witness is a valid legal reason. A future refinement would replace the string by a typed evidence object and establish kind-specific obligations.

Query refutation is directed:

$$
Refutes_R(x,y)\Longleftrightarrow
\exists r\in R,\ r.request=request\land r.refuter=x
\land r.target=y\land x\neq y.
\tag{14}
$$

`FORMALIZED`: `queryRefutes_irreflexive` proves that a query does not refute itself. Symmetry is not assumed. Two claims are contradictory only when both directed refutations occur.

## 7. From attacks to defeats

The validated attack set contains only attacks satisfying (13) and proves that every attacker belongs to one request. A policy $\pi$ then resolves attacks:

$$
D_\pi=\{(attacker_\alpha,target_\alpha)\mid
\alpha\in Attacks\land\pi(\alpha)=\top\}.
\tag{15}
$$

`FORMALIZED`: membership has an exact witness characterization:

$$
(x,y)\in D_\pi\Longleftrightarrow
\exists\alpha\in Attacks,\
\pi(\alpha)=\top\land attacker_\alpha=x\land target_\alpha=y.
\tag{16}
$$

The repository further proves that the source attack is well formed and that both endpoints preserve the input request. Thus the Dung layer cannot receive a resolved edge invented by the bridge. The policy is intentionally external. `CONJECTURE`: it implements a correct doctrine of priority, burden, exception, or authority.

## 8. The request-bound Dung framework

The resolved framework is (AF=(r,A,D)). Its well-formedness requires

$$
\forall a\in A,\ a.request=r\land ArgumentWF(a),
\qquad
\forall(x,y)\in D,\ x\in A\land y\in A.
\tag{17}
$$

`FORMALIZED`: `resolveToDefeatAF_wellFormed` proves (17). Internal support graphs remain inside canonical arguments; only resolved binary defeat edges enter Dung semantics.

For \(a\in A\), attackers and defense are

$$
Att(a)=\{b\in A\mid(b,a)\in D\},
\tag{18}
$$

$$
Defends(S,a)\Longleftrightarrow
\forall b\in A,\ (b,a)\in D\Rightarrow
\exists c\in S,\ (c,b)\in D.
\tag{19}
$$

The characteristic function is

$$
F_{AF}(S)=\{a\in A\mid Defends(S,a)\}.
\tag{20}
$$

Equations (18)–(20) are `FORMALIZED` in `ULM10DungProfiles.lean`. The implementation proves monotonicity of (F_{AF}), enabling finite fixed-point iteration.

## 9. Grounded semantics

Starting from ($\varnothing$), define

$$
G_n=F_{AF}^{n}(\varnothing),\qquad G=G_{|A|}.
\tag{21}
$$

The fixed-point and leastness theorems are

$$
F_{AF}(G)=G,\qquad
F_{AF}(S)=S\Rightarrow G\subseteq S.
\tag{22}
$$

These are `FORMALIZED`. `groundedExtension_is_grounded` packages them, and `grounded_unique` proves uniqueness for the repository’s predicate. A grounded extension may be the empty set. The family containing it, \(\{\varnothing\}\), is not an empty family. `FORMALIZED`: `singletonEmptyFamily` records this distinction. Therefore “no accepted arguments” does not mean “no extension.”

## 10. Complete, preferred, and stable semantics

Conflict freedom is

$$
CF(S)\Longleftrightarrow S\subseteq A\land
\forall a,b\in S,\ (a,b)\notin D.
\tag{23}
$$

Admissibility and completeness are

$$
Adm(S)\Longleftrightarrow CF(S)\land
\forall a\in S,Defends(S,a),
\tag{24}
$$

$$
Complete(S)\Longleftrightarrow Adm(S)\land F_{AF}(S)=S.
\tag{25}
$$

Preferred and stable semantics are

$$
Preferred(S)\Longleftrightarrow Adm(S)\land
\forall T,Adm(T)\land S\subseteq T\Rightarrow T\subseteq S,
\tag{26}
$$

$$
Stable(S)\Longleftrightarrow CF(S)\land
\forall a\in A\setminus S,\exists b\in S,(b,a)\in D.
\tag{27}
$$

All predicates are `FORMALIZED`. The repository requires admissibility in `Complete`; fixed-point equality alone is insufficient because a self-defending but conflicting set can otherwise satisfy the characteristic equation.

Reference extension families filter the finite powerset:

$$
PrefExt(AF)=\{S\subseteq A\mid Preferred(S)\}.
\tag{28}
$$

`FORMALIZED`: membership iff the semantic predicate holds. Preferred enumeration is sound and complete, and a preferred extension exists because the finite admissible family contains $\varnothing$ and has an inclusion-maximal member. Stable-extension existence is not claimed.

## 11. Profile-bound evaluation and branch queries

The selected extension family is

$$
Ext_p(AF)=
\begin{cases}
\{G\},&p=grounded,\\
PrefExt(AF),&p=preferred,\\
StableExt(AF),&p=stable,\\
CompleteExt(AF),&p=complete.
\end{cases}
\tag{29}
$$

`FORMALIZED`: `evaluateProfile` returns `noExtension` only with an emptiness proof, or a nonempty family exactly equal to (29). An incomplete result has nonempty obligations and proves only that discovered extensions satisfy the selected profile.

A branch key contains scenario, assumptions, profile, and extension. Composition requires

$$
Composable(x,y)\Longleftrightarrow x.branch=y.branch.
\tag{30}
$$

`FORMALIZED`: different branches cannot be one legal outcome. This blocks selecting favorable claims from incompatible preferred extensions.

Within an extension,

$$
Accepted(E,q)\Longleftrightarrow
\exists a\in E,\ conclusion(a)=q,
\tag{31}
$$

$$
Refuted(E,q)\Longleftrightarrow
\exists a\in E,\ QueryRefutes(conclusion(a),q).
\tag{32}
$$

Skeptical and credulous status are

$$
Common(q)\Longleftrightarrow\forall E\in\mathcal E,Accepted(E,q),
\tag{33}
$$

$$
Possible(q)\Longleftrightarrow\exists E\in\mathcal E,Accepted(E,q).
\tag{34}
$$

These are `FORMALIZED`, together with common and possible refutation. The model also defines

$$
UndecidedSome(q)\Longleftrightarrow
\exists E\in\mathcal E,\ Enterable(E,q)\land
\neg Accepted(E,q)\land\neg Refuted(E,q),
\tag{35}
$$

$$
InconsistentSome(q)\Longleftrightarrow
\exists E\in\mathcal E,\ Enterable(E,q)\land
Accepted(E,q)\land Refuted(E,q).
\tag{36}
$$

Both are `FORMALIZED`. Enterability and exclusion require positive witnesses; a gate may instead be incomplete with nonempty obligations. `undecided_requires_enterable` prevents an incomplete gate from being repackaged as undecided.

## 12. Worked finite examples

Consider \(A=\{a,b\}\) and \(D=\{(a,b)\}\). `DERIVED`: \(a\) has no attackers, so \(a\in F(\varnothing)\). Argument \(b\) is attacked by \(a\), and the empty set does not counterattack \(a\), so \(b\notin F(\varnothing)\). The grounded extension is \(\{a\}\). It is also stable because it attacks every argument outside it. This evaluates the definitions; it is not a named repository theorem.

Now let \(D=\{(a,b),(b,a)\}\). `DERIVED`: \(F(\varnothing)=\varnothing\), so the grounded extension is empty. The preferred extensions are \(\{a\}\) and \(\{b\}\). A query concluded by \(a\) is possible but not common. Combining it with a query concluded only by \(b\) would violate branch identity if outputs came from different extensions.

Finally, let a self-attack ((a,a)) be present. The ULM attack carrier does not globally forbid self-attacks at the Dung level, although directed query refutation is irreflexive. `DERIVED`: ({a}) is not conflict-free. This shows why fixed-point equality cannot alone define complete semantics.

These examples are mathematical, not factual legal cases. No legal conclusion should be attached to (a) and (b) without source-bound interpretation.

## 13. Structural identity and auditability

The choice of full structural identity deserves attention because many software systems identify an argument by a digest, database key, or conclusion. Those identifiers are useful engineering projections but are not the mathematical argument in this model. Two arguments may have the same conclusion and even the same base premises while relying on different rules or intermediate support. If they were collapsed, an undercut directed at one inference could incorrectly defeat the other. `DERIVED`: preserving the support hypergraph makes rule-specific attacks representable. This conclusion follows from the fields of `CanonicalArgument`, although the repository does not state it as a named theorem.

The same argument can also carry assumption dependencies through its tagged atoms. The well-formedness structure requires each premise dependency set to be a subset of the conclusion dependency set. This direction means a conclusion cannot silently claim fewer dependencies than the premises used to establish it. `FORMALIZED`: the subset fields are part of `ArgumentWF`. `DERIVED`: an explanation can conservatively report the root dependency set as covering every dependency admitted by the checked edges. `CONJECTURE`: that root set is minimal. No minimality theorem for dependencies is present.

Request identity is repeated at several layers. A tagged atom has a request; the support system has a request; a candidate has a request; the argument and each support edge have requests; the validated attack set and Dung framework have requests. These equalities are not merely database hygiene. They state local refinement boundaries. If an implementation combines support from two cases and then assigns a fresh request identifier to the result, it may satisfy a superficial output schema while violating the formal premises. `FORMALIZED`: generated candidates, supported positions, resolved defeats, and the resolved framework preserve the relevant request equalities. `CONJECTURE`: all external serialization and runtime calls preserve them; that needs separate cross-runtime evidence.

An auditable argumentation report can therefore expose at least five layers: admitted or assumed premise origin, Horn support membership, structural argument edges, typed attacks and their witnesses, and resolved defeat plus selected semantic profile. `DERIVED`: this layered report is reconstructible from the formal carriers. It should not collapse the layers into a single reason string, because a reader must be able to distinguish why a conclusion was derivable from why it was accepted.

## 14. Adversarial cases the formal carrier blocks

First consider a dangling-premise attack. An implementation emits an argument edge with premise (p), but (p) is neither a declared base premise nor the conclusion of any support edge. The argument may still look like a graph when serialized. `FORMALIZED`: `edgePremisesAvailable` rules it out under `ArgumentWF`. A report that has not established `ArgumentWF` cannot rely on this protection.

Second consider a disconnected argument. Every edge uses available premises, but one component does not reach the designated root. `FORMALIZED`: `baseReachesRoot` and `edgeReachesRoot` exclude it. This matters because otherwise irrelevant evidence could be attached to an argument and later presented as support for the conclusion. The theorem ensures structural relevance as reachability, not substantive legal relevance.

Third consider a cyclic derivation: (p) supports (q), while (q) supports (p), with neither grounded in an independent base premise. `FORMALIZED`: well-foundedness of direct dependence excludes such a concrete canonical argument. A global legal rule base may have cycles, but a particular accepted argument must exhibit a finite well-founded derivation. This separation permits cyclic rule theories without licensing circular proofs.

Fourth consider an empty attack witness. A system asserts an undercut but provides no basis. `FORMALIZED`: `AttackWF` requires the witness string to be nonempty, and validated attack sets admit only well-formed attacks. The protection is deliberately weak: the string “because” is nonempty. Content verification remains an external obligation. A typed evidence refinement is future work.

Fifth consider endpoint invention. The attack set contains only arguments (a) and (b), but the abstraction emits defeat ((c,b)) for a new argument (c). `FORMALIZED`: the image characterization of `resolveDefeat` and the endpoint condition of `DefeatAF.WellFormed` exclude this when the bridge premises hold. Every defeat pair traces to an input attack, and every attack endpoint belongs to the argument carrier.

Sixth consider semantic laundering. Preferred evaluation yields two incompatible extensions. A presentation layer selects the strongest-looking claim from each and merges them. `FORMALIZED`: branch artifacts compose as one outcome only when their full branch keys agree. Because the extension is part of the key, cross-extension merging is rejected. This structural rule does not stop a human from comparing branches; it stops the comparison from masquerading as one jointly supported outcome.

Seventh consider status laundering. A stable evaluator has not finished exploring candidates, yet a caller interprets the absence of a reported extension as proof that none exists. `FORMALIZED`: `IncompleteEvaluation` carries nonempty obligations, while `EvalResult.noExtension` requires equality of the reference family with the empty set. The constructors are distinct. The later procedure module preserves the distinction by mapping incomplete evaluation to `solverIncomplete`.

Eighth consider refutation by absence. A query is not concluded by any argument in an extension, so a caller labels it refuted. `FORMALIZED`: `RefutedIn` requires an actual argument whose conclusion stands in the directed `QueryRefutes` relation to the query. Absence of acceptance is compatible with undecided, excluded, incomplete, or refuted states and is not itself a refuter.

These adversarial cases show why the model contains more structure than a bare Dung graph. The Dung semantics remains standard; the surrounding carriers make its inputs and outputs accountable.

## 15. Semantics as views, not truth values

Grounded, preferred, complete, and stable semantics should be read as views over a fixed defeat graph. Grounded returns one least fixed point. Preferred may return several maximal admissible sets. Complete may include intermediate fixed points. Stable imposes the stronger condition that every outside argument is attacked and may have no solution. None is designated by the mathematics as the legally correct profile for every task.

`DERIVED`: skeptical acceptance is stronger than credulous acceptance for a nonempty extension family. If a claim occurs in every extension, it occurs in at least one. The repository has the definitions necessary for this implication but does not expose a named theorem. The nonemptiness premise is essential. `ExtensionFamily` carries it precisely so universal statements do not become vacuously true over an empty family.

The profile registry and request key make semantic choice explicit. `FORMALIZED`: the output of `evaluateProfile` remembers the selected profile, and the grounded and preferred evaluators return families tied to their profiles. `DERIVED`: changing profile changes the subject of an evaluation even if the underlying arguments and defeats are identical. An implementation that changes from grounded to preferred without changing request or branch metadata would conceal a semantic change.

Semantic acceptance also differs from evidential weight. An argument may be accepted because it is unattacked, not because its premises are highly credible. Another may be rejected because of a single successful undercut even if its evidence is otherwise strong. `CONJECTURE`: a numerical strength model should override these statuses. The present repository intentionally leaves strength outside the Dung carrier and uses the prior defeat policy as the place where priority or authority may act.

## 16. Procedure after argumentation

The next repository layer prevents semantic acceptance from becoming self-executing adjudication. A `ProofFinding` is either satisfied or unmet, but it must be packaged in an `AdjudicationAuthority` whose rule matches the request query, whose consequences are bound to the request, whose reviewer is nonempty, and whose success and failure consequences are nonprocedural. A procedure-only status travels through another subtype.

`FORMALIZED`: semantic incompleteness becomes `solverIncomplete` regardless of whether an authority value is available. No-extension without authority becomes `pendingLegalJudgment`, not automatic failure. A procedural disposition takes precedence through its typed channel. These results establish that the argumentation semantics supplies an input to adjudication rather than adjudication itself.

This boundary is important for the interpretation of Dung semantics in law. A grounded extension can establish what the model accepts relative to a defeat graph. It cannot establish that a legal burden was met, because the burden rule and authorized finding are separate inputs. `DERIVED`: the architecture rejects the equation “accepted argument = legal decision.” `CONJECTURE`: a particular jurisdiction permits a named decision to be derived from a specific extension. Such a proposition requires source-bound legal judgment.

## 17. Evidence ledger

| Claim | Status | Source anchor | Boundary |
|---|---|---|---|
| Finite support closure is least fixed point | `FORMALIZED` | `ULM07HornSupport` | Relative to declared Horn system |
| Canonical argument has well-founded, connected support | `FORMALIZED` | `ULM08ArgumentConstruction.ArgumentWF` | Does not prove persuasive force |
| Coverage checker is exact for finite equality | `FORMALIZED` | `checkArgumentCoverage_sound/complete` | Not global generator completeness |
| Every resolved defeat has a well-formed source | `FORMALIZED` | `resolved_defeat_has_wf_source` | Policy correctness remains external |
| Structured bridge yields well-formed DefeatAF | `FORMALIZED` | `resolveToDefeatAF_wellFormed` | No runtime equivalence implied |
| Grounded is least fixed point and unique | `FORMALIZED` | `groundedExtension_fixed/least`, `grounded_unique` | Finite carrier only |
| Preferred enumeration is exact and nonempty | `FORMALIZED` | `preferredExtensions_sound/complete/nonempty` | No complexity claim |
| Stable families may be empty | `DERIVED` | `Stable`, `noExtension` | No existence theorem |
| Different branches cannot form one outcome | `FORMALIZED` | `different_branches_not_composable` | Does not choose proper branch |
| Defeat policy encodes correct law | `CONJECTURE` | none | Requires authorized legal premises |
| Production generator is globally complete | `CONJECTURE` | none | Frozen equality is insufficient |

## 18. Validation boundary

The Lean results validate definitions and implications for finite structured inputs. They do not validate input truth. A fact attestation is a formal object; the theorem does not determine whether the fact occurred. A rule identifier is preserved; the theorem does not determine whether the rule is in force. An attack witness is nonempty; the theorem does not assess its evidential force. A policy chooses successful attacks; the theorem does not establish lawful priority.

Nor does the package establish behavioral equivalence with every runtime. A production system may serialize identities, optimize enumeration, stream partial results, or call an external solver. Each implementation needs a refinement claim and subject-bound evidence. Test success is engineering evidence, not a theorem. Conversely, a theorem about the reference carrier does not show runtime inputs were complete.

The branch layer solves a structural problem but not a jurisprudential one. It proves that incompatible branches were not silently merged. It cannot decide which assumptions, profile, or extension a court should adopt. Grounded semantics may be a protected default, but a default is not an all-jurisdictions legal theorem.

## 19. Limitations and future work

`CanonicalArgument` uses finite sets and string-backed atom payloads. Full dependent typing of proposition content remains open. Well-foundedness is a proposition carried by expected arguments, not a Boolean property decided by the coverage checker. Attack witnesses are strings; a stronger system would define kind-specific evidence and prove that verified evidence establishes an attack condition.

`DefeatPolicy.succeeds` is unconstrained beyond being Boolean. Formalizing priorities requires order properties, ties, authority, exceptions, and revision. Powerset enumeration is exact but may be inefficient; optimized algorithms need refinements. The current model does not prove complexity bounds.

Natural-language interpretation, retrieval, citation correctness, and normalization remain outside the Dung proofs. Argument strength is not a scalar here. A Boolean defeat policy and extension semantics are not calibrated probabilities. Explanation quality has no human validation. The model does not formalize burdens of production and persuasion inside the characteristic function; authority-bound procedure is a later layer.

Future work may connect a production generator to the frozen structural reference, refine a typed priority policy, and certify optimized preferred/stable algorithms. Each proposal is `CONJECTURE`, not a hidden implication of the current package.

## 20. Threats to validity

The first threat is specification validity. The Lean kernel checks the propositions encoded in the modules, but an omitted condition will not be supplied by proof search. For example, `AttackWF` verifies a nonempty witness and request equality, not the truth of the witness. The paper mitigates this threat by stating the exact predicate and refusing to substitute a stronger natural-language claim.

The second threat is translation validity. Mathematical notation in this paper abbreviates finite-set Lean definitions. The characteristic function’s existential defender is implemented through nonemptiness of a filtered attacker set; the notation in equation (20) is extensionally equivalent but easier to read. Each `FORMALIZED` label refers to the source definition or named theorem, not to typography alone.

The third threat is implementation validity. A powerset reference definition may differ from an optimized runtime through serialization, ordering, timeout, truncation, or policy configuration. The paper makes no runtime-equivalence claim. A runtime must provide independent refinement evidence for the exact subject and profile.

The fourth threat is external validity. Finite abstract frameworks do not capture every feature of legal argument, including open texture, institutional hierarchy, remedies, temporal effect, evidentiary admissibility, and strategic procedure. The architecture can represent some of these as typed attacks or later procedure inputs, but representation capacity is not demonstrated coverage.

The fifth threat is doctrinal validity. References to legal argumentation motivate the architecture but do not establish that one semantics should govern a particular jurisdiction. That choice must be justified through source-bound legal work. The branch key ensures the choice is visible; it does not make the choice correct.

These threats are not cured by adding more theorem names. They require distinct responses: specification review, faithful notation, runtime refinement, empirical evaluation, and authorized legal judgment. Keeping these responses separate is part of the method.

## 21. Reproducibility protocol

The argumentation claims can be reproduced in layers. A reader should first inspect the finite Horn carrier, its request-bound tagged atoms, and the least-fixed-point theorem. The next checkpoint is the structural argument: verify that base premises and support edges belong to one request, that premise nodes are available, dependencies are retained, every component reaches the root, and direct support is well founded. Equality with an expected carrier should be reported separately from the independent proof that expected arguments are well formed.

The attack checkpoint requires an actual member of the validated attack set, a nonempty witness, request equality, and a positive decision from the identified policy. The resolved pair should then occur among the framework arguments. A bare pair in a JSON graph does not reproduce the bridge theorem unless this provenance is shown.

For semantics, a small framework can be evaluated directly from the characteristic function. Grounded iteration starts at the empty set and continues to the finite bound. Preferred, complete, and stable reference families are obtained from the powerset predicates. If an optimized solver is used, its equality with these reference families is an additional implementation claim. Timeout or truncation must be represented as incomplete rather than no-extension.

For queries, record the exact extension family and branch key. Report acceptance and refutation independently, then state whether the quantifier over extensions is universal or existential. Preserve gate exclusion and incompleteness as distinct states. Finally, identify the authority step, if any, that turns a semantic report into an adjudication input. Following this protocol reproduces the paper’s bounded claims while leaving the legal interpretation with the person or institution authorized to supply it.

## 22. Conclusion

The architecture makes six separations precise: support is not acceptance; a premise set is not a structural argument; an asserted attack is not a resolved defeat; a semantic extension is not an adjudication; absence is not refutation; and incompleteness is not no-extension. The finite Dung results are substantive and `FORMALIZED`: grounded fixed-point existence and leastness, preferred-extension existence, exact reference enumeration, and branch-sensitive queries. Their legal use remains conditional on source-bound facts, rules, policies, and authority.

## Declarations

**Funding.** No external funding was received.

**Conflict of Interest.** The author declares no competing interests.

**Data Availability.** Formal definitions and proof sources are available in the `legal-math-modeling` repository [@LegalMathModeling2026]. No private case material is included.

**Ethics.** No human participants or private legal files were used. The paper does not offer legal advice and does not automate institutional authority.

**CRediT Author Statement.** Laupinco: Conceptualization, Methodology, Software, Formal Analysis, Investigation, Writing—Original Draft, Writing—Review and Editing.

**AI Disclosure.** AI assistance was used for drafting and consistency checking. The author reviewed the formal anchors, claim labels, and prose and remains responsible for the final manuscript.

## References

References are maintained in `paper/references.bib` [@LegalMathModeling2026; @Dung1995; @PrakkenSartor1997; @ModgilPrakken2013; @BenchCapon2003; @BenchCaponSartor2003; @RisslandAshley1987; @Horty2011; @Horn1951; @Tarski1955; @DeMouraUllrich2021].
