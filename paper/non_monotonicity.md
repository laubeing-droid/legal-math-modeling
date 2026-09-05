# Monotone Support, Nonmonotone Acceptance, and Fail-Closed Revision

**Author:** Laupinco

## Abstract

Legal reasoning often combines monotone derivation with defeasible acceptance. This paper states that combination precisely for the `legal-math-modeling` repository. The Horn layer computes a finite least fixed point: enlarging the current support set cannot remove immediate consequences, and an add-only delta cannot shrink the bounded closure. The argumentation layer has a different role. It turns well-founded support hypergraphs and typed attacks into a resolved finite Dung framework, where acceptance depends on grounded, complete, preferred, or stable semantics. Adding a defeat may remove a previously accepted argument even though its Horn support remains derivable. The repository formally proves the Horn monotonicity, finite stabilization, add-only closure inclusion, Dung definitions, branch separation, and non-conversion of incomplete results. It does not currently contain a general Lean theorem characterizing how every semantic profile changes under arbitrary graph updates. We therefore label general nonmonotonicity claims `CONJECTURE` and finite paper counterexamples `DERIVED`, while reserving `FORMALIZED` for current Lean propositions. The result is an exact account of revision that avoids two opposite errors: calling all legal inference nonmonotone, and assuming that monotone rule closure makes legal acceptance monotone. A fail-closed outcome algebra and assurance envelope preserve open obligations, branch identity, and authority requirements across revision.

## 中文摘要

法律推理常把单调规则推导与可撤销接受混合在一起。本文基于 `legal-math-modeling` 明确区分二者：Horn 层计算有限最小不动点，增加支持不会删除立即后继，只增量事实与规则也不会缩小闭包；论证层则将结构化论证和类型化攻击转化为 Dung 击败图，grounded、complete、preferred、stable 接受状态可随新增击败而改变。仓库已形式化 Horn 单调性、有限稳定、只增量闭包包含、Dung 语义、分支隔离与未完成结果不转化；但尚未在 Lean 中证明任意图更新下各语义轮廓的一般变化定理。因此本文把一般性变化命题标为 `CONJECTURE`，把有限反例标为 `DERIVED`，只把当前 Lean 定理标为 `FORMALIZED`。

**Keywords:** nonmonotonic reasoning; Horn logic; defeasible reasoning; Dung semantics; legal revision; fixed points; fail-closed systems

## 1. Research questions

The paper asks: Which relation in the repository is monotone? With respect to what order? At which boundary can acceptance become nonmonotone? How are additions distinguished from retractions or policy changes? What formal mechanisms prevent revision from laundering an incomplete or unsupported conclusion into a completed legal status?

The three proof labels have their strict meanings. `FORMALIZED` means a corresponding Lean declaration or theorem is present. `DERIVED` means that a finite example or paper-level proposition follows directly from those definitions but lacks a named theorem. `CONJECTURE` means that the repository does not establish the claim. The distinction is particularly important for nonmonotonicity, because a single counterexample establishes failure of monotonicity for a relation, whereas a general update theorem requires quantified proof over carriers, profiles, and updates.

## 2. Related work and terminology

Default logic and circumscription made explicit that adding premises can withdraw earlier conclusions [@Reiter1980; @McCarthy1980]. Defeasible logics and legal argumentation provide rule and priority mechanisms for such revision [@AntoniouEtAl2001; @Maher2001; @PrakkenSartor1997; @Horty2011]. Dung semantics locates nonmonotonic behavior in the interaction of attacks and defenses [@Dung1995]. By contrast, a positive Horn immediate-consequence operator is monotone [@Horn1951], and its least-fixed-point semantics is governed by standard order theory [@Tarski1955].

The word “monotone” is incomplete without an order. The repository uses at least four: support-set inclusion, add-only system extension, extension-set inclusion, and non-upgrading assurance orders. A function can be monotone under one order while acceptance is nonmonotone under another update relation. The paper therefore avoids the broad sentence “the system is nonmonotonic.” It identifies each carrier and update.

## 3. Monotone finite Horn support

For (H=(U,F_0,R)), define

$$
T_H(S)=F_0\cup
\{head(r)\mid r\in R,\ premises(r)\subseteq S\}.
\tag{1}
$$

`FORMALIZED`: `HornDefinitions.TH_monotone` proves

$$
S\subseteq T\quad\Longrightarrow\quad T_H(S)\subseteq T_H(T).
\tag{2}
$$

This monotonicity is unsurprising but foundational. Once a rule’s premises are contained in (S), they remain contained in any larger (T). The operator contains no negative premise and no removal instruction.

Iteration is

$$
I_0=\varnothing,\qquad I_{n+1}=T_H(I_n).
\tag{3}
$$

`FORMALIZED`: `FiniteMonotoneSystem.iter_mono` proves

$$
I_n\subseteq I_{n+1}.
\tag{4}
$$

Since every iterate lies inside finite (U), strict growth cannot continue beyond (|U|). The source proves

$$
\exists k\le |U|:\ I_k=I_{k+1},
\qquad I_{|U|}=I_{|U|+1}.
\tag{5}
$$

The closure (C_H=I_{|U|}) satisfies

$$
T_H(C_H)=C_H,\qquad
T_H(S)=S\Longrightarrow C_H\subseteq S.
\tag{6}
$$

Equations (1)–(6) are `FORMALIZED` across `HornDefinitions.lean`, `FiniteMonotoneIteration.lean`, `HornFixedPoint.lean`, and `ULM07HornSupport.lean`. They establish support closure relative to a finite system. They do not establish that the rule set is complete or legally valid.

## 4. Add-only system updates

The repository formalizes a restricted update. A delta contains new facts and rules whose facts and rule heads stay within the existing universe:

$$
H+\Delta=(U,F_0\cup\Delta_F,R\cup\Delta_R).
\tag{7}
$$

`FORMALIZED`: for every (S),

$$
T_H(S)\subseteq T_{H+\Delta}(S).
\tag{8}
$$

By induction on the common iteration count,

$$
I_H^n\subseteq I_{H+\Delta}^n,
\tag{9}
$$

and at the fixed finite bound,

$$
C_H\subseteq C_{H+\Delta}.
\tag{10}
$$

These are `FORMALIZED` in `ULM15IncrementalEmpiricalBanach.lean`. The theorem is about additions. Retraction of a fact, deletion of a rule, change of the atom universe, or replacement of a rule head is not represented by `HornAddDelta`. General belief revision under deletion is `CONJECTURE`.

The independent child specification is full recomputation. An optimized implementation is correct when

$$
IncrementalCorrect(impl,H)\Longleftrightarrow
\forall\Delta,\ impl(\Delta)=FullRecompute(H+\Delta).
\tag{11}
$$

`FORMALIZED`: this refinement predicate and its direct consequence are in the same module. The definition does not prove that any particular worklist implementation satisfies it.

## 5. From support to arguments

A supported candidate requires request identity and support containment:

$$
CandidateWF(H,c)\Longleftrightarrow
c.request=H.request\land c.support\subseteq C_H.
\tag{12}
$$

`FORMALIZED`: generated candidates satisfy (12). A canonical argument then retains labelled support hyperedges and a well-founded dependency relation

$$
p\prec_a q\Longleftrightarrow
\exists e\in a.supportEdges,\ p\in e.premises\land e.conclusion=q.
\tag{13}
$$

`FORMALIZED`: `ArgumentWF` rules out dangling and cyclic concrete derivations, preserves request identity, and retains assumption dependencies. None of these conditions makes acceptance monotone. They determine what object is being evaluated.

Support and acceptance answer different questions. If \(q\in C_H\), the declared positive rules support \(q\). If every argument concluding \(q\) is defeated under the selected profile, \(q\) need not be accepted. `DERIVED`: a support fact can persist through an attack update while its acceptance disappears. The finite example below witnesses this claim.

## 6. Typed attacks and resolved defeat

A typed attack is well formed when

$$
AttackWF(\alpha)\Longleftrightarrow
\alpha.witness\neq ""\land
\alpha.attacker.request=\alpha.target.request.
\tag{14}
$$

Given validated attacks and policy $\pi$,

$$
D_\pi=\{(attacker_\alpha,target_\alpha)\mid
\alpha\in Attacks\land\pi(\alpha)=\top\}.
\tag{15}
$$

Both are `FORMALIZED` in `ULM09AttackDefeat.lean`. Every defeat in $D_\pi$ has a real well-formed source attack and request-bound endpoints. The theorem does not constrain how $\pi$ responds when attacks are added or evidence changes. Policy monotonicity, antitonicity, and revision consistency are `CONJECTURE`.

There are at least three distinct updates:

$$
\Delta_A: A\mapsto A\cup A^+,\qquad
\Delta_D: D\mapsto D\cup D^+,\qquad
\Delta_\pi:\pi\mapsto\pi'.
\tag{16}
$$

This taxonomy is `DERIVED`. The Lean structures expose the carriers but do not package (16) as an update algebra. Adding an argument without attacks, adding a defeat between existing arguments, and changing policy over fixed attacks can affect semantics differently.

## 7. Acceptance semantics

For (AF=(A,D)), defense is

$$
Defends_D(S,a)\Longleftrightarrow
\forall b\in A, (b,a)\in D\Rightarrow
\exists c\in S, (c,b)\in D.
\tag{17}
$$

The characteristic function is

$$
F_D(S)=\{a\in A\mid Defends_D(S,a)\}.
\tag{18}
$$

`FORMALIZED`: (F_D) is monotone in (S) for a fixed (AF). The grounded extension is

$$
G_D=F_D^{|A|}(\varnothing),\qquad F_D(G_D)=G_D.
\tag{19}
$$

This fixed-framework monotonicity must not be confused with monotonicity under changes to (D). The theorem says

$$
S\subseteq T\Rightarrow F_D(S)\subseteq F_D(T)
\tag{20}
$$

for one fixed defeat relation. It does not say

$$
D\subseteq D'\Rightarrow G_D\subseteq G_{D'}.
\tag{21}
$$

Claim (21) is false in general, as shown below. The repository does not contain it, and this paper labels its negation with a finite witness `DERIVED`, not `FORMALIZED`.

Complete, preferred, and stable predicates are also `FORMALIZED`:

$$
Complete_D(S)\Longleftrightarrow
Admissible_D(S)\land F_D(S)=S,
\tag{22}
$$

$$
Preferred_D(S)\Longleftrightarrow
Admissible_D(S)\land S\text{ is inclusion-maximal},
\tag{23}
$$

$$
Stable_D(S)\Longleftrightarrow
ConflictFree_D(S)\land
\forall a\in A\setminus S,\exists b\in S:(b,a)\in D.
\tag{24}
$$

The powerset reference enumerators are exact for the finite definitions. A general incremental maintenance theorem for these extension families is `CONJECTURE`.

## 8. Counterexample: adding a defeat removes acceptance

Let \(A=\{a,b\}\) and initially \(D_0=\varnothing\). Then both arguments have no attackers, so

$$
F_{D_0}(\varnothing)=\{a,b\},\qquad
G_{D_0}=\{a,b\}.
\tag{25}
$$

Add one defeat (D_1=\{(b,a)\}). Argument (b) remains unattacked, while (a) is attacked by (b) and the empty set does not defeat (b). Therefore

$$
F_{D_1}(\varnothing)=\{b\},\qquad
G_{D_1}=\{b\}.
\tag{26}
$$

Although \(D_0\subset D_1\),

$$
a\in G_{D_0}\quad\land\quad a\notin G_{D_1}.
\tag{27}
$$

Equations (25)–(27) are `DERIVED` by finite evaluation of the `FORMALIZED` characteristic function. They constitute a counterexample to grounded-acceptance monotonicity under defeat addition. They are not represented as a named Lean theorem in the repository.

Nothing in the example removes Horn support for (a). Suppose an argument concluding (a) was built from a fixed closure (C_H). The attack update changes (D), not (H). Thus

$$
a\in C_H\quad\text{before and after the update},
\qquad
a\in G_{D_0},\ a\notin G_{D_1}.
\tag{28}
$$

Equation (28) is `DERIVED` and captures the architecture’s central separation: derivability can remain monotone while dialectical acceptance is defeasible.

## 9. Counterexample: adding a defender restores acceptance

Begin with (A_1=\{a,b\}) and (D_1=\{(b,a)\}), so (G_{D_1}=\{b\}). Add a new argument (c) and defeat ((c,b)):

$$
A_2=\{a,b,c\},\qquad D_2=\{(b,a),(c,b)\}.
\tag{29}
$$

Now (c) is unattacked, so it enters the first grounded iteration. It defeats (b), thereby defending (a). Iteration yields

$$
F_{D_2}(\varnothing)=\{c\},\qquad
F_{D_2}(\{c\})=\{a,c\},\qquad
G_{D_2}=\{a,c\}.
\tag{30}
$$

This `DERIVED` example shows that a later addition can restore an argument previously rejected. Nonmonotonicity does not mean arbitrary instability; it means the acceptance relation is sensitive to the topology of attack and defense.

## 10. Profile-dependent revision

The selected family is

$$
Ext_p(AF)=
\begin{cases}
\{G\},&p=grounded,\\
PreferredExt(AF),&p=preferred,\\
StableExt(AF),&p=stable,\\
CompleteExt(AF),&p=complete.
\end{cases}
\tag{31}
$$

`FORMALIZED`: `ULM11BranchQuery.extensionsForProfile` defines (31). An update may alter the number and contents of extensions. The same query can remain possible while ceasing to be common, or stable extensions can disappear. A universal theorem describing all such transitions is `CONJECTURE`.

Scenario, assumptions, profile, and extension form a branch identity. Composition is permitted only for equal branches:

$$
Composable(x,y)\Longleftrightarrow x.branch=y.branch.
\tag{32}
$$

This is `FORMALIZED`. It prevents revision from being hidden by combining claims from pre-update and post-update branches or from incompatible extensions. If an update changes any component of the branch key, the result is a new branch rather than a silent mutation of the old legal outcome.

## 11. Query states under revision

Within extension family $\mathcal E$, skeptical and credulous acceptance are

$$
Common(q)\Longleftrightarrow
\forall E\in\mathcal E,Accepted(E,q),
\tag{33}
$$

$$
Possible(q)\Longleftrightarrow
\exists E\in\mathcal E,Accepted(E,q).
\tag{34}
$$

`FORMALIZED`: the repository separately defines universal and existential refutation. It also distinguishes

$$
UndecidedSome(q)\Longleftrightarrow
\exists E,\ Enterable(E,q)\land
\neg Accepted(E,q)\land\neg Refuted(E,q),
\tag{35}
$$

from

$$
InconsistentSome(q)\Longleftrightarrow
\exists E,\ Enterable(E,q)\land
Accepted(E,q)\land Refuted(E,q).
\tag{36}
$$

These definitions are `FORMALIZED`. Under revision a query may move among statuses, but transitions must be recomputed for the new branch. The current model does not define a lattice of query-status changes, so claims of monotone “improvement” are `CONJECTURE`.

## 12. Failure-preserving revision

Revision can fail or remain incomplete. The outcome algebra has three constructors, and mapping preserves failure:

$$
map(f,Failure(e))=Failure(e).
\tag{37}
$$

`FORMALIZED`: `ULM02Outcome.map_never_upgrades_failure`. A partial result carries nonempty open obligations. At the semantic layer, an incomplete evaluation likewise contains a nonempty obligation set and only sound discovered extensions. At adjudication,

$$
adjudicate(Incomplete(p))=SolverIncomplete(p.openObligations).
\tag{38}
$$

This is `FORMALIZED` in `ULM12Procedure.lean`. Revision cannot turn solver incompleteness into an adjudicated status merely because an authority object is also present.

Coverage composition accumulates deficits:

$$
open(C_1\sqcup C_2)=open(C_1)\cup open(C_2).
\tag{39}
$$

Trust composition is a meet:

$$
(\tau\wedge\sigma)_i=\min(\tau_i,\sigma_i),\qquad
\tau\wedge\sigma\preceq\tau,\sigma.
\tag{40}
$$

Both are `FORMALIZED` in `ULM14CoverageTrust.lean`. Adding evidence cannot average away an open obligation or raise a weak coordinate through compensation.

## 13. Retraction, temporal change, and what is not proved

The add-only Horn theorem does not cover retraction. The broader repository defines source-version applicability:

$$
Applicable(v,t)\Longleftrightarrow
v.from\le t\land(t\le v.to\text{ if present})\land v.status=active.
\tag{41}
$$

`FORMALIZED`: retracted and superseded versions are not applicable, and future observations relative to an as-of date are rejected. These theorems provide input guards, not a complete truth-maintenance algorithm. How invalidation of a source propagates through every Horn atom, argument, attack, extension, calculation, and certificate is `CONJECTURE` unless represented by a new request and recomputation.

A safe operational interpretation is `DERIVED`: treat a retraction or policy change as producing a new subject and branch, recompute the reference result, and retain both old and new provenance. This follows the identity architecture but is not a single named theorem. In-place mutation without subject change would defeat the branch and receipt bindings.

## 14. Revision operators must name their carrier

Many apparent disputes about monotonicity disappear once the update carrier is stated. The formal Horn theorem orders input support sets by inclusion while holding (H) fixed. The add-only theorem orders systems by inclusion of initial facts and rules while holding the universe and iteration bound fixed. The Dung characteristic theorem orders candidate defense sets while holding both arguments and defeats fixed. A legal-revision claim often changes all three at once.

Suppose a new source adds an initial fact. If no attacks or policies change, Horn closure can only grow under the formal delta contract. New support may yield new arguments, increasing (A). Whether previous arguments remain accepted depends on attacks incident to the new arguments. Thus monotonic support growth does not determine acceptance growth. `DERIVED`: a pipeline update can be monotone at its first stage and nonmonotone at a later stage without contradiction.

Suppose instead that a source is retracted. This is not an add-only Horn delta. A safe model must construct a new subject, remove or invalidate dependent admitted premises, recompute support, rebuild affected arguments, resolve attacks again, and evaluate new extensions. The current repository supplies components for source applicability, assumption dependencies, and request identity but no single end-to-end retraction theorem. Therefore any claim that retraction is incrementally sound is `CONJECTURE`.

A policy update differs again. The set of typed attacks can remain fixed while $\pi$ changes which attacks succeed. In that case the Horn system, canonical argument set, and attack witnesses are unchanged, but $D_\pi$ changes. `FORMALIZED`: each new resolved defeat still requires a source attack under the new policy. `CONJECTURE`: policy changes preserve any previous semantic status. The finite counterexamples show why no such blanket preservation should be expected.

An as-of update may make a source newly effective without changing its text. `FORMALIZED`: source applicability depends on an effective interval and active status. `DERIVED`: moving the as-of date can change the admissible input set and therefore should change the request or scenario identity. The repository does not prove a temporal monotonicity theorem because active status can later become superseded or retracted.

These cases motivate an explicit update signature:

$$
u=(\Delta_{source},\Delta_H,\Delta_A,\Delta_{attack},
\Delta_\pi,\Delta_{profile},\Delta_{authority}).
\tag{42}
$$

Equation (42) is `CONJECTURE` as a future unified carrier. The present structures expose most components separately but do not define this tuple. A revision theorem should quantify over a named subset of components rather than use an unqualified phrase such as “adding information.”

## 15. Reproducible revision traces

A defensible revision trace needs both old and new subjects. Let (R_0) and (R_1) be request or branch identifiers before and after update. A minimal comparison record would contain

$$
Trace=(R_0,R_1,u,Outcome_0,Outcome_1,Open_0,Open_1).
\tag{43}
$$

This carrier is `CONJECTURE`; it is not defined in the ULM package. It is nevertheless consistent with the `FORMALIZED` principle that requests, branches, and open obligations remain explicit. Recording only the changed conclusion would be insufficient because a profile switch, policy update, or new assumption can change the meaning of the result without changing its surface text.

For an add-only Horn update, a trace can include the formal inclusion witness \(C_H\subseteq C_{H+\Delta}\). For an argumentation update, a trace should not presume inclusion between extensions. It should instead record the old and new framework, selected profile, and exact extension families. `DERIVED`: exact powerset reference evaluation can serve as an oracle for small fixtures. Production algorithms require a refinement receipt or theorem to claim equality with that oracle.

Revision also affects queries. The pair ((Common(q),Possible(q))) permits three informative combinations for a nonempty family: common and possible; not common but possible; neither. Refutation and gate state add further dimensions. Reducing this vector to a single Boolean loses whether a claim is disputed, merely absent, excluded, or uncomputed.

A comparison vector may be written

$$
Q_R(q)=(Common_R(q),Possible_R(q),CommonRefuted_R(q),
PossiblyRefuted_R(q),Excluded_R(q)).
\tag{44}
$$

Equation (44) is `DERIVED` from `FORMALIZED` predicates. It is not a probability vector and its coordinates are not mutually exclusive in all cases. In particular, an inconsistent branch can accept and refute a query simultaneously.

## 16. Nonmonotonicity and assurance are different

An acceptance reversal is not automatically an assurance failure. If a new valid attack changes a grounded extension, the change may be the correct result of nonmonotonic semantics. Assurance instead asks whether inputs, implementation, run, coverage, legal authority, and notices satisfy their respective contracts. The same revised result may be semantically exact but legally under-authorized, or legally reviewed but produced by an incomplete solver.

The five-coordinate trust meet avoids a second confusion. If a new component has lower source trust but higher proof trust, the composition retains the lower coordinate in each dimension rather than computing an average. `FORMALIZED`: meet cannot exceed either operand. `DERIVED`: revision cannot claim an overall trust upgrade merely because one dimension improved while another declined. There is no total trust score in the ULM package.

Coverage behaves similarly. If the old result has open obligations \(O_0\) and the new component has \(O_1\), composition yields \(O_0\cup O_1\). It does not subtract an obligation merely because additional evidence arrived. Discharge would require evidence satisfying the exact subject and obligation through a sound verifier. `FORMALIZED`: required obligations are nonempty and `sat_sound` proves a goal only from verifier soundness plus exact accepted evidence.

Thus a revision system needs two separate judgments:

$$
SemanticChange(R_0,R_1)\qquad\text{and}\qquad
AssuranceStatus(R_1).
\tag{45}
$$

The separation in (45) is `DERIVED`. A future end-to-end revision calculus is `CONJECTURE`. The current repository provides the component types but not a theorem that every semantic change is accompanied by a complete assurance recomputation.

## 17. Legal interpretation of defeasibility

The formal counterexamples establish only structural defeasibility. They do not prove a jurisprudential theory that all legal conclusions are defeasible, nor that a particular legal decision must be revised when a new attack appears. Courts may apply finality, waiver, preclusion, burdens, procedural deadlines, or institutional authority rules. Those doctrines are not encoded by a generic defeat edge.

The procedure module helps preserve this boundary. A procedural disposition travels through a distinct channel and can precede an entity-level finding. A computational extension does not manufacture a legal status. `FORMALIZED`: procedure-state transitions preserve the normative marker and burden outcomes require validated authority. `CONJECTURE`: a specified legal doctrine permits or requires reopening under an update.

The distinction also applies to sources. A future observation is blocked relative to an as-of date, and retracted or superseded records are inapplicable. These `FORMALIZED` guards prevent temporal leakage in the formal input. They do not determine the doctrine of retroactivity or the evidentiary effect of a later correction. Those require human legal judgment and source-specific rules.

## 18. Testing implications

Finite counterexamples provide high-value regression fixtures. An implementation of grounded semantics should reproduce equations (25)–(27) and (29)–(30). Mutation tests can remove a defeat, reverse it, or skip the second characteristic iteration; a valid test suite should detect the changed extension. Such tests are engineering evidence. They do not change the proof label of the paper examples unless the fixtures themselves are connected to Lean through a verified refinement.

Property-based tests can also check the `FORMALIZED` Horn laws on bounded generated systems: (T_H) remains inside (U), support iteration grows monotonically, and add-only extension contains the old iteration at every common step. These tests may reveal implementation bugs but are not substitutes for the Lean theorem.

Negative tests are especially important. A solver that times out must not return `noExtension`; a partial family must disclose open obligations; a post-update branch must not reuse the pre-update branch key; and a failed runtime receipt must not be interpreted as semantic rejection. These behaviors follow the formal constructors and should be mirrored by external interfaces.

## 19. Evidence ledger

| Claim | Status | Source | Boundary |
|---|---|---|---|
| (T_H) is monotone in support inclusion | `FORMALIZED` | `HornDefinitions.TH_monotone` | Positive Horn rules only |
| Finite iteration stabilizes by carrier size | `FORMALIZED` | `FiniteMonotoneIteration.fixed_at_card` | Declared finite universe |
| Add-only deltas cannot shrink Horn closure | `FORMALIZED` | `ULM15.horn_closure_subset_extend` | No deletion or universe change |
| Characteristic function is monotone in (S) for fixed AF | `FORMALIZED` | `ULM10.defeatSystem.step_monotone` | Defeat graph fixed |
| Defeat addition can remove grounded acceptance | `DERIVED` | equations (25)–(27) | Finite counterexample, not Lean theorem |
| Adding a defender can restore acceptance | `DERIVED` | equations (29)–(30) | Finite counterexample |
| All profile updates obey one revision law | `CONJECTURE` | none | Profiles react differently |
| Different branches cannot be merged | `FORMALIZED` | `different_branches_not_composable` | Does not select correct branch |
| Incomplete evaluation remains incomplete at adjudication | `FORMALIZED` | `adjudicate_incomplete` | Runtime must refine formal input |
| Retraction propagates through every layer | `CONJECTURE` | none | Requires dependency-aware recomputation theorem |

## 20. Validation boundary and limitations

The formalized Horn results are exact but narrow. They concern positive finite rules. Negation-as-failure, exceptions, priorities, and retractions are not encoded inside (T_H). The Dung layer represents resolved conflict but receives its defeat relation from an external policy. Therefore the repository proves how a fixed graph is evaluated, not that the graph captures every legally operative defeat.

The nonmonotonicity counterexamples in this paper are `DERIVED`, not Lean-certified artifacts. They are elementary finite evaluations of the formal definitions, but the distinction is recorded honestly. A future Lean module could define framework embeddings and prove profile-specific counterexamples or update conditions. Until then, no statement about arbitrary update sequences is `FORMALIZED`.

The system also lacks a general deletion refinement. Add-only incremental correctness is defined as equality with child full recomputation. A production truth-maintenance system would need dependency tracking, invalidation, recomputation, and receipt renewal. Performance claims, confluence of concurrent updates, and serializability are `CONJECTURE`.

Finally, acceptance is not legal judgment. A semantic change may be relevant to a decision, but a request-bound authority and burden finding remain necessary in the procedure layer. The model does not formalize when a court may reopen a judgment, apply retroactivity, or treat a later source as controlling.

## 21. Threats to validity and falsifiability

The central empirical-looking statements in this paper are actually structural. Equations (25)–(30) are finite calculations, not observations about courts. They can be falsified by applying the stated characteristic function; if the computed sets differ, the derivation is wrong. They cannot be confirmed or refuted by counting judicial outcomes because no mapping from those outcomes to (a,b,c) is asserted.

The `FORMALIZED` Horn results are vulnerable to a different misunderstanding: one may silently introduce negative premises, defaults, priorities, or deletion into (T_H) while retaining the theorem’s name. That would change the operator and invalidate the proof transfer. Any runtime comparison must demonstrate that its operator matches the positive finite definition or prove a new refinement.

The nonmonotonic Dung examples also hold the policy-resolved defeat graph fixed during each evaluation. If a runtime recomputes policy during iteration, its transition system differs. Similarly, preferred and stable algorithms that terminate early may return a sound partial family but may not claim exact equality with the reference family. The result algebra provides an incomplete constructor for precisely this case.

The legal interpretation is the largest external-validity threat. A new document need not be a permissible new premise; a purported attack need not be legally cognizable; an authority may lack competence; and finality rules may prevent institutional revision even when a model’s extension changes. The paper treats each as an external legal input. It does not infer doctrine from topology.

The proposed update and trace carriers in equations (42)–(44) are explicitly `CONJECTURE`. They are falsifiable as designs: a future implementation may reveal missing identity fields, update dimensions, or obligations. Their presence does not alter the current Lean proof inventory.

Finally, assurance is subject-bound. Evidence from one commit, request, profile, fixture, or external runtime cannot be reused merely because code or prose looks similar. A valid comparison must record the exact old and new subjects. This constraint may make evaluation more laborious, but without it revision evidence cannot show which result was checked.

## 22. Practical reporting protocol

A revision report based on this model should state, in order, the old subject, update class, new subject, Horn-support difference, argument and attack difference, policy identity, old and new extension families, query-status vector, open obligations, authority status, and runtime evidence. Omitting unchanged fields is acceptable only when their equality is evidenced. The report should never replace `solverIncomplete` by “rejected,” or replace “not common” by “false.”

For add-only Horn changes, the report may cite closure inclusion as `FORMALIZED`. For defeat additions, it should give an exact old/new comparison rather than claim monotonicity. For retractions or policy changes, it should state that the add-only theorem is inapplicable. For legal conclusions, it should identify the human or institutional authority responsible for interpreting the changed computation.

This protocol is `DERIVED` from the formal identity and assurance structures. It is not itself a Lean theorem. Its value is operational: it converts abstract proof boundaries into a reproducible account of why a result changed and what remains unresolved.

## 23. Reproducibility protocol

To reproduce a revision claim, begin by naming the ordered carrier. For Horn support-set monotonicity, hold the system fixed and compare \(S\subseteq T\). For add-only system monotonicity, hold the universe fixed and show that initial facts and rules were combined by union. A deletion, changed rule head, or new universe is outside that theorem and must not inherit its label.

For dialectical revision, record the complete old and new argument and defeat carriers. Recompute the characteristic function from the empty set for grounded semantics. For preferred, complete, or stable semantics, compare exact reference families rather than one selected extension. State whether a changed result arose from a new argument, a new typed attack, a changed policy decision, or a profile change. These are different update dimensions.

The two finite counterexamples in this paper can be checked by hand: an unattacked pair has grounded extension \(\{a,b\}\); adding \(b\to a\) removes \(a\); adding an unattacked defender \(c\to b\) restores \(a\). Their status remains `DERIVED` until encoded as named Lean theorems. A test of a runtime implementation is additional engineering evidence, not a promotion of the proof label.

At the reporting boundary, preserve the old and new request or branch identifiers, exact query quantifiers, open obligations, and authority status. A missing result is not a negative result, a non-common claim is not false, and a semantic reversal is not automatically a legal reversal. This protocol makes revision traces independently inspectable without claiming a general nonmonotonic-update theorem that the repository does not contain.

## 24. Conclusion

The repository supports a precise layered thesis. Horn support is monotone under support inclusion and add-only extension. Dialectical acceptance can be nonmonotone under changes to attacks, defeats, arguments, or policy. Fail-closed results, branch identities, open-obligation unions, and trust meets prevent that revision from being narrated as uninterrupted certainty. The current Lean package proves the monotone core and the finite semantics for each fixed framework. General revision laws and legal consequences remain `CONJECTURE`. This separation makes nonmonotonic legal reasoning analyzable without making it mysterious or overclaiming what has been verified.

## Declarations

**Funding.** No external funding was received.

**Conflict of Interest.** The author declares no competing interests.

**Data Availability.** Formal definitions, finite specifications, and source files are available in the `legal-math-modeling` repository [@LegalMathModeling2026]. No private case data are used.

**Ethics.** No human participants or private legal records were used. The examples are abstract and do not constitute legal advice.

**CRediT Author Statement.** Laupinco: Conceptualization, Methodology, Software, Formal Analysis, Investigation, Writing—Original Draft, Writing—Review and Editing.

**AI Disclosure.** AI assistance was used for drafting and consistency checking. The author reviewed all formulas, labels, source anchors, and conclusions and remains responsible for the manuscript.

## References

References are maintained in `paper/references.bib` [@LegalMathModeling2026; @Dung1995; @PrakkenSartor1997; @Horty2011; @Reiter1980; @McCarthy1980; @AntoniouEtAl2001; @Maher2001; @Horn1951; @Tarski1955; @DeMouraUllrich2021].
