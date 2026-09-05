# Graph Similarity Is Not Yet a Topology: Counterexamples, Metrics, and Formal Boundaries

**Author:** Laupinco

## Abstract

This paper gives a negative and constructive account of graph similarity in the `legal-math-modeling` repository. Earlier graph-similarity axioms were removed after counterexamples showed that the implemented score could fail strict reflexivity and identity-style discrimination. The current Lean core does not define a graph metric, graph kernel, or topology induced by graph similarity. It does define finite structural legal arguments, request-bound defeat graphs, and a weighted sup distance on finite real vectors; it proves nonnegativity, symmetry, triangle inequality, and point separation for the latter under positive weights. It also proves a coordinate-Lipschitz contraction inequality and generic Banach results under explicit complete-space and contraction hypotheses. Those vector results cannot be transferred to graphs without a defined representation map and proof that it preserves or reflects the intended graph identity. We classify current Lean results as `FORMALIZED`, paper-level counterexamples and conditional constructions as `DERIVED`, and proposed graph embeddings, metrics, kernels, or topologies as `CONJECTURE`. We show why a bounded similarity score is not automatically a metric, why self-similarity and separation must be tested independently, why two distinct graphs can receive maximal similarity, and why quotienting by a feature map changes the identity being modeled. The paper offers a safe path forward: retain structural equality for canonical arguments, call the legacy score a non-metric similarity, and formalize any new graph geometry only after its carrier, invariances, quotient relation, and proofs are explicit.

## 中文摘要

本文对 `legal-math-modeling` 的图相似度问题给出否定性与建设性结论。早期图相似度公理已因反例被删除：既有分数可能违反严格自反性，也可能把不同图赋为最大相似度。当前 Lean 核心没有定义图度量、图核或由图相似度诱导的拓扑；它形式化的是有限结构论证、请求绑定的击败图，以及有限实向量上的加权 sup 距离。后者已证明非负、对称、三角不等式和点分离，但不能在没有图到向量表示映射及其身份保持证明时直接移植到图。本文把当前 Lean 结果标为 `FORMALIZED`，把纸面反例和条件构造标为 `DERIVED`，把图嵌入、图度量、核与拓扑标为 `CONJECTURE`。

**Keywords:** graph similarity; graph metric; topology; counterexample; canonical arguments; weighted sup distance; formal verification

## 1. Research questions and claim labels

The paper asks whether the repository currently has a graph metric, which metric axioms the legacy score satisfies or violates, what a similarity range proof establishes, whether the weighted vector distance can repair the graph score, and what formal work is required before using similarity as identity evidence.

`FORMALIZED` is reserved for current Lean definitions and theorems. `DERIVED` covers mathematical consequences, conditional constructions, and counterexamples documented outside a Lean theorem. `CONJECTURE` marks a proposed graph representation, quotient, kernel, or topological result. A deleted axiom is not a theorem, and a Python or SMT check is not relabelled as Lean proof.

## 2. Related work

Graph comparison can mean exact isomorphism, edit distance, feature similarity, kernel evaluation, or task-specific ranking. These notions have different invariances and separation properties. In legal argumentation, graph structure matters because support and attack direction affect conclusions [@Dung1995; @PrakkenSartor1997]. Case-based reasoning can use similarity without claiming metric geometry [@RisslandAshley1987]. Formal verification requires the carrier and equality relation to be explicit [@Hoare1969; @DeMouraUllrich2021].

The repository’s canonical argument identity follows the full finite labelled support hypergraph. That design avoids using a similarity score as equality. The present paper retains that choice and treats approximate graph comparison as an optional analytical layer.

## 3. Similarity, distance, metric, and kernel

A similarity is merely a function

$$
s:\mathcal G\times\mathcal G\to[0,1].
\tag{1}
$$

Equation (1) is `CONJECTURE` as a general carrier for the graph score; no current Lean graph-similarity definition exists. Boundedness alone states

$$
0\le s(G,H)\le1.
\tag{2}
$$

An engineering artifact in the repository checks a range property for an earlier score, but equation (2) is not a Lean theorem in the ULM package. Even if (2) holds, it establishes neither self-similarity nor discrimination.

A distance is a metric when

$$
d(G,H)\ge0,
\tag{3}
$$

$$
d(G,H)=0\Longleftrightarrow G=H,
\tag{4}
$$

$$
d(G,H)=d(H,G),
\tag{5}
$$

$$
d(G,K)\le d(G,H)+d(H,K).
\tag{6}
$$

Equations (3)–(6) are standard definitions, included as mathematical background rather than repository theorems. If one sets (d=1-s), then a metric would require

$$
s(G,G)=1,\qquad
s(G,H)=1\Longrightarrow G=H,
\tag{7}
$$

plus symmetry and a transformed triangle inequality. These conditions do not follow from the range (2).

A positive-semidefinite kernel would require, for every finite sequence \(G_1,\ldots,G_n\) and real coefficients \(c_i\),

$$
\sum_{i=1}^{n}\sum_{j=1}^{n}c_ic_jk(G_i,G_j)\ge0.
\tag{8}
$$

Equation (8) is a background definition. The repository has no current Lean proof that the graph score is a kernel.

## 4. Preserved counterexamples

`JC_Formalization.lean` explicitly records that `GraphSimilarityAxioms` was deleted because of counterexamples CE-001 and CE-002. This source comment is evidence of demotion, not a positive theorem. The first reported pattern is self-similarity failure:

$$
\exists G:\ s(G,G)=0.4\neq1.
\tag{9}
$$

Equation (9) is `DERIVED/COUNTEREXAMPLE`, not `FORMALIZED`. It refutes the universal axiom $\forall G, s(G,G)=1$ for that score and input convention. The likely mechanism described in repository audit artifacts is an empty or conservative feature component, but this paper does not infer a universal cause from one witness.

The second pattern is failure of identity discrimination:

$$
\exists G\neq H:\ s(G,H)=1.
\tag{10}
$$

Equation (10) is also `DERIVED/COUNTEREXAMPLE`. Repository artifacts describe structurally different examples receiving maximal similarity. A score satisfying (10) cannot be used as an equality proxy under the carrier’s structural equality.

If (d_s(G,H)=1-s(G,H)), then (9) gives

$$
d_s(G,G)=0.6\neq0,
\tag{11}
$$

and (10) gives

$$
G\neq H\land d_s(G,H)=0.
\tag{12}
$$

Thus both reflexivity of zero distance and point separation fail. Equations (11)–(12) are `DERIVED`. No triangle-inequality analysis can repair these failures without redefining the score or carrier.

## 5. Why a range proof is insufficient

Suppose a program verifies (2) for all inputs in a bounded symbolic domain. It shows that the output respects a declared interval. It does not show that graph identity is recognized. The constant function

$$
s_0(G,H)=\tfrac12
\tag{13}
$$

satisfies (2) and symmetry but carries no discrimination. Likewise,

$$
s_1(G,H)=1
\tag{14}
$$

satisfies range, symmetry, and self-similarity but violates identity discrimination for every distinct pair. Equations (13)–(14) are `DERIVED` countermodels.

Range verification also does not prove positive semidefiniteness (8), monotonic relation to edit operations, stability under relabelling, or usefulness for a downstream task. Each property needs a separate statement and proof or empirical validation. The formal obligation registry reflects this general principle by requiring an observation declaration for a `ranker`; the tag does not supply the observation.

## 6. Structural equality in the current formal model

A canonical legal argument is the structure

$$
a=(request_a,conclusion_a,B_a,E_a),
\tag{15}
$$

where (B_a) is the base-premise set and (E_a) the labelled support-hyperedge set. `FORMALIZED`: `ULM08ArgumentConstruction.CanonicalArgument` uses structural equality derived from these fields. Finsets disregard duplicate storage and traversal order, while rule labels, conclusions, premise sets, dependencies, and request identity remain part of the object.

Direct support is

$$
p\prec_a q\Longleftrightarrow
\exists e\in E_a, p\in e.premises\land e.conclusion=q.
\tag{16}
$$

`FORMALIZED`: `ArgumentWF` requires well-foundedness, availability, request binding, nonempty premises, and reachability. Equality of argument structures is therefore not approximated by (s). An implementation may compute similarity for discovery, but it cannot replace the equality used by coverage, branch identity, or theorem statements without proving a new refinement.

The resolved Dung framework is

$$
AF=(request,A,D),\qquad D\subseteq A\times A.
\tag{17}
$$

`FORMALIZED`: `DefeatAF.WellFormed` requires every argument and endpoint to belong to the request-bound finite carrier. The semantics depends on directed defeat topology, so a similarity that ignores direction or labels may identify frameworks with different extensions.

## 7. A semantic collision example

Consider two two-node frameworks. Let

$$
AF_0=(\{a,b\},\varnothing),
\qquad AF_1=(\{a,b\},\{(a,b)\}).
\tag{18}
$$

Under grounded semantics,

$$
G(AF_0)=\{a,b\},\qquad G(AF_1)=\{a\}.
\tag{19}
$$

Equations (18)–(19) are `DERIVED` from the `FORMALIZED` characteristic function. Any graph feature that counts only nodes assigns equal node-count features to both frameworks while their legal-query outputs may differ. Therefore

$$
\phi_{nodes}(AF_0)=\phi_{nodes}(AF_1)
\centernot\Rightarrow
G(AF_0)=G(AF_1).
\tag{20}
$$

Equation (20) is a `DERIVED` counterexample. It shows that feature equality must be evaluated against a declared observation. If the observation is grounded acceptance, node count is not sufficient.

## 8. The formal weighted vector distance

The repository does contain a genuine distance-like construction on finite real vectors. For \(x,y:\mathrm{Fin}(n)\to\mathbb R\) and positive weights \(w_i>0\),

$$
d_w(x,y)=\max_i\frac{|x_i-y_i|}{w_i}.
\tag{21}
$$

`FORMALIZED`: `WeightedSupNorm.lean` proves

$$
d_w(x,y)\ge0,
\tag{22}
$$

$$
d_w(x,y)=d_w(y,x),
\tag{23}
$$

$$
d_w(x,z)\le d_w(x,y)+d_w(y,z),
\tag{24}
$$

$$
d_w(x,y)=0\Longleftrightarrow x=y.
\tag{25}
$$

These are substantive `FORMALIZED` results, but their carrier is a fixed-dimensional real vector space. The theorem named `weightedSupDist_complete` proves nonnegativity and point separation, not a complete-space instance. This paper does not interpret the name as topological completeness.

## 9. Why the vector theorem does not automatically apply to graphs

To compare graphs through (21), one must define a feature map

$$
\phi:\mathcal G\to\mathbb R^n
\tag{26}
$$

and induced pseudodistance

$$
d_\phi(G,H)=d_w(\phi(G),\phi(H)).
\tag{27}
$$

Equations (26)–(27) are `CONJECTURE`; no such Lean graph embedding is connected to ULM arguments. From the vector theorem, `DERIVED` conditionally:

$$
d_\phi(G,H)\ge0,\quad
d_\phi(G,H)=d_\phi(H,G),\quad
d_\phi(G,K)\le d_\phi(G,H)+d_\phi(H,K).
\tag{28}
$$

Point separation requires injectivity relative to the chosen graph equality:

$$
\phi(G)=\phi(H)\Longrightarrow G=H.
\tag{29}
$$

Without (29), (d_phi) is only a pseudometric. For finite feature vectors, graph collisions are common. Calling (27) a metric while omitting the quotient or injectivity proof would repeat the earlier overclaim.

## 10. Quotienting changes the identity

One can define an equivalence relation

$$
G\sim_\phi H\Longleftrightarrow\phi(G)=\phi(H).
\tag{30}
$$

Then (27) separates equivalence classes:

$$
d_\phi([G],[H])=0\Longleftrightarrow [G]=[H].
\tag{31}
$$

Equations (30)–(31) are `DERIVED` conditional mathematics, not repository theorems. They give a legitimate metric on a quotient if the construction is well defined. But the quotient identity means “same features,” not “same legal argument” or “same defeat semantics.” A system must name that loss of information.

If the intended observation is semantic, a coarser equivalence might be

$$
G\sim_p H\Longleftrightarrow Ext_p(G)=Ext_p(H).
\tag{32}
$$

Equation (32) is `CONJECTURE`. It is profile-dependent and may still identify structurally different graphs. It could be useful for caching semantic results, but it cannot replace structural identity in proof provenance.

## 11. Topology requires a valid distance or direct axioms

A metric (d) induces open balls

$$
B_d(G,r)=\{H\mid d(G,H)<r\},\qquad r>0,
\tag{33}
$$

and topology

$$
\mathcal T_d=
\{O\subseteq\mathcal G\mid
\forall G\in O,\exists r>0:B_d(G,r)\subseteq O\}.
\tag{34}
$$

These are background definitions. Since no graph metric is currently formalized, no graph topology induced by it is `FORMALIZED`. The legacy score cannot safely induce a metric topology through (1-s) because equations (11)–(12) violate metric axioms.

One could define a topology directly through a family of sets satisfying the empty/full, arbitrary-union, and finite-intersection axioms. That too is `CONJECTURE` for this repository. The word “topology” should therefore not appear as an achieved result in a release claim.

## 12. Contraction does not repair representation loss

The coordinate-Lipschitz theorem assumes

$$
|T(x)_i-T(y)_i|\le\sum_jL_{ij}|x_j-y_j|,\qquad
\sum_jL_{ij}w_j\le qw_i,
\tag{35}
$$

and proves

$$
d_w(Tx,Ty)\le qd_w(x,y).
\tag{36}
$$

This is `FORMALIZED` in `ContractionCondition.lean`. Generic Banach results prove convergence under complete-space and contraction hypotheses [@Banach1922]. None establishes that a graph updater preserves information through (phi). If (phi(G)=phi(H)) for semantically distinct graphs, a contracting vector iteration keeps them indistinguishable. Stability of the wrong abstraction is not correctness.

Thus the proposed implication

$$
T\text{ contracts features}\Longrightarrow
T\text{ preserves legal graph semantics}
\tag{37}
$$

is `CONJECTURE` and generally invalid without an observation-preservation theorem.

## 13. A safe graph-comparison specification

A future graph comparison should state its carrier, equality, invariances, observation, and proof target. Let \(Obs:\mathcal G\to\Omega\). An abstraction is observation-preserving when

$$
Obs'(\phi(G))=Obs(G).
\tag{38}
$$

This mirrors the `FORMALIZED` generic `Preserves` predicate in `ULM01NormalForm.lean`; applying it to an actual graph map is `CONJECTURE` until (phi) and observations are defined.

A safe output type would separate exact and approximate results:

$$
Compare(G,H)=
(StructuralEqual(G,H),\ Similarity_v(G,H),\ v,\ scope).
\tag{39}
$$

Equation (39) is `CONJECTURE`. The version and scope prevent a score from being reused across changed definitions. `StructuralEqual` remains the equality used by formal coverage; `Similarity` is an analytical annotation.

For ranking, one may require only boundedness and declared observation stability:

$$
0\le s_v(G,H)\le1,\qquad
G\cong H\Rightarrow s_v(G,K)=s_v(H,K),
\tag{40}
$$

where (cong) is a precisely defined relabelling equivalence. This proposal is `CONJECTURE`. It does not call the score a metric.

## 14. A taxonomy of metric failures

The preserved counterexamples show two failures, but a complete evaluation should distinguish at least six. The first is diagonal failure, \(s(G,G)\neq1\). It can arise when an empty-feature convention contributes a penalty even though both inputs are identical. A patch that special-cases object identity may restore the diagonal without improving comparisons between distinct but isomorphic graphs.

The second is separation failure, \(G\neq H\) yet \(s(G,H)=1\). It reveals that the selected features do not distinguish structural identity. Adding more features may reduce observed collisions, but absence of collisions in a finite test set is not an injectivity theorem.

The third is symmetry failure:

$$
\exists G,H:\ s(G,H)\neq s(H,G).
\tag{41}
$$

Equation (41) is `CONJECTURE` as a possible failure mode; it is not asserted about the preserved score without a witness. An asymmetric score may be appropriate for containment or retrieval but cannot be renamed a symmetric metric.

The fourth is triangle failure for (d_s=1-s):

$$
\exists G,H,K:\ d_s(G,K)>d_s(G,H)+d_s(H,K).
\tag{42}
$$

Equation (42) is likewise a test target, not a current repository result. Triangle inequality matters if the system uses metric indexing, nearest-neighbor pruning, or geometric convergence arguments.

The fifth is invariance failure. A graph relabelling that preserves the intended structure may change the score:

$$
G\cong H\quad\text{but}\quad s(G,K)\neq s(H,K).
\tag{43}
$$

Equation (43) is a `CONJECTURE` test property until the isomorphism relation and score are formalized. If identifiers are legally meaningful, full relabelling invariance may itself be undesirable. The intended invariance group must therefore be declared rather than assumed.

The sixth is semantic failure. Two graphs receive a high score but yield different extension or query results under the profile being predicted. A threshold formulation is

$$
s(G,H)\ge\theta\quad\land\quad Obs_p(G)\neq Obs_p(H).
\tag{44}
$$

Equation (44) is a `CONJECTURE` evaluation criterion. Unlike a pure metric axiom, it is task-relative. A structurally coarse score can be useful for retrieval even when it fails semantic preservation, provided the system labels the result as a candidate and verifies the retrieved graph separately.

This taxonomy prevents a common repair error: addressing one counterexample and declaring the whole score a metric. Each property has its own quantifiers, carrier, and evidence requirement.

## 15. Embedding prerequisites

An embedding must state exactly what becomes a coordinate. For a canonical argument, possible features include counts of base premises, support edges by rule kind, dependency labels, depth, branching, conclusion type, and request metadata. For a Dung framework, features may include argument count, defeat count, degree statistics, cycles, or profile-specific extension counts. Merely listing features does not show that they preserve structural identity or legal observation.

Let the proposed representation be

$$
\phi_v(G)=(f_{1,v}(G),\ldots,f_{n,v}(G)),
\tag{45}
$$

where (v) versions the feature schema. Equation (45) is `CONJECTURE`. Versioning matters because adding or redefining one feature changes every distance. Comparisons across (v) are invalid unless a migration relation is proved.

To use the weighted distance, every weight must be positive:

$$
\forall i,\ w_i>0.
\tag{46}
$$

Equation (46) is a `FORMALIZED` premise of `PositiveWeights` for the vector theorem. Zero cannot be used to “ignore” a coordinate without changing the carrier, because division by (w_i) is built into the definition. Removing a feature should produce a new representation version.

An exact structural metric needs injectivity:

$$
\phi_v(G)=\phi_v(H)\Longrightarrow G=H.
\tag{47}
$$

Equation (47) remains `CONJECTURE`. A finite vector of aggregate counts will generally fail it. An injective serialization into a vector might exist for a bounded finite carrier, but then the distance may encode identifiers rather than meaningful similarity. Injectivity and usefulness are different objectives.

If only observation preservation is needed, the weaker condition is

$$
\phi_v(G)=\phi_v(H)\Longrightarrow Obs_p(G)=Obs_p(H).
\tag{48}
$$

Equation (48) is `CONJECTURE`. It must name (p), because grounded and preferred observations can differ. It must also name the query or full extension-family observation. Preserving one query status does not preserve all semantics.

For approximate stability one might require

$$
d_w(\phi_v(G),\phi_v(H))<\eta
\Longrightarrow \rho(Obs_p(G),Obs_p(H))<\gamma.
\tag{49}
$$

Equation (49) is `CONJECTURE`; it introduces an output distance (ho), thresholds, and a robustness claim. The current repository proves none of them. For discrete extension families, small input distance can still cross a semantic boundary, so continuity cannot be assumed.

## 16. Why topology does not transfer automatically

Assume the vector carrier $X=\mathbb R^n$ has topology $\mathcal T_X$ induced by $d_w$. A feature map induces the initial topology

$$
\mathcal T_\phi=
\{\phi^{-1}(O)\mid O\in\mathcal T_X\}
\text{ closed under topology generation}.
\tag{50}
$$

Equation (50) is standard conditional mathematics and `DERIVED`, not a repository theorem. It defines openness only with respect to distinctions visible through $\phi$. If $\phi(G)=\phi(H)$, every open set in $\mathcal T_\phi$ contains either both or neither. The topology cannot separate them.

In separation terminology, a necessary condition for a (T_0) topology on the original graph identity is

$$
G\neq H\Longrightarrow
\exists O\in\mathcal T_\phi:
\mathbf 1[G\in O]\neq\mathbf 1[H\in O].
\tag{51}
$$

Equation (51) is background topology. Feature collisions violate it. Therefore the initial topology is naturally a topology on observable equivalence classes, not automatically on structural legal arguments.

A continuous vector updater (T_X) also does not induce a graph updater unless the diagram is specified:

$$
\phi\circ T_G=T_X\circ\phi.
\tag{52}
$$

Equation (52) is `CONJECTURE`. Without a graph map (T_G) and commutation proof, contraction of (T_X) says nothing about graph evolution. Even with commutation, a noninjective (phi) may hide divergent structural updates.

Homeomorphism would require far more:

$$
\phi\text{ bijective},\qquad
\phi\text{ continuous},\qquad
\phi^{-1}\text{ continuous}.
\tag{53}
$$

Equation (53) is `CONJECTURE` and implausible for a simple aggregate feature map. An embedding in the topological sense at least requires injectivity and a homeomorphism onto the image. Calling an arbitrary feature extractor an “embedding” therefore overstates what it establishes.

The safe language is: a versioned feature representation equips its image or quotient with the inherited weighted metric. It does not equip the original structural carrier with a proved metric or topology unless the relevant injectivity and transfer theorems are supplied.

## 17. Evaluation design

A credible evaluation needs four independent tracks. The axiom track tests diagonal, separation, symmetry, triangle inequality, and declared invariance. Exhaustive testing may be possible only on small bounded graph classes. It yields bounded evidence, not a universal theorem outside the enumeration.

The collision track searches for distinct graphs with equal features or maximal similarity. It should preserve minimal counterexamples and shrink larger failures. Structural equality must be computed independently of the score. For labelled legal arguments, collision reports should identify which rule, direction, dependency, or request distinction was lost.

The semantic track evaluates whether similar graphs preserve a named observation. For each profile (p), compute exact finite reference extensions and compare query-status vectors. A possible loss function is

$$
L_p(G,H)=
\mathbf 1[Ext_p(G)\neq Ext_p(H)]
\tag{54}
$$

or a set distance whose definition is disclosed. Equation (54) is `CONJECTURE` as an evaluation metric. It must not be called legal error unless extension equality is the approved task target.

The retrieval track measures practical candidate ranking. Given relevant pairs labelled through an independent process, report precision, recall, calibration of thresholds, and subgroup behavior. Human labels require a protocol and authority; model-generated labels cannot validate the model by circularity. Empirical retrieval success does not repair a failed metric axiom but may justify using a non-metric score for search.

Evaluation should also include adversarial transformations: relabel nodes, reverse defeats, replace one rule label, duplicate a stored edge, remove an assumption dependency, change a request key, or create a disconnected support component. The expected invariance depends on the carrier. Duplicate storage should not change a Finset-based structure, while direction and request changes should.

All results must bind the exact score version, feature schema, dataset, graph parser, and subject commit. A table should distinguish `FORMALIZED`, exhaustive bounded checks, sampled empirical tests, and counterexamples. The presence of one formal vector theorem must not upgrade the entire table.

## 18. Failure recovery and release gating

When an axiom fails, the first action is classification, not patching. Record the minimal witness, exact score version, expected property, actual output, and affected claims. If separation fails, disable equality substitution. If triangle inequality fails, disable metric-tree or triangle-pruning assumptions. If invariance fails, state which labels affect the score. If semantic preservation fails, require exact downstream verification after retrieval.

A failure status can be represented as

$$
SimilarityOutcome=
Complete(score)\;\uplus\;
Partial(score,obligations\neq\varnothing)\;\uplus\;Failure(reason).
\tag{55}
$$

Equation (55) is `CONJECTURE`, modeled on the `FORMALIZED` ULM `Outcome`. Any map over this result should preserve failure rather than return a numeric default.

Recovery has three legitimate paths. Redefine the score and create a new version; restrict the carrier or claim until the property holds; or keep the score explicitly non-metric. Deleting a counterexample or weakening structural equality is not recovery. If a quotient is adopted, the equivalence relation must be user-visible because it changes what counts as the same object.

A release gate should inspect certificate content, not merely job color. For a graph-metric claim it should require the formal or bounded property report, counterexample suite, exact subject identity, and nonempty observation declaration. Missing evidence should keep the claim blocked. A successful unrelated Lean build cannot certify a graph topology.

The legacy failure provides a positive engineering lesson. Preserving CE-001 and CE-002 prevents regression into the same overclaim. A future score can be better without inheriting a metric label until all axioms and carrier choices are re-established.

## 19. Evidence ledger

| Claim | Status | Evidence anchor | Boundary |
|---|---|---|---|
| Legacy graph-similarity axioms were removed | source fact | `JC_Formalization.lean:5-7` | Not a positive theorem |
| Strict self-similarity fails for a reported witness | `DERIVED/COUNTEREXAMPLE` | repository verification artifacts | Not Lean formalized |
| Distinct graphs can receive maximal similarity | `DERIVED/COUNTEREXAMPLE` | CE-002 artifacts | Refutes equality proxy |
| Similarity output stays in ([0,1]) | engineering evidence | bounded checker artifacts | Range only, not metric |
| Canonical argument identity is structural | `FORMALIZED` | `ULM08.CanonicalArgument` | Finite declared carrier |
| Defeat graph endpoints are request-bound | `FORMALIZED` | `ULM10.DefeatAF.WellFormed` | No approximate identity |
| Weighted vector distance has metric laws | `FORMALIZED` | `WeightedSupNorm.lean` | Vector carrier only |
| Graph feature embedding is injective | `CONJECTURE` | none | Needed for metric separation |
| Graph similarity induces a topology | `CONJECTURE` | none | No valid graph metric yet |
| Contracting feature updater preserves legal semantics | `CONJECTURE` | none | Needs observation theorem |

## 20. Validation boundary

Current Lean evidence supports structural argument identity, request-bound defeat graphs, observation-preservation composition in the abstract, and weighted vector distance laws. It does not support a graph metric. Counterexamples are preserved as negative engineering evidence. They should not be promoted to universal claims about every future graph score, but they decisively block the old score from being called a metric or equality proxy under the tested carrier.

A new graph score needs independent properties. Unit tests can check examples; property tests can search for counterexamples; SMT may prove bounded formulas over a finite encoding; Lean can formalize the carrier and universal theorem. Empirical retrieval performance can show task utility. These evidence types answer different questions.

## 21. Limitations

The paper does not reconstruct every legacy scoring implementation or independently rerun its counterexamples. It relies on preserved repository source and artifacts for their status. The ULM package does not include graph edit distance, Weisfeiler–Lehman features, spectral embeddings, graph kernels, or graph-isomorphism proofs. No dataset establishes that any graph similarity predicts legal relevance.

The weighted sup distance is finite-dimensional and assumes positive weights. Its Lean file does not prove a complete weighted metric space despite suggestive naming. The generic Banach theorem assumes completeness separately. No formal map connects canonical arguments or Dung frameworks to the vector carrier.

Legal similarity itself may be purpose-dependent. Structural identity, doctrinal analogy, outcome similarity, and explanation similarity need different observations. A single graph score is unlikely to preserve them all. This is a methodological caution, not a theorem of impossibility.

## 22. Reproducibility protocol

To reproduce a graph-comparison claim, state the exact graph carrier and equality relation. Record whether labels, directions, multiplicities, support rules, requests, and dependencies count toward identity. Then state the score and each claimed axiom separately. A bounded score should be called bounded, not metric. A symmetric score should be called symmetric, not a kernel.

Run the preserved counterexamples against the exact version, record inputs and outputs, and retain failures. If a vector embedding is proposed, publish (phi), weights, dimension, collision tests, and the intended observation. Prove injectivity or explicitly use a quotient. If semantic preservation is claimed, compare exact extension families under each profile.

Finally, keep similarity outside formal identity until the necessary theorem exists. This protocol permits approximate retrieval while preventing a score collision from merging distinct proof subjects or branches.

## 23. Permitted and forbidden uses

A non-metric similarity can still support candidate retrieval. A permitted workflow computes (s(G,H)), returns the top (k) candidates, and then independently checks structural identity, source binding, and semantic consequences. The score proposes where to look; it does not decide which graph is the same, which argument is accepted, or which legal result follows.

A second permitted use is exploratory clustering, provided the report names the score version and avoids metric-dependent algorithms unless their assumptions are independently satisfied. A visualization may reveal recurring patterns, but cluster boundaries are empirical artifacts. They are not proof that the grouped arguments share doctrine or outcome.

Forbidden uses follow directly from the failed properties. The score must not deduplicate proof subjects when distinct graphs can receive (s=1). It must not replace branch equality, because branch identity includes request, assumptions, profile, and extension. It must not justify metric pruning if triangle inequality is unproved. It must not support Banach convergence language when no graph metric, complete space, or contracting updater has been established.

The decision boundary can be summarized as

$$
Similarity\Rightarrow CandidateForVerification,
\qquad
Similarity\not\Rightarrow Identity\lor SemanticEquivalence.
\tag{56}
$$

Equation (56) is `DERIVED` policy guidance from the counterexamples and formal identity structures. It is not a Lean theorem. The first implication describes an authorized engineering role, not logical entailment.

If a future score passes all metric axioms on a declared carrier, the claim may be upgraded for that carrier and version. It still would not automatically prove legal relevance. Metric validity, semantic preservation, empirical usefulness, and legal acceptability remain four separate evidence questions. Publication and release materials should report them in separate rows.

This permitted-use discipline is intentionally reversible. A failed score can be demoted to retrieval without deleting it, while a later verified metric can be introduced under a new name and subject. Preserving versions and counterexamples makes that evolution auditable.

For downstream users, every similarity result should therefore carry a short capability label: `RANK_ONLY`, `PSEUDOMETRIC_ON_FEATURE_QUOTIENT`, or `VERIFIED_METRIC_ON_DECLARED_CARRIER`. The present legacy score belongs only in the first category. These labels are `CONJECTURE` as an interface design, but they state the evidence boundary directly and prevent a user interface from silently upgrading an exploratory score through ambiguous wording.

## 24. Conclusion

The current repository has no formal graph metric or graph topology. It has preserved counterexamples against the earlier similarity axioms, formal structural identity for legal arguments, finite defeat semantics, and a genuine weighted distance on real vectors. The constructive path is not to rename the vector theorem or ignore graph collisions. It is to define the graph carrier, representation, equality or quotient, observations, and proof targets explicitly. Until then, graph similarity is an analytical score, not a formal identity, metric, kernel, or topology.

## Declarations

**Funding.** No external funding was received.

**Conflict of Interest.** The author declares no competing interests.

**Data Availability.** Public source and counterexample artifacts are contained in the `legal-math-modeling` repository [@LegalMathModeling2026]. No private legal data are used.

**Ethics.** No human participants or private records were used. Similarity outputs must not be treated as legal conclusions or identity certificates.

**CRediT Author Statement.** Laupinco: Conceptualization, Methodology, Software, Formal Analysis, Investigation, Writing—Original Draft, Writing—Review and Editing.

**AI Disclosure.** AI assistance was used for drafting and consistency checking. The author reviewed the counterexample status, formal boundaries, equations, and final prose and remains responsible for the manuscript.

## References

References are maintained in `paper/references.bib` [@LegalMathModeling2026; @Dung1995; @PrakkenSartor1997; @RisslandAshley1987; @Hoare1969; @DeMouraUllrich2021; @Mathlib2020; @Banach1922].
