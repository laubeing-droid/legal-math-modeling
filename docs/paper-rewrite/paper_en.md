# Reporting Distortion in Legal Reasoning Systems: Six Inexpressibility Properties and the Strength of Their Claims

**Master manuscript, English version** (parallel to paper_cn.md; the Chinese version leads)

**Status**: written section by section; Sections 1–3 complete.
**Build and axiom-audit status**: CI_NOT_RUN (Lean is never executed locally; continuous integration is the sole authority, and triggering it requires per-round authorization).
**Count bindings**: the counts 145, 27, and 4 are static text measurements at the source level, bound to the generated artifact `docs/formal-release/theorem_inventory_v3.json` (subject `1e0875c`). No commit after that subject touched the numbered modules, so the counts are unaffected. That artifact declares itself a static inventory, not a release certificate.
**Sourcing discipline**: no sentence of this manuscript derives from the legacy documents under `paper/`. Every number and strong assertion maps to a counterpart recorded in the claim table at the end of each section.

---

## Section 1 Introduction

> **Scope of this section.** Of the six classes of reporting distortion, four have their carriers inside the sixteen numbered modules; the fifth has its trust-vector version inside and its permission-rank version outside; the sixth lies entirely outside. The counts appearing here, 145 (total theorem declarations in the numbered modules) and 27 (forwarding declarations in the final module), are bound to the artifact named above. Substantive legal correctness, refinement of any runtime implementation, and uniform coverage of the release process all lie outside what this paper has proved; the unproved list and its ordering appear in Section 9.

Computer-assisted legal reasoning has moved in Chinese judicial practice from a research topic to a work requirement. The Guiding Opinions of the Supreme People's Court on Unifying Legal Application and Strengthening Similar-Case Retrieval (for trial implementation) has been in trial implementation since 31 July 2020, and regulates the concept of a similar case together with the premises, scope, and methods of retrieval [1]. On 27 February 2024, the SPC Case Database went online and opened to the public [2]. Together these institutions impose one concrete demand: when a system delivers a conclusion, it must be able to state how that conclusion was reached.

Existing research answers this demand along two directions. One direction studies the identification and comparison of similar cases, asking how a pending case is judged to belong to the same class as decided cases and how retrieval results are combined with the pending case [3]. The other direction studies formal properties of reasoning, including defeasible reasoning, abstract argumentation frameworks, and priority rules [4]. Between the two lines lies a shared gap: the first cares whether conclusions are reliable, the second whether inference is valid, yet what a system actually hands to a person is a single act of reporting. What the solver returns, which arguments the evaluator accepts, and which status is finally presented to the adjudicator together constitute that report. The correctness of the reporting stage is guaranteed neither by similar-case retrieval norms nor by argumentation theory.

This paper addresses one specific kind of reporting distortion: a program reporting "not established" when it has in fact not finished checking. Type-level inexpressibility means that, given the fixed types, one cannot write code that violates the requirement; the guarantee relies on neither runtime checks nor documentary convention.

This kind of distortion is realized in this paper as six classes. Four lie inside this paper's trunk model: a failure cannot be mapped into a normal payload; a claim of incompleteness must hand over at least one still-open obligation; a claim that the family of extensions is empty must carry a proof of that emptiness, so "no stable extension exists" cannot be reported as "the claim fails"; and an incomplete solve cannot be rewritten into an adverse adjudication. Two lie in independent theories outside the trunk: aggregation cannot raise assurance, whose trust-vector version holds inside the trunk while its permission-rank version lies outside; and resubmitting a tainted input cannot clean it, a theory that likewise lies outside the trunk. This inside/outside distinction is a result of this paper, not an expository inconvenience.

The trunk model consists of sixteen Lean 4 modules containing 145 theorem declarations. For every declaration this paper states its actual strength, and concentrates its qualifiers in the scope box opening each section. Three strengths must be distinguished: inexpressibility at the type level; genuine induction and construction, including preservation of request identity across machine runs, monotonicity of the Dung characteristic function, and uniqueness of the grounded extension as the least fixed point; and forwarding of earlier theorems or of library results, the category to which all 27 declarations of the final module belong. The number 145 is verifiable at the source level; build success and the axiom audit can be claimed only after continuous integration binds them to a named commit, and at the time of writing that has not been obtained.

The temporal and permission theories outside the trunk, together with a considerably larger argumentation semantics, currently share only parallel definitions with the trunk; no bridging theorem connects them. That gap is set out on its own in Section 8, and the full unproved list with its proposed ordering in Section 9.

**Citation keys for this section**: [1] `SPCSimilarCaseGuideline2020` (effective date verified verbatim against the document's own sentence; the document number was not confirmed against an official text and is banned from print throughout); [2] `SPCCaseDatabase2024` (launch date verified verbatim); [3] `QiXiaodan2025SimilarCaseSearch`, `DengJinting2021CalcLawMethods`, `JiWeidong2024CalcLaw`; [4] `Dung1995`, `PrakkenSartor1997`, `BenchCapon2003`.

**Claim table for this section**

| Statement in text | Number | Counterpart (subject-bound) |
|---|---|---|
| Sixteen modules, 145 theorem declarations | 145 | `theorem_inventory_v3.json`, scope ulm_package: file_count 19 (16 numbered modules + 3 audit drivers, the drivers holding 0 theorems), theorem_count 145; `ULMAllTheoremsAxiomAudit.lean` lists 145 axiom-audit targets; the two lists differ by zero elements in both directions (gaps field of the same artifact) |
| All 27 declarations of the final module are forwardings | 27 | Same artifact, ULM16TheoryComposition.lean theorem_count 27; `ULMCoreCompAxiomAudit.lean` lists 27 targets; each of the 27 proof bodies was checked by hand and is a single application of an existing theorem or a definitional equality |
| Build and axiom audit not obtained | — | Lean is never executed locally; no authorized CI run exists; status recorded as CI_NOT_RUN |

---

## Section 2 Method and Claim Strength

> **Scope of this section.** This section describes only the shape of the types and the strength of the theorem statements; it does not reproduce proof details. Of the six inexpressibility classes, four have their carriers inside the sixteen numbered modules; the fifth has its trust-vector version inside the numbered modules, while its permission-rank version and the sixth class each live in one of two independent files outside the trunk. The counts 145, 27, and 4 are bound to the artifact named in the manuscript header, with the counting convention fixed in the final paragraph of this section. Theorem names and file line numbers appear only in the tables at the end of this section, never in the running text. Build and axiom-audit status: CI_NOT_RUN.

The trunk is a Lean 4 package of sixteen numbered modules chained in order. The first module issues the identity card of a request: a request is first located by its context, which holds five fields, namely the case scope, the run scope, the scenario, the base version, and the semantics version, with the run scope required to belong to the same case; on top of the context the request additionally binds the argumentation semantics, the query identifier, and the mapping version. Well-formedness is written as a predicate on each of the two levels, context and request. Each later module depends only on its predecessor, until the sixteenth module collects all results under a stable set of names. The trunk's entire dependence on the rest of the repository is four files: the semantics registry, the fact-admission specification, the finite monotone iteration kernel, and the Horn fixed-point module; its only dependence outside the repository is the mathematical library.

The trunk gathers the intermediate products of one act of reporting into three types. The computational outcome of a request is one of three values: a complete value, a partial value carrying obligations, or a failure core. The partial-value constructor must carry at least one still-open obligation, so a partial value with an empty obligation set cannot be constructed in the type at all. The failure core records the kind of failure, its reason, and the request it belongs to; the outcome map defined by the trunk returns that very failure on the failure branch, by definition.

The outcome of argument evaluation is another three-way type. A constructor claiming that no extension exists must carry a proof of emptiness, that is, evidence of the fact that the extension family of the chosen semantics is empty; a constructor claiming to deliver extensions must carry evidence that they equal that family; a constructor claiming the computation is unfinished must carry two things, a record that every discovered part already satisfies the chosen semantics, and at least one still-open obligation. Before an evaluator can report "no extension", the emptiness proof must already be in hand.

The adjudication function folds the evaluation outcome, an optional adjudicative authority, and an optional procedural conclusion into one of four outputs. When the evaluation is unfinished, the output can only be solver-incomplete, together with its open obligations; when both the authority and the procedural conclusion are absent, the output can only be pending legal judgment. For a request to end in an adverse finding, there must first exist an adjudicative authority valid for that exact request whose proof finding is explicitly unmet; the emptiness of the extension family by itself entails no substantive conclusion. The four outputs are four constructors of one inductive type, and solver-incomplete and adjudicated are simply two different values at the type level.

The full list of six inexpressibility classes can now be stated. Four lie inside the trunk: a failure is not mapped into a normal payload; a claim of incompleteness must hand over an open obligation; a claim that the extension family is empty must hand over a proof of emptiness; an incomplete solve is not rewritten into an adverse adjudication. Two lie outside: aggregation cannot raise assurance; resubmitting a tainted input cannot clean it. The fifth class has an additional trust-vector version inside the trunk, stating that a coordinatewise-minimum trust combination is below either input; its permission-rank version lies outside the trunk and states that any number of consensus rounds at the same level cannot produce a level increase. The sixth class states that a tainted input keeps its taint no matter how many times it is resubmitted. The precise meaning of type-level inexpressibility, for these six classes, is this: a value violating the requirement cannot be constructed past type checking, because the requirement's carrier is the fields and constructors themselves; neither runtime checks nor documentary convention play any role here.

This paper labels each of the 145 theorems with one of three strengths. The first is type-level inexpressibility, whose proofs close by constructor discrimination or by definitional equality and usually occupy a line or two; what they assert is not that some property holds, but that code violating the convention cannot be written. The second is genuine induction and construction, which carries the paper: the whole chain of the finite monotone iteration kernel, from monotonicity to the stopping point (Section 3 is devoted to it); monotonicity of the argumentation characteristic function; leastness and uniqueness of the grounded extension and existence of a preferred extension; preservation of request identity across machine runs; inclusion monotonicity of the incremental operator with respect to the iteration sequence; and consistency of an evaluator over an index-carrying family of expressions. The third is forwarding: two theorems of the seventh module each invoke an existing theorem of the Horn kernel; four contraction-mapping theorems of the fifteenth module are one-line wrappers of library theorems and hold only on complete nonempty metric spaces; and all 27 declarations of the sixteenth module merely give earlier theorems stable names.

The need to distinguish strengths comes from the reporting problem itself: what a theorem promises depends on what its proof stands on. The credibility of type inexpressibility comes from the shape of the definitions, and a reader can verify it by checking the fields; the credibility of genuine induction lies in the proof and must be read line by line; the credibility of a forwarding lies in the theorem forwarded. This paper records the strength of every theorem, so a reader can weigh each claim without reading proofs; the entries are filed section by section and consolidated in Section 9.

The counting convention is fixed here and is not re-explained later. 145 is the total number of theorem declarations in the nineteen files whose names begin with the trunk prefix, of which the sixteen numbered modules contain the theorems and the three axiom-audit drivers contain none; the same number is the count of targets in the full axiom-audit driver, and the two lists differ by zero elements in both directions. Counting by the beginning-of-line convention, which counts only declarations whose line begins with the theorem keyword, yields 111; the difference consists entirely of declarations sharing a line with an attribute annotation, and this paper uses 145 throughout. 27 is the theorem count of the sixteenth module, equal to the target count of the core-composition audit, and every one of them is a forwarding. 4 is the number of repository files the trunk depends on. All three numbers are static text measurements at the source level, bound by the generated artifact to a named commit; whether the source actually passes type checking and the axiom audit remains a matter for continuous integration bound to the same commit, and at the time of writing that has not been run.

**Claim table for this section**

| Carrier | Content | Location | Strength |
|---|---|---|---|
| Obligation field of the partial-value constructor | A partial result must carry a nonempty set of still-open obligations | ULM02 (module 2) | Type inexpressibility |
| Failure core and outcome mapping | The map is defined to return the failure unchanged on that branch | ULM02 | Type inexpressibility |
| Three-way evaluation result | No-extension carries an emptiness proof; extensions carry an equality witness; unfinished carries a satisfaction record for the discovered part plus an open obligation | ULM11 (module 11) | Type inexpressibility |
| Adjudication function and four outputs | Unfinished yields only solver-incomplete; no authority yields only pending; an adverse finding requires an authority with an unmet finding; distinct outputs are distinct constructors | ULM12 (module 12) | Type inexpressibility |
| Coordinatewise-minimum trust vector | The trust combination is below either input; an open specification slot stays open under combination | ULM14 (module 14) | Type inexpressibility (in-trunk version) |
| Rank-maximum consensus | Any number of consensus rounds at one level has rank at most that level | ReceiptAuthority (outside trunk) | Induction on the count (outside-trunk version) |
| Taint join and resubmission | Any tainted input taints the whole collection; resubmission and majority consensus leave the taint unchanged | TaintNoninterference (outside trunk) | Induction and construction (outside trunk) |

| Count | Convention | Counterpart |
|---|---|---|
| 145 | Total theorem declarations in nineteen ULM files (16 modules + 3 audit drivers, drivers holding 0 theorems) | `theorem_inventory_v3.json` scope ulm_package and `ULMAllTheoremsAxiomAudit.lean`; zero symmetric difference |
| 111 | Beginning-of-line convention (line starts with the theorem keyword) | Same artifact, field theorem_count_bol_convention; the gap to 145 consists of same-line attribute annotations |
| 27 | Theorem count of the sixteenth module, all forwardings | Same artifact and `ULMCoreCompAxiomAudit.lean`; checked entry by entry by hand |
| 4 | Repository files the trunk depends on | Module import lists: semantics registry, fact-admission specification, finite monotone iteration, Horn fixed point |

| Example of strength | Theorem | Location | Shape |
|---|---|---|---|
| Genuine induction | Iteration monotone; iteration stable; inequality gives strict containment; inequality gives strict cardinality growth; a stopping point exists within the carrier's cardinality; the stopping point occurs exactly at the carrier's cardinality | FiniteMonotoneIteration | Induction on the index; induction on appended steps; monotonicity plus antisymmetry; one library forwarding; contradiction with a cardinality chain; derived from stability |
| Genuine induction | Characteristic function monotone (the hardest proof in the repository, about fifteen lines) | ULM10, lines 67–88 | Monotone transfer through filters and the defense condition |
| Genuine induction | Grounded leastness; grounded uniqueness; preferred existence | ULM10, lines 99, 161, 199 | Induction over iteration index; antisymmetry; a maximal element of the powerset |
| Genuine induction | Runs preserve the request; the incremental operator is inclusion-monotone; the evaluator agrees with its denotation | ULM05, line 75; ULM15, line 48; ULM13, line 145 | Induction over runs; induction plus transitivity; induction over an index-carrying expression family |
| Forwarding | Support-closure fixed point and leastness | ULM07, lines 21 and 25 | Each invokes a Horn theorem once |
| Forwarding | Four contraction-mapping theorems (existence, uniqueness, convergence, a-priori error bound) | ULM15, lines 126, 131, 139, 146 | One-line wrappers of library theorems, with completeness and nonemptiness as hypotheses |

---

## Section 3 Finite Monotone Iteration: The Sole Kernel

> **Scope of this section.** This section asserts only the ten theorem declarations of the single kernel file (statements checked against the current working tree; build status CI_NOT_RUN). The kernel proves stabilization and the existence and position of the stopping point; it does not package leastness. Leastness is supplied separately by both instantiations and is treated in Section 4. The kernel's statement concerns no infinite carrier; monotonicity is a field of the structure, delivered by whoever instantiates it. The "sole kernel" claim rests on a check of module import relations, given in the sixth paragraph. The repository also contains an earlier Dung fixed-point file and the contraction-mapping route; the trunk imports neither, and both are assigned to Section 8.

The load-bearing structure of the trunk is not a theorem but a reusable kernel. The support closure of Horn rules and the grounded extension of Dung semantics, two tasks that look different, are mathematically the same task: start from a finite set, apply a grow-only operator repeatedly, and ask when it stops and where. The kernel does this common work once, and each of the two instantiations supplies only its entry data.

A finite monotone system consists of three things: a finite carrier, a step operator from subsets of the carrier to subsets of the carrier, and two promises about the operator. The first promise says the operator's output always stays inside the carrier; the second says the operator is monotone, so that a larger input can only give a larger output. The monotonicity promise is a field of the structure, not a theorem; to construct a system one must first deliver a proof of monotonicity, and without it no value of the system type can be obtained. The iteration sequence starts from the empty set and applies the operator to the previous result at each step.

Three basic properties of the sequence each take one induction over the index. The empty set is contained in every set; that is the base. Monotonicity says each step's output contains the previous step's output, and the inductive step uses precisely the monotonicity promise stored in the structure. Stability says that once the sequence stops at some step it stops forever: inducting on the number of appended steps, each step applies the same operator, and an operator applied to equal inputs gives equal outputs.

The theorem that actually carries weight argues by cardinality. Suppose the sequence never stops; then every step must grow strictly. In such a sequence, inequality together with monotonicity gives strict containment, and strict containment gives a strict increase in cardinality. The carrier has only finitely many elements; starting from zero and gaining at least one element per step, after the carrier's cardinality plus one steps the sequence would have cardinality exceeding the carrier itself, contradicting the promise that outputs stay inside the carrier. The conclusion reads two ways: a stopping point exists no later than the carrier's cardinality; and the stopping point has already occurred exactly at the carrier's cardinality. The second reading turns "when does it stop" into a bound one can execute against.

The set reached at a stopping point is a fixed point of the operator. Whether it is the least of all fixed points is not claimed by the kernel; that property is supplied by each of the two instantiations through one induction over the iteration index, the two inductions sharing the same shape and using nothing beyond the monotonicity promise plus the fixed-point equation. That the kernel does not package leastness as a general theorem is the current state of the repository rather than a necessity of design, and Section 9 lists it as a candidate for unification.

Calling it the sole kernel rests on a check of dependency relations rather than on naming: among the sixteen numbered modules, every theorem touching fixed points either cites the kernel file directly or cites the Horn theorem file built on the kernel; the trunk cites exactly one general fixed-point theory. The contraction-mapping route goes through the library's complete metric space theorems and runs parallel to the finite-carrier kernel without intersecting it. The repository also holds an earlier Dung fixed-point file that the trunk does not import; its relation to the trunk is dealt with in Section 8.

The kernel's boundaries must be stated as well. It treats only expanding operators on finite carriers and asserts nothing about infinite carriers; the operator may hold still for some steps, and the stabilization conclusion applies unchanged. It supplies no semantic interpretation of the operator; semantics belongs to the instantiations, and Section 4 gives both in full.

**Claim table for this section**

| Theorem | Line | Content | Filed strength |
|---|---|---|---|
| Iteration base; iteration step | 28, 30 | The sequence is empty at zero steps; one step is the operator applied to the previous step | Closed by definitional equality |
| Iteration stays in the carrier | 32 | The result at any step count lies in the carrier | Induction on the index |
| Iteration monotone | 39 | Each step's output contains the previous output | Recursive induction on the index, using the monotonicity field |
| Iteration stable | 46 | Equality of two adjacent steps implies equality forever after | Induction on appended steps |
| Inequality gives strict containment | 62 | Monotonicity plus inequality yields strict containment | Derived from the monotonicity theorem plus antisymmetry |
| Inequality gives strict cardinality growth | 71 | Strict containment has strictly greater cardinality | One application of a library theorem |
| Cardinality bounded by the carrier | 75 | The cardinality of an iterate never exceeds the carrier's | One application of a library theorem |
| A stopping point within the carrier's cardinality | 80 | There exists a stopping point no later than the carrier's cardinality | Contradiction with a cardinality chain (the core of the file) |
| Stopped exactly at the carrier's cardinality | 103 | Step carrier-cardinality equals the next step | Derived from the previous item plus stability and arithmetic |

| Adjacent claim | Verification outcome |
|---|---|
| The kernel proves the least fixed point | Does not hold. The kernel contains no leastness theorem; leastness is proved once in the Horn instantiation (HornFixedPoint, from line 60) and once in the Dung instantiation (ULM10, from line 99), in the same shape |
| "Sole kernel" | Holds, by the module import lists: the only general fixed-point theory cited by the numbered modules is this one; the earlier Dung fixed-point file and the contraction-mapping route are outside the trunk's imports |

---

## Section 4 Two instantiations: Horn support closure and Dung semantics

> **[S4-SCOPE] Scope of this section.** This section only shows how the common formal skeleton is instantiated as Horn-rule support closure and as Dung argumentation semantics, and compares the two leastness constructions; structural similarity is not promoted into a claim that the two theories are equivalent. Running examples come from existing definitions in the temporal theory and the minimal obligation theory. Counts follow the conventions fixed in Section 2; this section introduces none.

<!-- S4-P01 -->
The first instantiation handles Horn rules. The instantiator supplies three pieces of entry data: a finite predicate universe, a rule set whose premises and conclusions are predicates, and the monotonicity promise of the one-step support-closure operator. With these three delivered, a finite monotone system exists; the kernel theorems apply immediately, the iteration stops within the carrier's cardinality, and the stopping point is the support closure of the rule set.

<!-- S4-P02 -->
Leastness of the support closure is supplied by the instantiation, in the shape of one induction over iteration indices. Take any fixed point of the rule operator and first show that every iterate is contained in it: the base is the empty set, the key step applies the monotonicity promise to the induction hypothesis and closes with the fixed-point equation; instantiating the induction at the carrier's cardinality then yields containment of the iteration result in every fixed point. Only two facts are used, the monotonicity promise and the fixed-point equation, and neither concerns the logical meaning of the rules.

<!-- S4-P03 -->
The second instantiation handles Dung semantics. The carrier becomes a finite set of argument identifiers and the step operator becomes the characteristic function of the argumentation framework: an argument enters the set at the next step exactly when it is defended by undefeated members of the set. Monotonicity of the characteristic function requires a transfer argument over filters and defense conditions, the longest proof in the trunk; once delivered, the grounded extension is defined as the iteration result of that system.

<!-- S4-P04 -->
Leastness of the grounded extension is supplied by an induction of the same shape: take any fixed point of the characteristic function, induct over iteration indices, use monotonicity plus the fixed-point equation at each step, and conclude at the cardinality of the argument set. The two leastness constructions are therefore two entries into one skeleton; the skeleton itself carries no semantic commitment to support closure or grounded extensions, and claiming that the two theories are thereby equivalent goes beyond what this section proves.

<!-- S4-P05 -->
Running examples place these constructions back in a legal context. The pointwise extension of a litigation timeline in the temporal theory, and the rule progression of the direct-violation shape for contract breach in the minimal obligation theory, are both entries of the skeleton on different carriers; the definition that permission-type rules produce no direct violation marks the boundary between rule shapes on the same carrier. These examples are illustrative and verify no real-case reasoning chain.

**Claims table for this section**

| Claim ID | Claim | Supporting object | Status | Boundary |
|---|---|---|---|---|
| S4-C01 | Horn support closure stops within the carrier's cardinality and the stop is the closure | Kernel theorems plus Horn instantiation entry data | Proved | Not extrapolated to Dung semantics |
| S4-C02 | The support closure is contained in every fixed point of the rule operator | HornFixedPoint from line 60, induction over iteration indices | Proved | Uses only the monotonicity promise and the fixed-point equation |
| S4-C03 | The grounded extension is the iteration result of the characteristic function and is least | ULM10 from line 99, same-shape induction | Proved | Holds for the defeat semantics only |
| S4-C04 | The two leastness constructions share one shape | Line-by-line reading of both sources | Structural check | No equivalence of the two theories claimed |
| S4-C05 | Temporal and obligation running examples | Existing definitions in TemporalKripke and DDLDefinitions | Example | Not a general jurisprudential proof |

---

## Section 5 The trunk encoding layer: identity, results, types, and premises

> **[S5-SCOPE] Scope of this section.** This section only organizes the encoding responsibilities of the trunk modules, namely request identity, the result algebra, type relations, obligations, the machine, and premise provenance, and admits the kernel object types added in the present round; it describes how the machine distinguishes objects, not a claim that these encodings exhaust legal meaning.

<!-- S5-P01 -->
Request identity is carried by two levels of context. The context first fixes five items, case scope, run scope, scenario, base version, and semantics version, with the run scope required to stay inside one case; the request then binds the argumentation semantics, the query identifier, and the mapping version. Each level carries its own well-formedness predicate, and a request that fails it cannot enter later modules. Identity is thus a statically checkable credential, not a runtime label.

<!-- S5-P02 -->
The outcome of a computation is encoded by a three-way type: a total value, a partial value with obligations, or a failure core. A partial value must carry at least one open obligation; the failure core records the failure kind, reason, and owning request; and the outcome mapping is definitionally the identity on the failure branch. This layer is the carrier of the first inexpressibility of Section 2: code that maps failure into a normal payload cannot be written.

<!-- S5-P03 -->
Obligations and the machine encode what is owed as a trackable object. The machine's run sequence preserves the request, with every state transition carrying the same request identity, and obligations are listed explicitly in partial values. Premise provenance is delegated to the fact-admission specification: candidates, user assumptions, and disputed facts never gain decisive standing at any entrance, and admission levels rise only through independent, scope-bound external credentials.

<!-- S5-P04 -->
The present round adds the legal-semantic kernel objects to the type graph. The relation whole carries shared-constraint fields; power, obligation, and occurrence are three independent fields that do not imply one another; events carry time points with the history structure holding the time order; the jurisdiction axis exists on its own. Truth and judgment are layered, with judgment three-valued and disposition an independent field rather than a fourth value. The size and layering of the type graph are pinned by a machine-readable manifest that documents do not duplicate.

**Claims table for this section**

| Claim ID | Claim | Supporting object | Status | Boundary |
|---|---|---|---|---|
| S5-C01 | Two-level well-formed request identity, statically checkable | Context and request definitions of the first two modules | Implemented | Encoding layer, not a legal-validity layer |
| S5-C02 | Partial values carry open obligations; failure returned as is | Constructors and outcome mapping of the second module | Type-inexpressible | — |
| S5-C03 | Run sequences preserve the request; candidate facts never decisive | Machine-module theorem and fact-admission specification | Proved / contract | No doctrine of burden allocation |
| S5-C03 | Run sequences preserve the request; candidate facts never decisive | Machine-module theorem and fact-admission specification | Proved / contract | No doctrine of burden allocation |
| S5-C04 | Kernel object types enter the graph; three modalities mutually non-implying | Type registry manifest and existing witness theorems | Proved | Semantics left to upper layers |
| S5-C05 | Truth/judgment layering; disposition as a field | Kernel contract tests and the formalization module | Proved (contract-level) | No concrete norm content |

---

## Section 6 Branch queries and procedural adjudication

> **[S6-SCOPE] Scope of this section.** This section discusses only how branch queries, procedural determinations, and proof-carrying constructions constrain result propagation; a determinate procedural result must not be read as assigning the same judgment to a substantive proposition. Sentencing and probability are out of scope here.

<!-- S6-P01 -->
Branch queries type what is being asked. Queries split into substantive, procedural, and effect kinds; the result of one evaluation is a pair: judgment and disposition. Judgment is three-valued, namely established, not established, and undetermined, while disposition is an independent field of procedural legal effect and may be empty. A determinate judgment on a procedural question does not automatically generate a judgment on the substantive question: the evaluation batch returns exactly the set of asked questions, and no channel writes procedural conclusions into substantive ones in passing.

<!-- S6-P02 -->
Propagation limits tighten again at the event layer. Adjudication events split four ways by effect: confirmatory, constitutive, performance, and procedural binding. A confirmatory adjudication cannot create a relation at the type level, because the non-constitutive constructors carry no next-state field at all; only constitutive events transfer entity state, and the transfer leaves the evidence set untouched. A losing sample therefore cannot rewrite the normative ontology through a confirmatory event.

<!-- S6-P03 -->
The evidence-side counterpart is this: evidence updates only narrow the candidate set, narrowing is typed by a subset premise, and the normative state is returned unchanged. Undetermined output has a narrowing gate, and a proof that four families of rules are exhausted must accompany it. Together the three clauses state this section's claim: the procedural layer and the evidence layer each keep their own gate, and neither decides for the other.

**Claims table for this section**

| Claim ID | Claim | Supporting object | Status | Boundary |
|---|---|---|---|---|
| S6-C01 | The evaluation batch returns only the asked questions | Kernel contract, on both the test and formalization sides | Proved (contract-level) | No burden-of-proof semantics of judgment |
| S6-C02 | Non-constitutive events structurally cannot carry a next state | The kernel's event inductive type | Type-inexpressible | — |
| S6-C03 | Constitutive transfer preserves the evidence set; narrowing preserves the ontology | Transfer and narrowing theorems | Proved | Transfer semantics interpreted by the norm layer |
| S6-C04 | Undetermined requires a proof of four-family exhaustion | The proof field of the undetermined constructor | Type-inexpressible | Exhaustion criteria supplied by rule packs |

---

## Section 7 Dimensions, trust meets, and assurance envelopes

> **[S7-SCOPE] Scope of this section.** This section examines how dimensional arithmetic, trust meets, and assurance envelopes constrain the admissible use of computational outputs; these mechanisms restrict acceptance without converting empirical estimates into normative truth.

<!-- S7-P01 -->
Numbers must enter computation with dimensions and exactness. Exact values are carried as integer minor units with an explicit rounding policy, excluding binary floats; the evaluator has a dedicated theorem on consistency over indexed expression families. The point of dimensional arithmetic is not speed but that wrongly combined numbers cannot be assembled in the first place, so amounts and time limits never silently change tracks mid-computation.

<!-- S7-P02 -->
Trust merges coordinatewise to the minimum inside the trunk: the trust of a merged result never exceeds any input, and open specification slots stay open under aggregation. The permission-rank version lives outside the trunk and says that any number of consensus rounds at one level never produces a level rise. Read together: neither horizontal merging nor vertical repetition lifts the standing of evidence.

<!-- S7-P03 -->
The assurance envelope governs how certain is certain enough. The contraction-mapping route supplies four forwarded theorems, existence, uniqueness, convergence, and an a-priori error bound, under the premise of a complete nonempty metric space; the certificate envelope and the independent checker require that producers hand over no trusted booleans and that checkers recompute. Certified approximators turn admission itself into proof obligations on top of this: error bound, tolerance, applicability domain, and the scaled contraction ratio all become constructor-time fields, and without a certificate there is no admission.

<!-- S7-P04 -->
Outputs passing this gate remain reference-grade. The approximator's identity marker has exactly one grade, reference, and interval, identity, and certificate travel with the output, the output failing if any is missing; probability intervals computed on retrieved populations carry identity markers too, with synthetic data permanently hard-marked as unvalidated. The boundary between reference and decisive is thus not a wording convention but a structural consequence of types and certificates.

**Claims table for this section**

| Claim ID | Claim | Supporting object | Status | Boundary |
|---|---|---|---|---|
| S7-C01 | Type discipline for exact values and dimensions | Exact-numeric contract and the evaluator-consistency theorem | Proved | No doctrine of currency conversion |
| S7-C02 | Trust merge never exceeds inputs; consensus lifts no rank | Coordinatewise minimum in the trunk; rank theorem outside | Proved | No unifying bridge between the two versions (Section 8) |
| S7-C03 | Four error-bound theorems of the contraction route | Forwarded library theorems, complete-nonempty premise | Forwarded | Premise not self-proved in the trunk |
| S7-C04 | No certificate, no entry; outputs permanently reference-grade | The proof-carrying admission construction | Type-inexpressible | Certificates prove no legal correctness |

---

## Section 8 Independent theories outside the trunk, and gaps

> **[S8-SCOPE] Scope of this section.** This section keeps ununified parallel theories and engineering structures outside the trunk and records, item by item, which bridge to the current kernel is still missing; the existence of an implementation is kept strictly distinct from formal unification.

<!-- S8-P01 -->
The temporal, permission, and taint theories exist independently, sharing definitions but no bridge theorems with the trunk. The temporal theory has its own worlds and accessibility relation; the permission theory has its own hierarchy; the taint theory has its own conservation of merging. Each stands on its own, but the trunk imports none of them, and their conclusions cannot be forwarded by trunk theorems. The gap is structural: what is missing is bridges, not proofs.

<!-- S8-P02 -->
Argumentation semantics has more parallel copies. An earlier Dung fixed-point file runs alongside the trunk's; the attack kinds of abstract argumentation frameworks are defined in two places; at least four priority mechanisms coexist; the number of cross-file homonyms is considerable, including at least one self-attack check folded into a package conflict. No proved equivalence or containment theorem exists between these copies, and any phrasing that they are really the same thing currently has no basis.

<!-- S8-P03 -->
Confirmed gaps at the engineering layer include: the permission file defines a value as false and then proves its negation, with no lattice laws proved; the certificate checker reads six self-reported fields only; at the old audit baseline, eleven of the forty-eight registered type names had no implementation carrier, and after the present round the registry holds fifty-two with every added name having a contract carrier, but the old gap remains unfilled. The receipt ledger and the claims lists are machine-readable with drift gates; that is engineering closure and changes no proof status.

<!-- S8-P04 -->
The honest reading of these gaps: what the trunk claims and what it does not is checkable at the source level. The parallel theories and the gap list form the engineering half of Section 9's unproved list; the two sections together give a map of where one can still go, not an announcement of arrival.

**Claims table for this section**

| Claim ID | Claim | Supporting object | Status | Boundary |
|---|---|---|---|---|
| S8-C01 | Temporal, permission, taint theories share zero bridges with the trunk | Module import list check | Structural check | No judgment on the theories themselves |
| S8-C02 | Multiple parallel copies of Dung semantics, attack kinds, priorities | Source census, audit-confirmed | Confirmed | No equivalence theorem of any kind |
| S8-C03 | Permission rank defined false then negated; checker reads self-reported fields | Corresponding sources | Confirmed | Listed as unproved |
| S8-C04 | Eleven names unimplemented at the old audit; registry now fifty-two | Old audit baseline and the current machine-readable manifest | Confirmed (time-distinguished) | Old gap unfilled |

---

## Section 9 The unproved list, the order of advance, and conclusions

> **[S9-SCOPE] Scope of this section.** This section only consolidates what remains unproved or unbridged at the current construction snapshot, states the order of further formalization, and aggregates the paper's claims ledger; engineering integration, passing tests, and local theorems are not enlarged into a claim that the legal system is completely proved.

<!-- S9-P01 -->
Unproved items inside the trunk are ordered by load. First, the three properties of argumentation semantics: conflict-freeness, admissibility, and completeness have definitions in the trunk but no corresponding existence or characterization theorems for extensions; next, the completeness bridge for the weighted metric space, whose contraction-route premise is not self-proved in the trunk; then the dependency bridge between two modules, machine reachability and termination, non-monotonic update, the algebraic laws of assurance combination, and the inhabitance problems of the contract-closure instances. The full axiom audit stays in its established place in continuous integration, unmoved by this round.

<!-- S9-P02 -->
Cross-layer unproved items include: the delimitation theorems of the six inexpressibility classes are all unproved, and this paper claims type-level inexpressibility only, never closure of the boundary; the item-by-item alignment of the external target spectrum sits in the external ledger, for which this round built only a pending skeleton, the non-alignment being an explicit status rather than an omission; and the end-to-end bridge from the contraction error formula to the existing numeric theorems is unbuilt. Each item carries an explicit status marker and none is silenced by the pipeline's advance.

<!-- S9-P03 -->
What the present round did land can be counted honestly. The type registry grew to fifty-two and passed one full build; the machine-readable receipt ledger pinned the authorization of seven layers against seven receipt domains into a machine-checkable table, with outputs of receipt-less layers degrading automatically to unclaimable; the kernel contracts of the object definition landed on both the test and formalization sides, the formal side adding some twenty theorems, all entered into the axiom-audit list; retrieval, probability, comparison, behavior, and ontology each gained independent contracts and gate tests. All counts are bound by the generated artifact to named commits, and the build-run identifiers and outcomes per round appear in the table below.

<!-- S9-P04 -->
The conclusion returns to the reporting problem. What this paper offers is not an announcement that legal reasoning has been completely formalized but a checkable layered ledger: which distortions are impossible at the type level, which properties have genuine inductive proofs, which claims are forwardings, and which gaps stay in plain sight. Theories outside the trunk, unfilled implementation gaps, and the external ledger all exist with explicit statuses. For the system's users, the ledger means every report traces to its evidence grade; for further construction, it is itself the order of advance.

**Claims table for this section**

| Claim ID | Claim | Supporting object | Status | Boundary |
|---|---|---|---|---|
| S9-C01 | Unproved list and order of advance | Body of this section and the lists of the two preceding sections | Aggregated | The order is an engineering judgment, not unique |
| S9-C02 | Build-run identifiers and outcomes per round | Continuous-integration run records | See table | Cover only the bound commits |
| S9-C03 | Repository scale and registry scale | Static measurements of the generated artifact | Static measurement | Build passage rests with continuous integration |

| Round | Covered commits | Continuous-integration run | Outcome |
|---|---|---|---|
| Type registry expansion | 4836464..f4d46b0 | 36094524508 | All jobs succeeded |
| Receipt ledger and claims lists | c6d568c | 36095609565 | All jobs succeeded |
| Object contracts, local batch | 1a75437 | 36115235418 | All jobs succeeded |
| Contracts and formalization rounds | e4709ca..094ccb2 | 36117165469 | All jobs succeeded |
