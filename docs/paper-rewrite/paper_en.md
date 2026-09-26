# The Seven-Layer Liability Architecture of Legal Formalization: A Verifiable Ledger of Layered Claims

**English mirror** (structure-isomorphic to paper_cn.md; the Chinese master leads)

**Status**: rewritten from scratch on the frozen Concept Master Genealogy (docs/master-plan/基线/法律概念总谱.md); the prior paper (broadcast-distortion / sixteen-module organization) is archived at docs/history/paper-v1-en.md.
**Evidence discipline**: every count and theorem claim binds to the generated artifact docs/formal-release/theorem_inventory_v3.json (current subject `1488685`) and to named CI runs. No anchor, no claim; a missing anchor is UNKNOWN, never PASS.

---

## Introduction: The Answer a Court Needs, the System Must State in One Sentence

The SPC Similar-Case Guideline (trial) has been in force since 31 July 2020, requiring search-and-explain for similar cases [SPCSimilarCaseGuideline2020]. On 27 February 2024 the SPC Case Database went live, turning similar-case retrieval into daily practice [SPCCaseDatabase2024]. Legal-AI research flourished accordingly [JiWeidong2024CalcLaw; DengJinting2021CalcLawMethods; BuitenEtAl2021], with argumentation frameworks, defeasible reasoning, and probabilistic models in ample supply [Dung1995; PrakkenSartor1997; ModgilPrakken2013; FentonNeilLagnado2013].

Yet the existing work shares one gap: **to what grade a system's conclusion is trustworthy — nobody says.** What the solver returns, which arguments the evaluator accepts, and which state is finally reported to the adjudicator: these three steps constitute the broadcast, and neither retrieval norms nor argumentation theory governs its correctness [BenchCapon2003; Horty2011]. The Chinese computational-law literature has long located the real junction at verifiability [DengJinting2021CalcLawMethods]; computational logic stocked the tools long ago [ClarkeEtAl1986; CousotCousot1977; Tarski1955]; and machine-learning explainability research concedes its outputs are advisory [RibeiroEtAl2016; GuidottiEtAl2018]. What is missing is not parts but the assembled machine — layered by legal semantics, each layer carrying its receipt.

This paper delivers the machine and its ledger of claims. Three deliverables:

1. **A seven-layer, two-cross-cut genealogy.** One hundred thirty-two legal concepts (P-001 through P-132), each with one definition, one number, one formalization target, filed into Concept (L0), Source of Law (L1), Elements (L2), Proof (L3), Discretion (L4), Computation Guarantee ((L5)), and Delivery (L6), plus two cross-cutting disciplines: Empirical Calibration (A) and Receipts (B). The genealogy is frozen; changes pass a three-gate lock.
2. **Theorem-level full coverage.** Of the 132 concepts, 57 anchor existing theorems and 75 are newly written this round — contract and Lean on both sides, 1,775 repository theorem declarations (bound to the inventory artifact), all verified by the CI authority, zero sorry.
3. **A receipt discipline.** Every layer's output carries a claimable grade: conclusive (certified), reference (advisory only), unclaimable (no basis). A receipt-less layer's output degrades to unclaimable automatically — a structural consequence of the machine-readable ledger and the type system, not a wording convention.

Chapters follow the layers: each states its conclusion first, then the theorems and evidence anchors, then what the layer cannot do. Skeptics may turn directly to Chapter 10's unproved list — we spare ourselves nothing.

---

## Chapter 1 Concept Layer (L0): 132 Households, Zero Unregistered

**Conclusion: the legal ontology stands on the first floor in its own name; swallowing it into any data pocket is prohibited.**

The concept layer is the vocabulary. Claim, limitation, elements, power, event — every later layer speaks in these words, so the vocabulary is pinned first. Ten concepts work here (P-001–P-010): concept definition [LegalMathModeling2026], concept-as-dataset, legal language, legal subject, the Hohfeld eight, relation state, context parameters, characterization, versioned concepts, the personal-information family.

**Theorems and anchors.** The Hohfeld algebra: opposite and correlative maps are both involutive and fixed-point-free — four theorems (Hohfeld.lean, opposite_involutive et al., axiom-audited). Relation state: the Relation type carries shared constraints (same loss, competing exclusion, joint reduction), and a non-constitutive adjudication cannot create a relation at the type level (LegalModelV2.lean, relation_shared_constraints_participate). Versioned concepts: registration versions strictly increase; violations are rejected (Genealogy/Part0.lean, namespace P009, strictly_increasing_version_enters).

**Boundary.** This layer only says what things are. Interpretation belongs to Chapter 5; the engineering registry (52 types) keeps its single authority in the manifest, not duplicated here.

---

## Chapter 2 Source-of-Law Layer (L1): Hierarchy Routing, and New-General-vs-Old-Special Answers UNKNOWN

**Conclusion: sources of law supply the foundation; hierarchy conflicts route, but that one conflict class must answer UNKNOWN.**

Twelve concepts (P-014–P-025): source typology, hierarchy rank, validity and provenance, retroactivity, version transition, precedent binding, jurisdiction, conflict rules and renvoi, public-policy override, applicable-law selection, cause-of-action routing, the jurisdiction axis.

**Theorems and anchors.** Three routing theorems (Genealogy/Part1.lean, P015): higher rank wins (lex_superior_left); same rank, same day, same nature returns none; **old-special versus new-general returns none** — the machine explicitly refuses to adjudicate, leaving the question to the empowered interpreter. This is discipline, not defect: one class of source conflicts is by law not for algorithms [Maher2001; AntoniouEtAl2001]. One-hop renvoi: a foreign law pointing back applies forum substantive law, and the chain cannot take a second hop in the function (P021, renvoi_back_uses_forum_and_terminates). Retroactivity: intertemporal rules land in the TemporalApplicability.lean theorem group.

**Boundary.** The typology of hierarchy itself remains an open target — a typology question, not a routing one.

---

## Chapter 3 Elements Layer (L2): Subsumption Is an Operator; a Claim Needs Its Chain

**Conclusion: characterize first, find law second; subsumption is an operator; an incomplete chain means no claim.**

Thirteen concepts (P-026–P-038) — where the handling judge's first move happens: what kind of dispute is this, what is disputed, how do the elements decompose.

**Theorems and anchors.** The claim (first of the four former gaps) closes at theorem level: **a claim is available if and only if its basis chain's elements are all satisfied; an unregistered basis returns UNKNOWN** (Genealogy/Part2.lean, P034, claim_available_complete_iff and unregistered_basis_unknown). The subsumption operator's completeness is contract-grade (ontology_v3, subsume); its general-induction Lean upgrade sits on the unproved list. Agency trichotomy: agency binds the principal, representation binds within scope, impersonation binds nobody absent ratification (P035, three theorems). Rules versus principles: rules are all-or-nothing, principles carry weight only (P063).

**Boundary.** General completeness of subsumption is a mathematical, not a legal, assertion; the legitimacy of analogical transfer belongs to Chapter 5's discretion.

---

## Chapter 4 Proof Layer (L3): Whose Burden, Who Benefits from UNKNOWN

**Conclusion: evidence moves the candidate set only, never the normative state; losing is not falsity; undetermined requires exhausting four rule families.**

Fourteen concepts (P-039–P-052). This layer concentrates clause 2 of the object definition: Truth is normative semantics, Judgment is evidential supportability, **a judgment of not-established does not force truth false** unless a norm says otherwise.

**Theorems and anchors.** The layering's Lean carrier: KernelV3.lean's three-valued judgment with the layering witness (judgment_notEstablished_does_not_force_truth_false). But-for causation: one missing counterfactual direction is UNKNOWN (P047, two_sided_but_for_true and one_side_missing_unknown). Evidentiary weight: the weakest of three factors caps the grade (P042). Filing deadline: late is barred absent good-cause extension (P049). Exclusion: a closed list; named means excluded (P050). **The free-evaluation boundary (second former gap) closes at theorem level**: the kernel supplies admissible inputs only, the act of evaluation lies outside — the output type has no judgment field at all (P051, boundary_inputs_complete and boundary_records_input_only).

**Boundary.** How the judge evaluates, this system never says. The positive record of the formalization boundary is itself the theorem — the honest limit, not an excuse.

---

## Chapter 5 Discretion Layer (L4): Interpretive Disputes Fight; Sentencing Computes on Two Tracks

**Conclusion: readings coexist, attack each other, and get pinned by precedent; the sentencing norm line and empirical line present separately, neither impersonating the other.**

Thirty-eight concepts (P-053–P-090), the largest layer: defeasible argumentation [Dung1995; PrakkenSartor1997; ModgilPrakken2013], exceptions and exemptions, analogy and distinguishing [RisslandAshley1987; VlekEtAl2015], the five interpretation constructors, value preorders (total order refused), imputation principles, liability forms, and the full behaviorist family (negotiation, settlement, litigation strategy, judicial pressure).

**Theorems and anchors.** Interpretation branches isolate before evaluating (P060, isolated_branch_preserved): five methods evaluate independently, comparison only after — no rigged benches. Interpretive dispute: a pinned reading is immune to attacks of no higher precedence (P061). Gap signals (third former gap) close at theorem level: detection preserves the signal roster, and the output has no continuation slot (P066). Value preorder: incomparability is a legal output (P064) — when two positions cannot be ordered, the system says INCOMPARABLE, it does not force an order. Dual-track sentencing (P071/P072/P101): the norm line is deterministic rule-table execution, the empirical line a certified interval; the tracks merge only at the declaration step. Negotiation pieces: ZOPA existence (P076), monotone concession ladders (P077), the mediation zone (P078), settlement expected values (P079). Game equilibrium: explicitly labeled conflict-free-filter semantics, never impersonating Nash.

**Boundary.** The empirical sentencing line stays reference-grade forever; substantive interpretive weighing belongs to prose, not theorems; script assets only pass the never-masquerade check (P107).

---

## Chapter 6 Computation-Guarantee Layer ((L5)): What the Machine Does Unattended Wears Parentheses

**Conclusion: amounts compute exactly, deadlines compute on calendars, probability comes only from retrieved populations; the parenthesized layer is the machine's unattended execution surface, not a human station.**

Thirteen concepts (P-091–P-103). Guarantees for the whole stack: ExactExpr evaluation consistency, RoundingPolicy, ladder constructors, segmented interest, allocation conservation, progressive tax brackets, delay interest, consent-locked contract states.

**Theorems and anchors.** Allocation conservation (P097): an underfunded single debt applies the whole payment, an overfunded one carries the remainder; the two-debt witness reads 10 = 6 + 4 + 0. Penalty reduction (fourth former gap) closes at theorem level: six clamp theorems — below-band clamps to low, above-band to high, in-band fixed points, in-band idempotence (P098, the full set). Three-bracket progressive tax: each bracket taxes only its slice (P099, two witnesses). Smart contracts: no consent, no transition; no edge, no transition (P103, three theorems). The one-way logic-probability bridge (P114): deduction implies probability one; probability one does not imply deduction — the reverse theorem says false outright.

**Boundary.** All numerics ride Nat/exact rationals, floats banned; real rates and exchange rates are external parameters whose correctness this layer's theorems do not endorse.

---

## Chapter 7 Delivery Layer (L6): What Reaches a Human Hand Passes a Human Gate

**Conclusion: procedure flows along legal edges, effect logs are idempotent, listed actions pass their human gates — the machine hands over the knife; a human signs.**

Four concepts (P-104–P-107). The smallest layer, and the only one facing the user.

**Theorems and anchors.** Disposition sequences: file→answer→cross-examine→dismiss/suspend/terminate, a closed legal-edge table (P105, valid_path and invalid_jump). Litigation-subject identity: same cause plus same unordered parties (P106). Script assets: containing legal-fact assertions means rejection (P107).

**Boundary.** Delivery verifies non-masquerade, not correctness — doctrinal quality is supplied by Chapter 5; this layer only governs the shipping discipline.

---

## Chapter 8 Cross-Cutting A (Empirical Calibration): Retrieval Defines the Population, Then There Is Win Rate

**Conclusion: no population, no probability; the population must be really computed from retrieval; synthetic data stays permanently hard-marked.**

Eleven concepts (P-108–P-118). Two-layer retrieval: vector recall yields candidates only, structural comparison checks exactly [QiXiaodan2025SimilarCaseSearch for the Chinese practice background]; the win-rate pipeline in three steps: retrieval defines the population → the population computes the frequency → the case at hand compares [FentonNeilBerger2016 for the Bayesian legal-evidence frame]; three-reference deviation and stratified tendency; **the certificate-forced approximator (military-grade)**.

**Theorems and anchors.** Recall never impersonates isomorphism (P108/P109). Direction and flip witnesses (P110/P111): reverse without witness carries no attack witness. The win-rate pipeline (P112/P113): five-element event definition with unidentifiable-hard-coded UNKNOWN. The certificate-forced approximator (P118): proof-carrying admission — q below one, error bound within tolerance, nonempty applicable domain, positive iteration count all become constructor-time proof obligations; no certificate, no admission (five theorems, BanachCertificateV3) [Banach1922 for the fixed-point original].

**Boundary.** Empirical output stays reference-grade; a win rate is model-relative posterior mass, never a guarantee of case outcomes; text-similarity tools cap at candidate grade (P117).

---

## Chapter 9 Cross-Cutting B (Receipts): A Layer Without a Receipt Has No Right to Speak

**Conclusion: the seven-layer × seven-domain authorization table is machine-readable; receipt-less layers degrade to unclaimable automatically; the claims lists are machine-read with drift gates.**

Fourteen concepts (P-119–P-132). The receipt is the receipt discipline running through the genealogy: who issued, on what basis, to what grade claimable.

**Theorems and anchors.** UNKNOWN preservation and the three-gate admission (P119/P120, existing theorem groups). Anti-hallucination: named patterns block (P125). Anti-smuggling: cross-jurisdiction without adaptation blocks (P126). Citation verification: verbatim prefix comparison (P127, degradation note: prefix, not arbitrary substring, honestly recorded). Due-process mapping of three elements (P128). Lifecycle edge table (P130). Idempotent effect log (P131, empty-log replay idempotence plus the existing-command no-overwrite witness). The human-gate table (P132): listed actions pass exactly their gate.

**Boundary.** Receipts prove binding, not truth; forty-one of the forty-nine authorization cells start NO_RECEIPT_PENDING — conservative start is discipline, not defect.

---

## Chapter 10 The Unproved List and the Claims Ledger: What We Have Not Proved

**Conclusion: a verifiable machine must also deliver the list of what it cannot do; whoever withholds that list is the untrustworthy one.}

**Unproved items (re-ranked after the round-9 compaction)**:
1. ~~T01–T127 theorem-level rollout~~ — **compacted in round ten**: four batches delivered 131 theorems (Batch1..4, all CI-green), the coverage ledger reports 127/127 COVERED;
2. ~~P-083 global descending-correctness of the sort~~ — **compacted this round**: the full general chain of four insertion-sort theorems now lands (GENERAL-A single insert adds one / GENERAL-B length conservation / GENERAL-C insertion preserves descending / GENERAL-D sort output always descending, General.lean, CI run 36258901155 at commit bd364c5 all green); the previously authorized witness-level half-step is thereby closed;
3. Sentencing rule-table slot (DATA_SLOT_READY): the structure is jurisdiction-agnostic and ready — any jurisdiction's real rule table plugs in (the synthetic table already proved structural correctness; real data is data, not architecture, and binding to one province would lock the general structure);
4. Subsumption completeness, the eight degradations, and the six boundary-delimitation theorems — **compacted in round nine**: 25 new theorems (General.lean + Boundary.lean, CI-verified); the P-127 left-prepend claim is closed by a minimal counterexample on record with the corrected right-append theorem proved; boundary classes 5/6 are pointer-compacted (consensus_does_not_escalate / repetition_does_not_clean / majority_cannot_clean);
5. Retrieval layer-one vector engine — **compacted in round nine**: a deterministic TF-IDF cosine engine now lives in the repo (vector_engine.py, 8 gate tests: normalization invariance, self-similarity, symmetry, deterministic ranking, candidate-grade cap), zero-dependency pure Python.

**Claims ledger**: 1,775 repository theorem declarations, bound to the inventory artifact (subject in the header), axiom audit green (named CI runs). This paper does not claim: the entirety of Chinese law formalized; approximator outputs conclusive; the T spectrum closed. Every conclusion a user sees traces through its receipt to its evidence grade; for further construction, the T-coverage ledger is itself the order of advance.
