# Legal Math Modeling Paper Corpus

This directory is a formula-centered research corpus derived from the machine-checked ULM01–ULM16 specification. It is not a set of release notes and does not treat repository build status as a legal conclusion.

## Evidence vocabulary

Every substantive proposition uses one of three labels:

- **FORMALIZED:** backed by a named Lean definition or theorem in `proofs/lean/juris_lean/JurisLean/`.
- **DERIVED:** follows from assumptions stated in the paper, but is not represented as a theorem in the repository.
- **CONJECTURE:** a legal, empirical, or mathematical extension that still needs proof or evaluation.

The labels are not truth scores. In particular, `FORMALIZED` does not mean that facts are true, an external implementation refines the model, or a legal judgment is correct.

## Manuscripts

| File | Role | Language | Formula target |
|---|---|---|---:|
| `main.md` | full master manuscript | English with Chinese abstract | 30+ |
| `main_cn.md` | full master counterpart | Chinese with English abstract | 30+ |
| `main.tex` + `sections/*.tex` | complete LaTeX master | English with Chinese abstract | 30+ |
| `icail_full_paper.md` | conference-length synthesis | English with Chinese abstract | 10+ |
| `mathematical_structures.md` | mathematical foundations | English with Chinese abstract | 10+ |
| `legal_reasoning_paradigms.md` | reasoning paradigms | English with Chinese abstract | 10+ |
| `argumentation_frameworks.md` | structured and abstract argumentation | English with Chinese abstract | 10+ |
| `non_monotonicity.md` | monotone support and non-monotone acceptance | English with Chinese abstract | 10+ |
| `argument_strength.md` | strength, trust, and defeat boundaries | English with Chinese abstract | 10+ |
| `probabilistic_legal_reasoning.md` | probabilistic extension boundary | English with Chinese abstract | 10+ |
| `dp_impossibility.md` | privacy-budget underdetermination | English with Chinese abstract | 10+ |
| `legal_analogy.md` | analogy under structural safeguards | English with Chinese abstract | 10+ |
| `graph_similarity_topology.md` | graph similarity counterexamples and metric preconditions | English with Chinese abstract | 10+ |
| `explainable_legal_reasoning.md` | traceability versus explanation quality | English with Chinese abstract | 10+ |
| `multi_ai_formalization.md` | multi-agent authority and taint | English with Chinese abstract | 10+ |
| `ai_liability_infrastructure.md` | assurance infrastructure for liability analysis | English with Chinese abstract | 10+ |

## Formal anchor map

The principal source sequence is:

1. `ULM01NormalForm.lean` — request identity and observation preservation.
2. `ULM02Outcome.lean` — complete, partial, and failed outcomes.
3. `ULM03TypedGraph.lean` — typed graph edges and request-preserving transitions.
4. `ULM04Obligations.lean` — mandatory obligations and sound verifier contracts.
5. `ULM05Machine.lean` — finite execution states.
6. `ULM06FactEvidence.lean` — admitted and assumed premise dependencies.
7. `ULM07HornSupport.lean` — finite least Horn closure.
8. `ULM08ArgumentConstruction.lean` — structured arguments and frozen-carrier coverage.
9. `ULM09AttackDefeat.lean` — typed attacks and policy-resolved defeats.
10. `ULM10DungProfiles.lean` — grounded, complete, preferred, and stable semantics.
11. `ULM11BranchQuery.lean` — skeptical/credulous queries and branch-safe composition.
12. `ULM12Procedure.lean` — procedure-sensitive adjudication and authority gating.
13. `ULM13DomainCompositionExact.lean` — branch choices and dimension-indexed exact evaluation.
14. `ULM14CoverageTrust.lean` — open obligations, five-dimensional trust, and conservative assurance composition.
15. `ULM15IncrementalEmpiricalBanach.lean` — add-only incrementality, empirical attachments, and conditional contraction results.
16. `ULM16TheoryComposition.lean` — concrete normal-form composition instances, not a theorem that every external TheorySpec is refined.

Supporting formal files include `HornDefinitions.lean`, `FiniteMonotoneIteration.lean`, `HornFixedPoint.lean`, `WeightedSupNorm.lean`, `ContractionCondition.lean`, `TemporalKripke.lean`, `TemporalArithmetic.lean`, `TemporalApplicability.lean`, `ReceiptAuthority.lean`, `HumanResearchReceiptSpec.lean`, and `TaintNoninterference.lean`.

## Citation policy

`references.bib` is the shared source of bibliographic truth. Entries were checked against DOI resolvers, publisher records, official journal pages, or official EUR-Lex instruments. Markdown manuscripts cite keys as `[@Key]`; LaTeX uses the same keys through `\citep{Key}` or `\citet{Key}`. No manuscript may invent a citation absent from the BibTeX file.

## Verification boundary

The formal release audit and paper corpus answer different questions. The release pipeline binds build evidence, axiom audits, mutation results, refinement receipts, subject identity, certificate status, and an independent verifier to one commit. The papers interpret the proved invariants and state limitations. Readers must not infer a current certificate verdict merely from prose or from a green job icon; inspect the JSON artifacts for the named subject.

No local Lean, Elan, or Lake invocation is part of the paper-writing workflow. GitHub Actions remains the authoritative elaboration environment. Static paper checks cover word counts, displayed equations, bilingual abstracts, declaration sections, citation-key closure, prohibited warning markers, encoding, and LaTeX syntax or compilation when an already-installed engine is available.
