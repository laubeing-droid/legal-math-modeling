# Evidence-Calibrated Trust Labels as AI Liability Infrastructure

**Author:** Legal Math Modeling Research Group

**Keywords:** AI liability, trust labels, evidence calibration, responsibility attribution, formal verification, legal AI governance

---

## Abstract

Current AI liability frameworks -- including the EU AI Act (2024) and proposed US algorithmic accountability legislation -- lack fine-grained mechanisms for attributing responsibility when AI systems produce incorrect or unverified outputs. We introduce a formal model of *evidence-calibrated trust labels* as liability infrastructure. Each AI-generated claim is assigned one of seven evidence statuses (PROVED, REFUTED, PARTIAL, DATA_INSUFFICIENT, TOY_SYNTHETIC, PENDING_TOOLCHAIN, ENGINEERING_BASELINE), and we prove that this labeling induces a unique responsibility attribution over every claim. The system satisfies audit completeness: every claim's provenance is fully traceable from assertion to evidence. We formalize liability transfer conditions for PROVED and REFUTED claims and establish engineering constraints that prevent unverified assertions from propagating to downstream decisions.

---

## 1. Introduction

The rapid deployment of AI systems in high-stakes domains -- medical diagnosis, legal reasoning, financial advising, autonomous vehicles -- has outpaced the development of liability frameworks capable of assigning responsibility when these systems err. The EU AI Act (Regulation 2024/1689) introduces a risk-based classification (unacceptable, high, limited, minimal) but treats each *system* as a monolithic risk unit, ignoring the heterogeneous evidence quality of individual outputs. Proposed US legislation (e.g., the Algorithmic Accountability Act) similarly focuses on system-level impact assessments rather than claim-level evidentiary calibration.

This granularity gap creates a critical problem: when an AI system produces 1,000 claims, some may be rigorously verified while others are speculative, yet under current frameworks the entire system receives a single risk designation. A claim backed by formal proof and a claim produced by ungrounded pattern matching are treated identically for liability purposes.

We address this gap by formalizing the *evidence-calibrated trust label system* as AI liability infrastructure. Drawing on the 7-level trust label schema developed for cross-jurisdictional legal reasoning verification [1], we prove that the labeling induces a well-defined responsibility attribution function, establish liability transfer conditions, and demonstrate audit completeness. Our approach transforms trust labels from a software engineering artifact into a legal instrument for fine-grained liability assignment.

---

## 2. Definitions

**Definition 1 (AI Claim).** An *AI claim* is any assertion $\varphi$ produced by an AI system $\mathcal{S}$, together with its generation context $C = (\mathcal{S}, t, I, M)$ where $t$ is the timestamp, $I$ is the input context, and $M$ is the model configuration. Formally, a claim is a tuple $\langle \varphi, C, \sigma \rangle$ where $\sigma$ is the initial confidence score assigned by $\mathcal{S}$.

**Definition 2 (Evidence Status).** The *evidence status* function $\varepsilon: \Phi \to \mathcal{L}_7$ maps each claim to one of seven trust label levels, ordered by evidentiary strength:

$$\mathcal{L}_7 = \{\texttt{PROVED},\; \texttt{REFUTED},\; \texttt{PARTIAL},\; \texttt{DATA\_INSUFFICIENT},\; \texttt{TOY\_SYNTHETIC},\; \texttt{PENDING\_TOOLCHAIN},\; \texttt{ENGINEERING\_BASELINE}\}$$

with the partial order $\texttt{PROVED} > \texttt{REFUTED} > \texttt{PARTIAL} > \{\texttt{DATA\_INSUFFICIENT}, \texttt{TOY\_SYNTHETIC}\} > \texttt{PENDING\_TOOLCHAIN} > \texttt{ENGINEERING\_BASELINE}$. Note that $\texttt{REFUTED}$ ranks above $\texttt{PARTIAL}$ because a refutation is *definitive*, while a partial proof leaves truth value uncertain.

**Definition 3 (Liability Chain).** A *liability chain* for claim $\varphi$ is a directed sequence $\lambda(\varphi) = (a_1, a_2, \ldots, a_n)$ where each $a_i$ is an agent (AI system or human) that contributed to producing, verifying, or endorsing $\varphi$. The chain is equipped with an attribution function $\alpha: \{1, \ldots, n\} \to \mathcal{L}_7$ mapping each agent's contribution to the evidence status it warrants.

**Definition 4 (Responsibility Attribution).** The *responsibility attribution function* $\rho: \Phi \times \mathcal{L}_7 \to \mathcal{A}$ maps each claim-evidence pair to a responsible party $\rho(\varphi, \varepsilon(\varphi)) \in \mathcal{A}$, where $\mathcal{A}$ is the set of all agents. For a liability chain $\lambda(\varphi) = (a_1, \ldots, a_n)$ with refutation timestamp $t_{\text{ref}}$, the responsible party is determined by the evidence status:

$$\rho(\varphi, \varepsilon(\varphi)) = \begin{cases} a_{\text{verifier}} & \text{if } \varepsilon(\varphi) = \texttt{PROVED} \\ a^* & \text{if } \varepsilon(\varphi) = \texttt{REFUTED} \\ a_{\text{last}} & \text{if } \varepsilon(\varphi) \in \{\texttt{PARTIAL}, \texttt{DATA\_INSUFFICIENT}, \texttt{TOY\_SYNTHETIC}\} \\ \text{none} & \text{if } \varepsilon(\varphi) = \texttt{PENDING\_TOOLCHAIN} \\ a_{\text{deployer}} & \text{if } \varepsilon(\varphi) = \texttt{ENGINEERING\_BASELINE} \end{cases}$$

where $a^* = \arg\max_{a_i \in \lambda(\varphi)} \{t_{a_i} : t_{a_i} > t_{\text{ref}}\}$ is the last agent to assert $\varphi$ after refutation (or $\text{none}$ if no agent asserts after $t_{\text{ref}}$). This ensures that liability for a refuted claim falls on the party that persisted in asserting it despite available counter-evidence.

---

## 3. Main Results

**Theorem 1 (Unique Responsibility Attribution).** Under the trust label system with a well-defined labeling procedure $\varepsilon: \Phi \to \mathcal{L}_7$ (as enforced by the schema in `trust_label_schema.json`), every claim $\varphi \in \Phi$ has a unique responsibility attribution $\rho(\varphi, \varepsilon(\varphi))$.

*Proof.* The labeling procedure is an engineering implementation (not a mathematical theorem); we assume it satisfies the schema constraint that exactly one label is assigned per claim (enforced by mutual exclusivity of the 7 status values in the `EvidenceStatus` enum). Given this assumption, $\varepsilon(\varphi)$ is unique for each $\varphi$. The responsibility attribution function $\rho$ (Definition 4) is a deterministic case analysis on $\varepsilon(\varphi)$, returning exactly one agent per case. Since $\varepsilon$ is a function and $\rho$ is a function, the composition $\rho(\cdot, \varepsilon(\cdot))$ is a function from $\Phi$ to $\mathcal{A}$. Therefore every claim has exactly one responsible party. $\square$

**Theorem 2 (PROVED Liability Transfer).** If $\varepsilon(\varphi) = \texttt{PROVED}$ and the proof is verified by an automated checker $V$ (e.g., SMT solver, theorem prover, exhaustive enumerator), then liability for the truth of $\varphi$ transfers from the AI system $\mathcal{S}$ that generated $\varphi$ to the verification infrastructure $\mathcal{V} = (V, \text{toolchain}, \text{artifact})$.

*Proof.* Let $\varphi$ be a claim with $\varepsilon(\varphi) = \texttt{PROVED}$. By Definition 2, PROVED status requires a machine-checkable proof artifact $\pi$ and a verification command $c$ such that executing $c$ on $\pi$ yields acceptance. The liability chain is $\lambda(\varphi) = (\mathcal{S}, V)$. Since $V$ independently confirms $\varphi$ through a reproducible artifact, the evidentiary basis for $\varphi$ rests entirely on $\mathcal{V}$, not on $\mathcal{S}$'s initial assertion. The AI system $\mathcal{S}$ contributed the *conjecture*; the verification infrastructure $\mathcal{V}$ established the *truth*. Liability attaches to the party that established truth, hence $\rho(\varphi, \texttt{PROVED}) = V$. If $\varphi$ is subsequently found to be false (e.g., due to a checker bug), liability falls on the toolchain maintainers, not on $\mathcal{S}$. $\square$

**Theorem 3 (REFUTED Liability Transfer).** If $\varepsilon(\varphi) = \texttt{REFUTED}$ and agent $a^*$ asserts or deploys $\varphi$ despite the refutation, then liability for any harm caused by reliance on $\varphi$ transfers to $a^*$.

*Proof.* Let $\varphi$ be a claim with $\varepsilon(\varphi) = \texttt{REFUTED}$. By Definition 2, REFUTED status requires a concrete counterexample $\bar{w}$ and a reproducible refutation command. The truth value of $\varphi$ is established as *false*. Consider the liability chain $\lambda(\varphi) = (a_1, \ldots, a^*, \ldots, a_n)$. For any agent $a_i$ that asserts $\varphi$ after the refutation timestamp $t_{\text{ref}}$, the assertion constitutes a failure to exercise reasonable care: the counterexample is publicly available and machine-reproducible. Therefore $\rho(\varphi, \texttt{REFUTED}) = a^*$ where $a^* = \arg\max_{a_i} \{t_{a_i} : t_{a_i} > t_{\text{ref}}\}$ is the last agent to assert $\varphi$ after refutation. If no agent asserts $\varphi$ after refutation, no liability attaches (the system correctly rejected the false claim). $\square$

**Proposition 1 (Audit Completeness).** The trust label system satisfies *audit completeness*: for every claim $\varphi$, the tuple $(\varphi, \varepsilon(\varphi), \lambda(\varphi), \rho(\varphi, \varepsilon(\varphi)))$ is fully determined and traceable.

*Proof.* By the schema definition, each evidence status requires specific fields: artifact path, checker command, assumptions, and limitations. The liability chain is constructed at claim creation time. The responsibility attribution is computed deterministically (Theorem 1). Therefore the full provenance -- from assertion to evidence to responsible party -- is reconstructible for any claim. No claim can exist in the system without an evidence status (the schema mandates assignment), and no evidence status can exist without supporting metadata (the schema mandates required fields). $\square$

---

## 4. Engineering Implications

Deploying trust labels as liability infrastructure in production systems requires three engineering commitments:

**Mandatory Status Assignment.** No AI-generated claim may propagate downstream without an evidence status. Claims entering the system without verification receive $\texttt{ENGINEERING\_BASELINE}$ by default, carrying the `synthetic_guard` flag that prevents their use in consequential decisions.

**Status Transition Logging.** Every transition between evidence statuses must be recorded with an immutable audit trail. The valid transitions form a DAG:

$$\texttt{PENDING\_TOOLCHAIN} \to \{\texttt{PROVED}, \texttt{REFUTED}, \texttt{PARTIAL}\}$$
$$\texttt{PARTIAL} \to \{\texttt{PROVED}, \texttt{REFUTED}\}$$

Downward transitions (e.g., from $\texttt{PROVED}$ to $\texttt{REFUTED}$ upon discovery of a checker bug) are permitted and must trigger liability re-evaluation.

**Forbidden Tag Enforcement.** Certain tags must never appear in any downstream system: `FINAL_ALL_THEOREMS_PROVED`, `REAL_PRICING_VALIDATED`, `DP_EPSILON_LEGALLY_DETERMINED`, `ALL_SOURCES_OFFICIALLY_VERIFIED`. These represent epistemic overreach -- claims of certainty that exceed any possible evidence. The enforcement mechanism rejects any output containing these tags at the system boundary.

---

## 5. Comparison with Related Work

**Model Cards** (Mitchell et al., 2019) document model-level properties (intended use, performance metrics, ethical considerations) but do not track individual claim evidence. A model card describes the *system*; trust labels describe each *output*.

**Datasheets for Datasets** (Gebru et al., 2021) provide dataset-level provenance but operate at training time, not inference time. They answer "where did the data come from?" but not "is this specific output correct?"

**EU AI Act Risk Classification** assigns systems to four risk tiers. This is a *regulatory* classification, not an *evidentiary* one. A high-risk AI system may produce some claims that are rigorously verified and others that are speculative; the Act's risk tier cannot distinguish them. Trust labels provide the missing claim-level granularity.

**NIST AI Risk Management Framework** (2023) recommends "contextual transparency" but provides no formal mechanism for tracking evidentiary status at the individual claim level. Our formalization fills this gap with a mathematically precise, machine-enforceable system.

The trust label system is complementary to all of the above: it operates at finer granularity (claim-level vs. system-level) and carries formal guarantees (Theorems 1--3, Proposition 1) that documentation-oriented approaches lack.

---

## 6. Conclusion

We have formalized evidence-calibrated trust labels as AI liability infrastructure, proving that the 7-level labeling system induces unique responsibility attribution (Theorem 1), establishes liability transfer conditions for PROVED (Theorem 2) and REFUTED (Theorem 3) claims, and satisfies audit completeness (Proposition 1). The framework transforms the trust label system from a software engineering verification artifact into a legal instrument for fine-grained liability assignment.

The key insight is that *evidence status determines liability*: a claim backed by a machine-checked proof carries different legal weight than a claim produced by pattern matching, and the liability framework must reflect this difference. Current regulatory approaches that classify entire AI systems into monolithic risk tiers cannot capture this heterogeneity. Trust labels fill the gap.

Future work includes: (1) formalizing the interaction between trust labels and jurisdiction-specific liability standards (strict liability vs. negligence); (2) extending the framework to multi-agent systems where liability chains span multiple AI providers; and (3) integrating trust labels with blockchain-based audit trails for tamper-evident provenance recording.

---

## References

[1] Legal Math Modeling Research Group. "A Formal Framework for Cross-Jurisdictional Symbolic Legal Reasoning." 2026. Evidence-calibrated trust label system with 7-level status schema.

[2] Regulation (EU) 2024/1689 of the European Parliament and of the Council (EU AI Act). Official Journal of the European Union, 2024.

[3] Mitchell, M. et al. "Model Cards for Model Reporting." *Proceedings of the Conference on Fairness, Accountability, and Transparency*, 2019.

[4] Gebru, T. et al. "Datasheets for Datasets." *Communications of the ACM*, 64(12):86--92, 2021.

[5] NIST. "Artificial Intelligence Risk Management Framework (AI RMF 1.0)." NIST AI 100-1, 2023.

[6] Dung, P.M. "On the Acceptability of Arguments and its Fundamental Role in Nonmonotonic Reasoning, Logic Programming and n-Person Games." *Artificial Intelligence*, 77(2):321--357, 1995.
