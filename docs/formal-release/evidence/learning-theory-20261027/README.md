# Original U01 theory: bounded-risk and learning proof batch

The original v003 main text, sections U01.1-U01.3, requires a population risk
decomposition, the actual iid sample-mean radius, data-selected approximate ERM,
a same-loss label bridge with joint failure budgets, and a joint-law deployment
bound. These are implemented in LearningRisk20261027, LearningFiniteClass20261027
and LearningBridge20261027. All populations, losses, classes and assumptions stay
explicit; no theorem certifies the truth or lawfulness of real labels.

[Authority module run 40369446453, job 121735932469](https://github.com/laubeing-droid/legal-math-modeling/actions/runs/40369446453/job/121735932469)
built the independent LearningTheoryAudit20261027 driver at
`c265e254ecc45565642dd087ad8a095fc47ede5a`. It checks fourteen complete theorem
types and prints their kernel axioms. The adjacent raw text contains that
driver's output, without dependency-installation or unrelated build output.
All fourteen use only propext, Classical.choice and Quot.sound.

The certificate is module evidence. Root entry and final-branch acceptance
require the later full ULM and Authority checks. It does not claim that every
U01 subclaim or actual pipeline consumer has been completed. In particular,
the original probabilistic copy/common-cause models and downstream task,
measurement, calibration and decision consumers remain separate obligations.

The same proof branch also carries the actual Horn closure finite-fuel and
robust-query module CompilerClosure20261026, previously built successfully in
[module run 40356182317, job 121689192880](https://github.com/laubeing-droid/legal-math-modeling/actions/runs/40356182317/job/121689192880).
That module is byte-identical to its tested subject `2646bdd3`; its provenance
DAG completeness and original composition obligations are not replaced by a
closure theorem.

No frozen Final20261021 sources, CAND8 eight-name scope, PROVE_CANDIDATES, tip pin
or archive-debt disposition is changed by this batch. OPEN remains 20 and
closes_debt=false. Import reachability is build coverage, not actual theorem or
runtime consumption.
