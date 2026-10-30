# U01.4 finite-obligation audit

## Frozen scope and evidence

The archived `U01.4` residual is copied verbatim into `verification.json` from the pinned `scope-archive.json`. This package supplies independent changed-module evidence for the finite witnesses named by that residual; it does not assert that real data follow the bad mechanism.

The finite Boolean construction uses `pointWeight_is_probability` and `pointPopulationRisk_eq` to establish the point-mass risk calculation, and `actualConstantFit_value` identifies the output of the actual constant fit. Instantiate `pointPopulationRisk_eq` and `actualConstantFit_value` at the same visible point `false`, with label `fun _ => false`, truth `fun _ => true`, and hypothesis `actualConstantFit false`: label risk is 0 and truth risk is 1. For `allowed(action) := action = true`, the same finite set has the witness `action = true`, while the actual fit output `false` is not allowed. The opposite-label `u01_6_perfect_fit_does_not_supply_authorization` witness retains its separate purpose: perfect fit does not imply permission. Its different label encoding does not conflict with the direct literal witness. The existing `LearningERM20261027.u01_1_actual_empirical_fit_minimizes` theorem supplies the nonempty finite empirical-fit minimization contract as context; this package adds no duplicate minimization theorem or production Fit/provenance claim.

For the source/deployment split, `u01_3_actual_fit_zero_train_one_deploy` uses target `id`; `pointWeight false` is the source point mass and `pointWeight true` is the deployment point mass, with fitted hypothesis `actualConstantFit false`, giving source risk 0 and deployment risk 1. The two-world theorem proves that, for every finite `n` and every deterministic learner, the same visible training data can be paired with different targets, with a target world attaining deployment risk 1. The “any training data” scope is limited to finite samples generated from the stated source measure.

The dependence witnesses cover three explicit models: independent fair Bernoulli observations with variance `1/(4n)`, copied observations with variance `1/4`, and a concrete common-cause model with distinct event identifiers but no independence when `n > 1`. Distinct IDs therefore do not imply iid. The checked `grouped_unit_not_split` declaration says a single-valued split map cannot assign two different groups to the same unit; it does not establish iid, exclude future leakage, or remove source bias. The existing finite fair-coin measure is reused; no new probability model or theorem is introduced.

## Original-question mapping

The evidence maps only the U01.4 finite subclaims that overlap the indicated rows:

- 01.1: the finite label/truth, zero-label-risk / unit-truth-risk at the same point witness. The row remains partial.
- 01.3: the independent-versus-copied/common-cause variance models and identifier counterexample. The row remains partial.
- 01.5: the source/deployment point-mass construction and finite same-training / different-target worlds. The row remains partial.
- 04.2: the independent/copy/common-cause variance subclaim only. A variance calculation is not a likelihood theorem and does not settle the `θ` versus `θ^10` likelihood distinction; that is tracked against its separate evidence. The row becomes partial, not covered.

The distinct original 01.4 representation-error question, other requirements in these rows, and all 15 consumer edges are unchanged. The package does not claim actual data follow the bad mechanism, universal empirical truth, source authenticity, legal permission, or deployment acceptance. It changes no actual consumer call edge.

## Independent changed-module audit

The ten theorem targets and five object checks were audited by changed-module run `41081311144`, attempt 1, job `124150886815`, against subject `f80e790e6d6ecbd8449f2181433673945540e5af` and tree `21de998db857fc5cbd642a198a8a11b5fb25483b`. Nine theorem targets have only the standard `propext`, `Classical.choice`, and `Quot.sound` axioms; `grouped_unit_not_split` is axiom-free. The artifact and the seven bound source files are listed in `verification.json`; the original 25 raw output blocks are retained in `axiom-audit.raw.txt`.

This is independent source/module evidence only. It does not represent PR, full-release, merge, real-data, legal-correctness, or whole-theory acceptance.
