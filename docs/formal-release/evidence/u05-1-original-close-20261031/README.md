# U05.1 exchangeable rank and marginal conformal coverage close

## Frozen scope

The exact archived U05.1 residual is kept verbatim in `verification.json`; neither the frozen scope archive nor the tip pin is changed. The archived exact scope concerns a fixed scoring rule after training, exchangeability of the calibration and test scores conditional on training, the threshold `k = ceil((n+1)(1−α))`, and marginal coverage. It explicitly distinguishes marginal coverage from group or pointwise coverage and notes deployment shift as a failure boundary. The historical residual mentions a continuous tie-break as an assumption and references an older run; the new proof constructs the tie-break and its uniform rank law under the stated independent continuous auxiliary model.

## Audited declarations

`rank_order_statistic_core` proves the deterministic finite ranking and order-statistic implication while retaining tied calibration scores as separate indices. `iid_auxiliary_rank_prefix` constructs an independent IID continuous auxiliary vector and derives the actual rank-prefix probability `k/(n+1)` from exchangeability of the score vector; score exchangeability is the premise, not IID scores. `exchangeable_split_conformal_coverage` gives the finite-branch threshold and the `k > n` top branch for fixed scoring after training, `n ≥ 1`, and `0 < α < 1`. `scored_sample_split_conformal_coverage` transports the result to a fixed measurable score. Those results give marginal coverage under the declared law. The supplementary `group_conditional_split_conformal_coverage` theorem is a distinct conditional-law instance for one stated test group under the explicit premises below; it does not assert pointwise coverage or a deployment-shift guarantee.

`finite_group_and_deployment_boundaries` supplies the finite source and deployment counterexamples: marginal coverage is `13/16` while rare-group conditional coverage is `1/4`; when calibration retains its source law and the test group is always true, coverage is `1/4` and exchangeability fails. They identify when the marginal theorem does not yield a conditional guarantee. The supplementary theorem supplies a group-conditional sufficient version only under its actual conditional-law premises; neither result is a universal shift theorem.

## Group-conditional assumption checklist

`group_conditional_split_conformal_coverage` applies the existing fixed-score theorem under the actual conditional measure of the test-group event `A_g = {ω | group (X ω (Fin.last n)) = g}`. The statement requires `A_g` to be measurable and have positive mass, and it returns a probability bound under `cond μ A_g`. For this fixed group, `n` is its calibration count `n_g` and must satisfy `n_g ≥ 1`; the calibration entries are in the same group almost surely under `cond μ A_g`. The full calibration-plus-test vector must satisfy permutation exchangeability under that same conditional measure. Measurability and group membership alone do not establish this exchangeability premise.

The score function is fixed for the statement, and `0 < α < 1`. The actual threshold uses `k_g = ceil((n_g+1)(1−α))`: when `k_g ≤ n_g`, the finite calibration order statistic gives the coverage bound; when `k_g > n_g`, the existing top branch returns the infinite threshold. A requested finite threshold therefore needs `k_g ≤ n_g`. The auxiliary tie handling is constructed by the reused theorem and its independent continuous law; it is not an assumed uniform-rank premise.

The group map and g are fixed for this evaluation and conditioning. This is a conditional guarantee for the specified positive-mass group and conditional law, not a pointwise-in-x guarantee, a legal-branch guarantee, or a guarantee for arbitrary fine subdivisions. Each further subgroup must independently satisfy the measurable positive-mass, calibration membership, count, and actual conditional exchangeability premises. An unknown group or missing calibration sample does not turn into a false or automatic coverage guarantee.

## Original-question mapping

Original-question 05.4 L111 is covered by the actual exchangeable score-vector theorem and the constructed independent continuous tie-breaking auxiliary, which yields uniform finite rank prefixes. L113 is covered by the retained-multiplicity calibration order statistic, the non-strict coverage implication, `k = ceil((n+1)(1−α))`, and the explicit infinite-threshold branch. For L115, the finite marginal-versus-group and deployment examples remain boundary witnesses, and the new `group_conditional_split_conformal_coverage` supplies the requested sufficient group-conditional version under the assumptions in the checklist. This additional L115 evidence supplements the archived U05.1 marginal scope; it does not change that archived residual.

The run also gives negative support for the distribution-change boundary in original-question 05.5 L123: changing the test law can invalidate the calibration coverage guarantee. It does not resolve the exact covariate-shift identity and density-ratio error analysis at L119, the unseen-input label nonidentification at L121, or a general concept-shift detector. Original-question 05.5 remains unreconciled.

## Original-question 01 mapping

The six finite model-card questions 01.1–01.6 are now marked `COVERED` only within their written finite contracts and explicit assumptions. The row-level `paragraph_evidence` entries identify each paragraph, its named source declarations, and the quantifier boundaries. In particular: label `Y`, fact `T`, legal relation `R`, and norm `N` remain distinct; the fixed finite class and IID evaluation premise are not expanded to adaptive or infinite search; event grouping prevents same-event leakage but does not create independence; risk decomposition and sufficient representations are stated over the fixed classes; TV transfer requires a known joint source/target bound for the same loss; and the finite model card does not imply calibration, legal authorization, or real-world validity. This is not a claim that the 105 engineering requirements, 15 consumer edges, six designated cuts, or whole theory are complete.

## Independent changed-module audit

Six theorem targets and three object types were audited by run `41163534485`, attempt 1, job `124426094626`, against subject `72135485cb4cbba15ec3e2bdd0183d99d05e9947` and tree `ff6132ec279f6f9d020e455d4b0f11a44f054578`. Each target uses exactly `propext`, `Classical.choice`, and `Quot.sound`; the artifact and three source-file hashes are bound in `verification.json`. The 15 raw blocks are extracted from this run's `changed-module.log`, limited to the named audit driver.

This is source/module evidence only, not PR/full-release/merge acceptance, consumer-edge wiring, real-data validation, legal correctness, or whole-theory completion. Global archived-gap discharges, Step 2, and `math_flip` remain false.
