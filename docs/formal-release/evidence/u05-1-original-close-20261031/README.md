# U05.1 exchangeable rank and marginal conformal coverage close

## Frozen scope

The exact archived U05.1 residual is kept verbatim in `verification.json`; neither the frozen scope archive nor the tip pin is changed. The archived exact scope concerns a fixed scoring rule after training, exchangeability of the calibration and test scores conditional on training, the threshold `k = ceil((n+1)(1−α))`, and marginal coverage. It explicitly distinguishes marginal coverage from group or pointwise coverage and notes deployment shift as a failure boundary. The historical residual mentions a continuous tie-break as an assumption and references an older run; the new proof constructs the tie-break and its uniform rank law under the stated independent continuous auxiliary model.

## Audited declarations

`rank_order_statistic_core` proves the deterministic finite ranking and order-statistic implication while retaining tied calibration scores as separate indices. `iid_auxiliary_rank_prefix` constructs an independent IID continuous auxiliary vector and derives the actual rank-prefix probability `k/(n+1)` from exchangeability of the score vector; score exchangeability is the premise, not IID scores. `exchangeable_split_conformal_coverage` gives the finite-branch threshold and the `k > n` top branch for fixed training, `n ≥ 1`, and `0 < α < 1`. `scored_sample_split_conformal_coverage` transports the result to a fixed measurable score. The guarantee is marginal under the declared law; it is not group-conditional, pointwise, or a deployment-shift guarantee.

`finite_group_and_deployment_boundaries` supplies the finite counterexamples named by the U05.1 scope. In the source model with an independent Bernoulli(1/4) group indicator, marginal coverage is `13/16` while coverage conditional on the rare test group is `1/4`. In the deployment model, calibration retains its source law while the test group is always true; coverage is `1/4` and exchangeability fails. These examples demonstrate the boundary of the marginal theorem; they do not assert a universal shift theorem or supply a group-conditional calibration method.

## Original-question mapping

Original-question 05.4 L111 is covered by the actual exchangeable score-vector theorem and the constructed independent continuous tie-breaking auxiliary, which yields uniform finite rank prefixes. L113 is covered by the retained-multiplicity calibration order statistic, the non-strict coverage implication, `k = ceil((n+1)(1−α))`, and the explicit infinite-threshold branch. L115 receives the finite marginal-versus-group counterexample and the deployment-shift example. The original request for a group-conditional sufficient version is not claimed: the archived U05.1 exact scope states the marginal guarantee and its group/deployment boundary, and this close does not add arbitrary subgroup guarantees or a new calibration procedure.

The run also gives negative support for the distribution-change boundary in original-question 05.5 L123: changing the test law can invalidate the calibration coverage guarantee. It does not resolve the exact covariate-shift identity and density-ratio error analysis at L119, the unseen-input label nonidentification at L121, or a general concept-shift detector. Original-question 05.5 remains unreconciled.

## Original-question 01 mapping

The six finite model-card questions 01.1–01.6 are now marked `COVERED` only within their written finite contracts and explicit assumptions. The row-level `paragraph_evidence` entries identify each paragraph, its named source declarations, and the quantifier boundaries. In particular: label `Y`, fact `T`, legal relation `R`, and norm `N` remain distinct; the fixed finite class and IID evaluation premise are not expanded to adaptive or infinite search; event grouping prevents same-event leakage but does not create independence; risk decomposition and sufficient representations are stated over the fixed classes; TV transfer requires a known joint source/target bound for the same loss; and the finite model card does not imply calibration, legal authorization, or real-world validity. This is not a claim that the 105 engineering requirements, 15 consumer edges, six designated cuts, or whole theory are complete.

## Independent changed-module audit

Five theorem targets and three object types were audited by run `41134518610`, attempt 1, job `124333547346`, against subject `89a5ec8a3e1180ee072c20fc91a3026f498893e5` and tree `deb761a55294eb6d695a05916cfce68241d96980`. Each target uses exactly `propext`, `Classical.choice`, and `Quot.sound`; the artifact and two source-file hashes are bound in `verification.json`. The 13 raw blocks are extracted from this run's `changed-module.log`, limited to the named audit driver.

This is source/module evidence only, not PR/full-release/merge acceptance, consumer-edge wiring, real-data validation, legal correctness, or whole-theory completion. Global archived-gap discharges, Step 2, and `math_flip` remain false.
