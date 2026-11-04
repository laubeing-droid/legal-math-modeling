# Original question 05.1 calibration — evidence package

This package records the named source result for frozen original-question 05.1, L87/L89/L91. The handoff row is marked COVERED at the math-row level from four new declarations plus five reused declarations under an independent changed-module CI run. Full-record PR acceptance remains pending.

## Frozen-clause mapping

- **L87 — actual score sigma-field.** `conditional_correct_score_is_calibrated` specializes the existing tower result to `MeasurableSpace.comap (score ∘ X)`, with the actual score in the a.e. `[0,1]` range and Bool outcome. It does not constrain unobserved inputs. The finite `fairBoolLaw` instance shows a constant score `1/2` is calibrated, while the full-input conditional expectation is the actual `0/1` label and is not a.e. `1/2`; calibration is weaker than conditional correctness.
- **L89 — normalization and calibration.** `normalized_rule_not_calibrated` fixes raw weights `(1,9)`, ignores training samples, and emits `9/(1+9)`, with both train and test law `fairBoolLaw`. The score lies in `[0,1]`, but its actual conditional expectation is `1/2`, so it is not calibrated. The existing equal-weight finite bucket/group counterexample remains a separate finite calculation; it is not a theorem equating arbitrary bucket predicates with conditional expectations. Softmax at temperature 1 gives the same normalized value in this instance; no general temperature or training-optimum claim is made.
- **L91 — bounded binary Brier contract.** `bounded_binary_brier_contract` derives `MemLp` from ambient a.e. strong measurability, binary labels, an `m`-strongly measurable score, and the stated a.e. score range, under the existing probability-measure and `m ≤ mΩ` premises. It reuses the conditional decomposition and unique optimum, then integrates using `integral_condExp`. This characterizes the population risk objective; it does not claim finite training found that objective or that an OOD conditional law matches.

The audit driver also checks five existing declarations: the conditional tower result, Brier decomposition and unique optimum, the equal-weight population/group finite example, and the earlier normalized-score counterexample. The actual audit log is preserved byte-for-byte as `axiom-audit.raw.txt`; run, job, artifact, source pins, declaration line mapping and hashes are in `verification.json`.

## Evidence boundary

Run 41271710425 attempt 1 / job 124745651579 succeeded for the requested changed-module target on subject `53a76a8f950ce309b28963b86582e978f6c61c5e`, tree `fcfdbc6aacd88a5a95735cf97a2f7ae79c793918`. The nine audited targets use only `propext`, `Classical.choice`, and `Quot.sound`, with no `sorryAx`. This is module-level evidence only. Full-record PR acceptance, exact-subject full chain, certificate/reference reconciliation, independent verifier, merge and post-merge checks remain pending.

This math-row result adds no actual consumer caller or joint-sampling proof. It does not upgrade other original-question rows, engineering requirements, or the separate designated Brier design cut. The two earlier failed changed-module runs remain recorded as failures.
