# U02.4 original-scope conditional-risk close

## Exact scope and evidence

The frozen manuscript L297-L299 supplies the actual conditional-risk setup under `P_H = P(· | H)` and the `H`/`Hᶜ` event split. Original-question 02.4 paragraphs 125, 127, and 129 state related but distinct parts of the same risk contract: generic finite conditional union bounds; independent/countable risk accumulation with its stated budget assumptions; and accumulation over one global attempt sequence. The old 17-target `HarnessRisk20261027` evidence remains recorded in the progress row and PR55 record. This package adds the actual `P_H` consequences and the exact global-index prefix/suffix identity; it does not introduce a separate risk-reserve or commit object.

### Paragraph 125: finite conditional risk

The old `finite_conditional_union_bound` and `finite_adaptive_union_bound` establish generic finite bounds under their declared measure and conditional-risk premises. The new `finite_prefix_external_condition_bound` instantiates `finite_adaptive_union_bound` with the actual conditional measure `P_H`. Given each attempt's conditional failure-risk bound and a pathwise cumulative budget bound for the finite prefix, it proves `P_H(⋃ B_t) ≤ ε`. With `P(Hᶜ) ≤ α`, the actual event partition gives `P(⋃ B_t) ≤ α+ε`.

### Paragraph 127: independent/countable accumulation

The old `countable_conditional_risk_budget` and `countable_summable_risk_budget` provide the conditional and summable-risk bounds. The old `bernoulliPaths`, `bernoulli_coordinates_are_independent`, `bernoulli_cylinder_probability`, `bernoulli_one_attempt_risk`, `no_failure_is_the_false_cylinder`, `independent_constant_risk_accumulates`, and `positive_constant_risk_has_no_fixed_subunit_horizon_limit` declarations establish the actual infinite Bernoulli product for `p : ℝ≥0` with `p ≤ 1`, its independent constant-risk model, and the finite-horizon failure probability for each `T : ℕ`; for positive `p`, failure tends to 1 as `T` grows, so no fixed subunit horizon bound follows. The new `countable_prefix_external_condition_bound` supplies the same conditional `P_H` conclusion and actual `H`/`Hᶜ` split for every finite prefix; continuity from below passes those prefix bounds to the countable union. The theorem uses the supplied prefix budget conditions and does not add an unconditional independence or general tower premise.

### Paragraph 129: one global attempt sequence

Every actual attempt receives its next index `t` in the same global sequence, and its history includes all earlier attempts. The same cumulative sum includes each new attempt. For each `ω`, let `f t = budget t ω` and `S_n(ω) = ∑ t ∈ Finset.range n, f t`. The reused Mathlib theorem `Finset.sum_range_add` states

`S_(n+m)(ω) = S_n(ω) + ∑ j ∈ Finset.range m, budget (n+j) ω`.

For any prefix length `n` and following segment length `m`, the identity decomposes the total into that prefix plus its suffix. If the same global sequence satisfies `S_(n+m)(ω) ≤ ε`, its suffix spend is at most `ε − S_n(ω)`. The prefix/suffix identity holds pointwise for every `ω`; probability bounds are guarantees under the declared measure (`P_H` where specified). If the cumulative cap holds only `P_H`-almost everywhere, the suffix inequality has that same `P_H`-almost-everywhere qualification. For a countable process the cumulative cap is assumed for every finite prefix. Grouping retries cannot reset the cumulative cap. The old `two_attempts_are_not_one_budget` witness shows why restarting the same per-attempt allowance fails; it is a counterexample, not a general prefix/suffix proof. Each actual attempt must still satisfy its conditional `δ` premise under the complete history; arbitrary learner updates do not automatically preserve that premise. This is the mathematical global-index contract, not a production forced-deduction proof or a newly required reservation/commit interface; the frozen manuscript does not require those systems. The Mathlib declaration is pinned to commit `c5ea00351c28e24afc9f0f84379aa41082b1188f`, `Mathlib/Algebra/BigOperators/Group/Finset/Basic.lean:548-553`.

The old `u02_4_hb_not_the_marginal_bound` witness is also retained: with `H=B`, marginal risk is `1/10` while conditional risk is `1`. It remains the stated counterexample/boundary.

## Independent audit

The six-target changed-module audit contains two new theorems, three reused repository declarations, and `Finset.sum_range_add`. Exact type and axiom output from run `41062973614`, attempt 1, job `124087082984`, is preserved in `axiom-audit.raw.txt`; subject, artifact, source pins, target names, and raw-file hash are in `verification.json`. The exact 17-target historical record remains intact in the progress row; this receipt does not overwrite or narrow that prior evidence.

## Historical archive wording

The pinned `scope-archive.json` is unchanged. `verification.json` retains the exact original `remaining_obligations` string, including its historical narrow/non-goal wording and reference to run `39783481932`. That string records the earlier evidence state. This package reads it together with the archived `exact_scope` and frozen manuscript L297-L299; it does not rewrite or delete archive history.

## Acceptance boundary

The 02.4 mathematical question is recorded as `COVERED` under the progress file's existing definition: the frozen conditional proposition and listed paragraphs have named proofs independently validated by authoritative CI, with their stated premises retained. This does not mean that the engineering requirements, six construction cuts, complete theory, real-world legal domain, actual runtime behavior, or deployment are covered. The six-target run is changed-module evidence; it is not a PR/full-release run or merge. The draft root imports and AxiomAudit entries were not covered by a full JurisLean-root build. The progress record remains `SOURCE_EVIDENCE_ONLY` until that release chain is completed. This round makes no actual-call change to the 15-edge consumer audit; that existing table remains authoritative, and this mathematical evidence upgrades no consumer edge. Global `discharges_archived_manuscript_gaps`, `math_flip_authorized`, and `step_2_closed` remain `false`.
