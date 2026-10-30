# U04.4 equicorrelated variance and effective-count close

## Frozen scope and evidence

The exact archived `U04.4` residual is retained verbatim in `verification.json`; the frozen `scope-archive.json` and tip pin are unchanged. The package audits the original equal-variance/equal-correlation model under its stated premises. It adds no assumptions of independence, zero mean, finite sample space, or a desired target formula. The frozen manuscript location is v003 `01_统一法律数学模型总稿.md` §U04.4, `方差等效量的退化分支`, lines 482–484; the older source pointer at lines 311–314 in `scope-archive.json` is preserved unchanged.

For `n ≥ 2`, common variance `v > 0`, measurable coordinates, and every off-diagonal covariance equal to `v * r`, `equicorrelated_mean_variance` proves the actual empirical-mean variance

`v * (1 + (n - 1) * r) / n`

and the nonnegativity of `D = 1 + (n - 1) * r`. `equicorrelated_mean_branches` separates the cases. If `D > 0`, it establishes positive `n_eff = n / D` and rewrites the same variance as `v / n_eff`. If `D = 0`, it proves the actual mean variance is zero, forces `r = -1 / (n - 1)`, and connects that boundary to the existing rational-valued `u04_4_variance_equivalent` constructor `EffectiveCount.degenerateZeroVariance`. The rational constructor is not evidence that the old software interface accepts arbitrary real-valued inputs.

The proof reuses the pinned Mathlib `variance_fun_sum` and `variance_mul_const` lemmas; coordinate AEMeasurability together with positive common variance supplies `MemLp 2`, without adding a premise.

The finite fair-coin construction takes `B` and `1 - B` under the actual `fairCoinMeasure`: each coordinate has variance `1/4`, their covariance is `-1/4`, their two-point average is identically `1/2`, and its variance is zero. The reused `u01_4_concrete_common_cause_counterexample` separately shows that distinct event identifiers do not imply independent coordinates: for `n > 1`, the common-cause sample mean has variance `1/4` and is not independent. In that common-cause case `r = 1`, so `D = n` and the formula gives `n_eff = 1`; this summarizes variance of the aggregate mean and does not restore independence among the original coordinates.

The audit contains three declarations from the new leaf and one reused declaration, plus four object checks. It does not claim a classification of all positive-semidefinite covariance matrices, Gaussianity, an extension of the zero-denominator constructor to arbitrary real carriers, restored independence, an actual old-consumer call, or real-data behavior.

## Original-question mapping

Only the effective-sample-count paragraph of original question `04.2` (the statement that file count does not itself establish effective sample size) receives this additional evidence. Its row remains `PARTIAL`: the variance identity and its positive/degenerate branches are source-mapped, while other statistical claims, real source-generation premises, and actual consumer evidence remain open. No 04.4 original-question row or any of the 15 consumer edges changes in this round.

## Independent changed-module audit

The four theorem targets and four object checks were audited by run `41098286355`, attempt 1, job `124209655817`, against subject `7dcee7f360758bebc15e7a2efc49ee76c7d97201` and tree `3c12367dac3fd20c4ed7287bf6bc91bf9753c5aa`. Each of the four theorem targets has exactly the standard `propext`, `Classical.choice`, and `Quot.sound` axioms; no `sorryAx` or nonstandard axiom was reported. The success artifact and all five source-file pins are recorded in `verification.json`; the 12 raw output blocks are extracted from this run's `changed-module.log`.

This is source/module evidence only. It is not PR/full-release/merge acceptance, consumer wiring, real-data validation, legal correctness, or whole-theory completion. Global archived-gap discharges, Step 2, and `math_flip` remain false.
