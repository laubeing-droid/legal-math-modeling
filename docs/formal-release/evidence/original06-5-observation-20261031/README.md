# Original U06.5 finite observation instance — CI receipt

This evidence package records changed-module CI for the supplementary finite observation instance on the exact subject below. It does not close or reopen the global U06.5 ledger debt: that debt was previously closed by PR81. `closes_debt` is `false` in `verification.json`.

- Repository: `laubeing-droid/legal-math-modeling`
- Branch: `formal/original06-5-observation-20261031`
- Subject: `9c6e5603a226aba53861f9d151cf97b5350387a7`
- Git tree: `cf07752ad13dbd6e22b78b0458dc60025ad973af`
- CI: run `41182937172`, attempt 1; `changed-modules` job `124483896794` succeeded.
- Artifact changed-module-only-41182937172-1, ID `13035807675`, 8,402 bytes; SHA-256 is recorded in `verification.json`.
- Artifact members: `module-plan.json` and `changed-module.log`.

The audit driver checked the three named public declarations and printed their axioms. Each depends only on `propext`, `Classical.choice`, and `Quot.sound`; the captured audit output contains no `sorryAx` and no compiler errors. This is changed-module CI evidence only, not full-release, cross-repository, empirical, or legal acceptance.

The two source files are identified in `verification.json` by Git blob, byte size, LF line count, and SHA-256. Their downloaded bytes and the original artifact ZIP/log are retained alongside this three-file package under `../raw/` for receipt traceability; they are intentionally not copied into this package.

Original-question mapping is split by its frozen lines. L121 reuses `U06_5OriginalModels20261031.signal_information_values`: every no-signal policy `Unit → Bool` has value 1/2, while `Prod.fst` reads the hidden truth and attains 1; this is the two-world nonanticipation counterexample, not an admissible policy. L123 is supplemented by `actual_information_states_and_options` and `actual_purchase_trajectory_and_single_cost`, which bind visible posteriors/options and count k once (0.8−k versus 0.5; cutoff 0.3). L125 reuses `U06_1FiniteBellman20261030.bellman_optimum_of_actual_trajectory_expectation` and `nonrectangular_bellman_counterexample`, and adds `actual_nonanticipating_trajectory_optimum` for the finite visible-history instance. Partial observation still requires an externally supplied observation kernel/belief update; no hidden-state input is given to the policy.
