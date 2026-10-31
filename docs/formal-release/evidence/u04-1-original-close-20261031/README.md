# U04.1 positive-real Beta prediction and finite sampling close

## Frozen scope and evidence

The exact archived U04.1 residual is retained verbatim in `verification.json`; the frozen scope archive and tip pin are unchanged. The audited scope is the archived `U04.1` posterior-and-prediction statement: positive real Beta parameters, the specified binomial likelihood, the next-observation bridge, and the half-copy/half-independent exchangeable construction. The older `remaining_obligations` text still mentions integer-shape reuse and the prior CI run; it is historical residual wording, interpreted against the frozen `exact_scope`, not rewritten as a new contract.

The frozen master locates U04.1 at §U04.1 L444–448 and L890–892, and original-question 04.3 at topic L103–110. The scope archive's older source pointer L273–278 remains unchanged.

For real `α, β > 0`, the reused `positive_real_beta_posterior_density`, `positive_real_beta_posterior_measure`, and `positive_real_beta_predictive_mean` declarations establish the normalized likelihood density, posterior measure, and posterior predictive mean. `u04_1_real_gamma_weight_ratio` is reused for the real Gamma weight identity. The new `beta_future_success_of_channel` connects the posterior predictive result to an actual next-observation kernel when its success probability equals `θ` almost everywhere under the posterior. The separate `beta_future_success_of_conditional_independence` gives the same result from the stated data likelihood, conditional independence of observed and future events given `θ`, and future success probability `θ`. These are sufficient model premises; the proof does not derive them from observed data.

The `half_copy_kernel_realizes_generation` theorem identifies the actual pair kernel as one-half copied draws plus one-half conditionally independent draws. Its `half_copy_exchangeable_counterexample` is exchangeable but has conditional future success `5/6`, not the Beta(1,1) one-success prediction `2/3`. It shows why exchangeability alone does not establish the predictive bridge. The two new channel theorems state the additional assumptions under which the posterior prediction follows.

`iid_bernoulli_mean_two_tail` instantiates the existing `row_mean_two_tail` theorem for actual Bernoulli-valued samples. Its guarantee requires the explicit IID sample law with common fixed parameter `p ∈ [0,1]`; this is a conditional concentration statement, not a derivation of that sampling law. `actual_beta_integrals_enclosure` connects rational lower and upper enclosures for the actual incomplete and complete Beta-kernel integrals to the clipped ratio interval and its explicit width bound, reusing `u04_2_enclosed_propagation`. It does not compute the integrals or provide an approximation algorithm.

## Original-question mapping

The previously accepted U04.2 package and this source audit together map the three specified subparagraphs of original question 04.3:

- **L105:** positive-real Beta likelihood conjugacy, posterior measure, and posterior mean are established by the reused exact probability declarations.
- **L107:** the half-copy construction supplies the exchangeable `5/6` versus `2/3` counterexample; the fixed-parameter Bernoulli two-tail bound is separately conditional on its actual IID premises. The counterexample does not imply a real dataset follows that mechanism.
- **L109:** the new actual-integral enclosure connects the numerator and denominator Beta integrals to the ratio and width statement under supplied rational enclosures; the U04.2 propagation theorem supplies the interval algebra.

Under the existing `COVERED` definition, original-question row 04.3 is covered for these frozen statements and stated premises. This does not close U04.1 as an archive clause beyond its own exact scope, does not promote original-question rows 04.1 or 04.2, and does not establish calibration, a data-generation mechanism, actual consumer wiring, real-data behavior, or legal correctness. No consumer-edge or six-cut change is claimed.

## Independent changed-module audit

The ten named theorem targets and nine object checks were audited by run `41124014317`, attempt 1, job `124297730406`, against subject `af2000042f139e1cb504d2bedf0ce5bb7c894bff` and tree `2e2d82987ac47a6ebab3e8145c381d074f51fada`. All ten targets have exactly the standard `propext`, `Classical.choice`, and `Quot.sound` axioms; no `sorryAx`, nonstandard axiom, or conflicting target output was reported. The successful artifact and seven source-file pins are recorded in `verification.json`; the 29 raw output blocks are extracted from this run's `changed-module.log` and are limited to the audit driver.

This is source/module evidence only. It is not PR/full-release/merge acceptance, consumer wiring, real-data validation, legal correctness, or whole-theory completion. Global archived-gap discharges, Step 2, and `math_flip` remain false.
