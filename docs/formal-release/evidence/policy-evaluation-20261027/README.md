# Finite policy evaluation, support/missingness and valid finite selection

Original 12.3–12.5 and correction S12 require the actual original values, not just a single propensity-weighted row. This module reuses the existing finite IPW identity and real clipping lemma. It proves a rational finite-population clipping-bias bound by summing actual discarded mass. Unsupported actions have explicit lower/upper completions; every bounded completion lies between them, and changing unsupported Bernoulli means preserves the whole logging law. The specified endpoints attain [.15,.65].

Exact original computations give logging value .45, always-one value .55, weights 4 and 4/3, clipped value .35 and bias .20. Personalization gives .75 in equal groups; the target mixture gives .64/.40/.72 for always-zero/always-one/personalized. These are frozen-population values under identified conditional means, not general deployment or legal conclusions. The missing-outcome family constructs normalized, nonnegative full binary joint distributions with identical visible records and sharp target interval [.5,1]. Two transition models agree on the whole first-stage log while terminal values under action 1 differ by 1.

For a predeclared finite policy family and genuine iid observations, the existing bounded finite-class theorem applied to actual scores divided by W derives simultaneous error W*sqrt(log(2M/delta)/(2n)). Its event is then consumed to prove at most 2*radius regret for a winner of the actual empirical scores, allowing the chosen policy to depend on those observations. W is positive and bounds the importance-weighted observations; when every score has zero range the score/value problem is identically zero. This does not infer correct propensities, causal exchangeability, measurement, support or mechanism stability from data. Reusing adaptive data with a newly generated family requires the separate history-conditional validation contract.

Independent [run 40450127416](https://github.com/laubeing-droid/legal-math-modeling/actions/runs/40450127416), [job 122010649641](https://github.com/laubeing-droid/legal-math-modeling/actions/runs/40450127416/job/122010649641), succeeded on `b25b14dde466b667284de537aad7640bba0f5a1b`: 16 exact type/axiom targets and 8 guarded executions. Both LF-normalized source files are bound; raw type/axiom messages are retained and contain only standard axioms. First subject `8f497e0d3fe2910df7a65a353d23d99100c88f92`, [run 40449847943](https://github.com/laubeing-droid/legal-math-modeling/actions/runs/40449847943), failed two proof simplifications (a rational endpoint and an equality simplified to True), and is not PASS evidence. The final version preserves the statements and additionally proves the confidence/winner theorem.

G-PROPOSED correspondence (baseline 825792b83476a767152396d7f5e2ba3017048841): this namespace/source is NEW; Frozen Policy.u12_1_finite_ipw, Policy.u12_3_clipped_bias, Behavior.indicator and later LearningFiniteClass.u01_1_iid_empirical_risk_uniform are reused without changing their sources.

| Symbol | Original obligation | Actual consumer/check |
|---|---|---|
| policyValue / importanceValue / clippedValue | 12.3 actual frozen policy values and clipping | original values/weights/bias executions and finite_clipping_bias_bound |
| fillUnsupported / unsupported_value_bounds | 12.3 lack of overlap | full Bernoulli logging-law equality and attainable [.15,.65] endpoints |
| missingJoint / missingVisibleMass | 12.4 outcome recording | valid full distribution, same visible records, sharp [.5,1] target |
| firstStageLog / terminalValue | 12.4 missing later state | same initial logs but terminal 1/0 under the chosen intervention |
| bounded_policy_score_uniform / bounded_policy_winner_probability | 12.5 finite fixed-family iid evaluation | actual score normalization, derived event and selected-policy regret |

Behavioral response, logit limits, damped dynamics, finite legally allowed suggestions and actual business/measurement/policy/RSI consumers remain separate obligations. Importing this module is not full U00 consumption. Root integration follows independent success; final PR/main acceptance is separate. OPEN=20, closes_debt=false, CAND8=8 outside PROVE_CANDIDATES; no frozen-pin/discharges/workflow/toolchain changes and no local Lean/Lake/Elan.

