# Strategic response, exact damping and legal information boundaries

Original 12.1, 12.2 and the information boundary of 12.6 / S12 are proved for their stated models. Every threshold in (0,1] gives the original three net utilities 0,.4,.9; gaming is the unique maximizing response. A rule reading only the score cannot distinguish equal-score effort and gaming even though their true outcomes differ.

The shifted logit calculation is proved equal to the original softmax of those actual utilities and is a positive normalized distribution. Its actual finite expected outcome and score are computed. At beta=0 they are 1/3 and 2/3; as real beta tends to infinity, the true outcome tends to 0 while the score tends to 1. These are model implications, not a verified behavioral law.

The same algebraic affine implementation supports exact rational execution and the original real-domain theorems. Its n-step formula holds for arbitrary n and initial state. The two original maps have the same unique fixed point 1/2. The reflection map has no limit from any noncentral real initial state. Damping preserves [0,1] when the rate lies there and converges to the original fixed point from every initial state in [0,1] exactly when 0<rate<1. This excludes both zero-step stasis and the undamped reflection endpoint. Local affine behavior can coexist with two distinct global fixed points; a globally stable center can lie outside an independently given legal interval. Identical behavioral data cannot recover two different admissible-policy sets.

Independent [run 40451401604](https://github.com/laubeing-droid/legal-math-modeling/actions/runs/40451401604), [job 122014729609](https://github.com/laubeing-droid/legal-math-modeling/actions/runs/40451401604/job/122014729609), succeeded on `c77fd50a8e6c0b937b0315ea1a6647387d7ba561`: 17 exact type/axiom targets and 7 guarded executions, standard axioms only, both LF-normalized sources bound. The real logit/limit results are kernel theorems, not Float approximations; the guarded executions exercise exact rational utility and trajectories. Raw 34 type/axiom message blocks are retained. The first subject `ff43e3c7f33ba32535d8f7f74a3db3670983feae`, [run 40451010939](https://github.com/laubeing-droid/legal-math-modeling/actions/runs/40451010939), failed Fin-numeral reductions and real-limit elaboration. Its unchanged claims were repaired with explicit finite indices, real constants and noncomputable real comparison; it is not PASS evidence.

G-PROPOSED correspondence (baseline 825792b83476a767152396d7f5e2ba3017048841): the namespace/source is NEW. The pinned Mathlib exponential and geometric-limit theorems are reused, with the original utility table, actual expectations, iteration and boundary cases supplied here. Frozen Policy's general contraction and signal/incentive statements remain unchanged.

| Symbol | Original obligation | Actual consumer/check |
|---|---|---|
| preparationUtility / finite_response_payoffs | 12.1 finite responses and score information | both original thresholds and exact response ranking |
| logitPreparation / logitQuality / logitScore | 12.1 finite rationality | original-softmax equivalence, normalization, actual expectations and limits |
| affineResponse / affine_iterate_formula | 12.2 actual n-step response | full real-domain convergence and exact rational executions |
| damping_converges_for_all_iff | 12.2 all rates and all initial states | sharp open-interval criterion, stasis/oscillation endpoints |
| local_affine_behavior_does_not_give_global_contraction | 12.2 local versus global claim | explicit distinct fixed points despite the specified local behavior |
| behavior_only_cannot_recover_admissible_sets | 12.6 separate normative basis | arbitrary data-only algorithm, identical observations and incompatible allowed sets |

This is not yet the finite admissible-policy suggestion implementation or business/measurement/policy/RSI consumer. Those and U00 remain separate. Root integration follows independent success; full PR/main acceptance is separate. OPEN=20, closes_debt=false, CAND8=8 outside PROVE_CANDIDATES; no discharges/frozen-pin/workflow/toolchain changes or local Lean/Lake/Elan.

