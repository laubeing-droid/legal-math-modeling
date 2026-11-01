# Original question 06.7 — finite chapter bridge evidence

This package maps frozen question 06.7 (L137/L139/L141; clauses U06.2/U06.5) to the accepted finite evidence listed below. The candidate row and complete-record status remain separate from this changed-module proof. The source-core commit is `9e62edd834bae22dbd8fc85d3c2fd0f34f0e8ed7` / tree `19ea36929958d4e7914b2103c52ebe95a3cdc1cd`; the selected changed-module Audit imports and compiles the new cash bridge. Its plan requests the Audit entrypoint only.

## L137 — the finite W4 tree and the cash-event bridge

The accepted W4 package gives a two-round finite bargaining tree with the existing action, history, information, deterministic transition, terminal ledger, and strategy-payoff links. This round adds the missing connection from a terminal cash-event view to the already proved W4 abstract terminal utility; it does not relabel the abstract utility record as a cash ledger.

For the finite witness, a terminal acceptance by A or B records exactly two cash events from party 0 (pot) to party 1 or 2. A failed terminal records no payment. Each event amount is the corresponding existing gross amount, the synthetic source marker is `⟨6707⟩`, and payment dates are the relevant round dates 0 or 1. Event IDs use `2 * terminalCode(z) + recipientBit`; uniqueness is proved within each terminal case only. The finite example holds a common `AmountTag` and valuation context fixed. `factDate` is the payment date, not the valuation time. The proof reuses the Q1 cash flow/net-cash definition and the accepted W4 payoff equality. The W4 preference parameter `δ = 1/2` discounts the later utility payoff; it is not a cash fee. This synthetic witness has no extra cash delay fee, which does not establish that a real arrangement has zero fees. The connection is limited to this stated finite model and does not claim a global EventId namespace invariant or a T113 interpretation.

## L139 — equilibrium concepts and their conditions

| Finite object or claim | Accepted evidence and finite example | Premises and boundary |
|---|---|---|
| Normal-form mixed Nash existence | Existing mixed-Nash/Brouwer results and the finite matching-pennies no-pure-equilibrium result | The existence theorem uses a finite player set, nonempty finite strategy sets, and finite outcomes (or the stated bounded-utility version). Strategies are product mixed strategies. A Brouwer fixed point theorem alone is not a Nash theorem. It does not apply to an arbitrary coupled feasible-policy set. |
| Finite perfect-information extensive form | Existing one-shot-deviation characterization for a given profile, with its finite-outcome and perfect-information assumptions | `EFG.oneShotDeviation_iff_spe` characterizes a supplied profile; it is not a general backward-induction construction theorem. The accepted cake-10 backward-induction instance is a separate finite example. The new cash bridge uses the W4 cake-100 model and does not identify the two examples. |
| Equilibrium selection | The accepted finite W4 profile/payoff bridges and the separate matching-pennies example | Existence does not imply uniqueness or a normative selection rule. No equilibrium concept is silently chosen for an application. |

The Audit in this package prints 32 selected declarations (3 new bridge targets and 29 reused targets). Those 32 checks support the mappings above; they are not the proof-count denominator for every earlier question package. The raw changed-module log also contains seven `#check` outputs, reported separately.

## L141 — seven-question finite deliverable and remaining boundary

| Question | Finite object and accepted evidence | Example or counterexample | Premises and remaining boundary |
|---|---|---|---|
| Q1: cash identity | `original06-1-cash-identity-close-20261101` | Three labels pointing to one six-unit event give true event cash 6 versus erroneous label-summing 18; two actual six-unit payments give gross 12 and opposite signed account nets | Real cash semantics, unique event IDs, common amount tag and valuation context are explicit. Old Q cash records embed one way into real cash; arbitrary real amounts are not asserted to encode exactly as rationals. |
| Q2: expected utility | `original06-2-expected-utility-close-20261101` | Higher success probability can yield lower expected cash; equal mean cash can rank differently under strict concave utility | The linear risk-neutral comparison and threshold are only under their stated common affine utility and baseline conditions. Money and utility are distinct quantities. |
| Q3: common robust strategy | `original06-3-common-robust-strategy-close-20261102` | A finite two-branch model has a common max-min strategy different from each branch's individual best | Feasibility is checked on reachable histories; the joint-action obstruction applies at the same reachable position. No minimax interchange or general mixed-strategy theorem is claimed. |
| Q4: value of information | `original06-4-information-20261031` | The accepted finite conditional value-of-information and robust monotonicity instances | Results retain their stated branch-law and decision premises. |
| Q5: observation and adaptation | `original06-5-observation-20261031` | Actual information states/options, a purchase trajectory with one cost, and a nonanticipating trajectory optimum | The accepted finite observation protocol and its information structure are retained; no new runtime consumer is inferred. |
| Q6: risk evaluation | `original06-6-risk-evaluation-close-20261102` | The risk-2 filter excludes the unconstrained risky optimum; at limit 0 the finite filter is empty | This is the expected-loss OR route. The no-choice result is for the supplied finite class under its well-formedness premises. A chance route would separately require its loss threshold and probability budget; those are not added here. |
| Q7: bargaining and equilibrium bridge | This package plus the accepted W4, matching-pennies, mixed-Nash/Brouwer, and one-shot-deviation evidence | The finite cake-100 cash-event bridge and the separate accepted cake-10 backward-induction example | The W4 bridge is finite and conditional on its stated shared currency/valuation context. T113 is not applied because its exact statement, assumptions, and source version were not supplied. No general bargaining-tree construction is added. |

The accepted Q4 and Q5 packages remain their complete evidence; this package cites them rather than reopening or reducing them. The row preserves the prior U06.2 and U06.5 evidence entries.

## External inputs, at most eight classes

These inputs are conditional on the application path; they are not all required for every finite result.

1. Finite game/control structure: actors, decision nodes, histories, information sets, actions, transition or kernel, and terminal rule.
2. Legal branches, chance laws, and observation laws when used. There is no implicit prior over the legal-branch type.
3. The finite candidate class `C`, its Q3 candidate-policy realization map, and the legal/physical/information feasibility evidence used to form the common feasible set; an arbitrary candidate set is not presumed feasible. This Q3 input is distinct from Q7 `φ`: the Q7 action/history/information/kernel/payoff bridge is constructed and proved by this package, not imposed as an external hypothesis.
4. Cash data: amounts, currency/unit/version (`AmountTag`), common valuation time, actual monetary costs, any real cash delay charge, and any exchange-rate conversion rule. Payment date and valuation time are separate. No event fee follows merely from a utility discount.
5. Preferences and criterion: utility functions, noncash utility, pure time preference (such as `δ`), and the chosen decision rule. The discount is not double-counted as a monetary fee.
6. The chosen risk route and its loss and expected-loss limit. Only if a chance-constrained route is selected are a loss cutoff and probability budget additionally needed.
7. T113's exact statement, assumptions, and source version only if that legal reference is to be applied. This package does not ask the user to construct or prove the finite `φ` bridge supplied here.
8. An external statutory cap source and its specified object, time, and aggregation rule only if a cap such as `Cap_N`/P584 is adopted. No new legal duty is inferred where the source is silent.

Missing real-world values remain conditional or `UNKNOWN`; finite theorem parameters do not establish their real-world provenance. Neither policy ownership nor statutory meaning is proved as a theorem here. The q-to-recommendation consumer path and runtime callers remain unchanged.

## Source and CI evidence

The selected Audit entrypoint ran in changed-module run [41358291966](https://github.com/laubeing-droid/legal-math-modeling/actions/runs/41358291966), attempt 1, job `125003002576`, on source `9e62edd834bae22dbd8fc85d3c2fd0f34f0e8ed7` / tree `19ea36929958d4e7914b2103c52ebe95a3cdc1cd`. It emitted 32 actual `#print axioms` results (3 new and 29 reused); the seven `#check` outputs are separate. No `sorryAx` or compiler errors appeared. The other seven workflow jobs were skipped. The artifact and exact per-target log lines are bound in `verification.json`; the raw log is retained byte-for-byte.

Two earlier failed runs remain distinct history. Run [41356995198](https://github.com/laubeing-droid/legal-math-modeling/actions/runs/41356995198), attempt 1, on subject `87b67c7a8148b96e0cb50d8a755460a2cfc9ba76`, printed 0/32 Audit targets because only the Instances module was requested and that module failed. Run [41357580430](https://github.com/laubeing-droid/legal-math-modeling/actions/runs/41357580430), attempt 1, on subject `7b731944dc728b480f60d06953cef2bf126fb8fe`, printed 31/32 (3 new and 28 reused) before the missing EFG import caused the final target to fail. Both failure artifacts and logs are retained separately; neither is counted as a pass.

The canonical math row has candidate-C mathematical mapping (`COVERED`); this is not full-record acceptance. Exact-subject PR acceptance, independent certificate/layout verification, and any consumer wiring remain separate gates.