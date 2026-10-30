"""Dispositions for the 50 archived manuscript gaps.

The manuscript pin ``evidence/ci-tip-e87543d8/scope-archive.json`` stays
verbatim. The live carry is ``evidence/ci-tip-f85ebe44/scope-archive.json``.
Carrying those rows is not a proof and does not close a gap. This module is
the construction record that processes each pinned ``remaining_obligations``
string on the math pack's suggested path:

* ``缩`` rewrites the residual as an explicit non-goal in the same row as the
  claimed-scope declarations.
* ``证`` wires the formal candidate bodies to declarations accepted by the
  live tip-pin axiom audit (subject f85ebe44644f32820e9d0fad1325428fb8f171d9,
  run 40115638107, job 120936221970). A sentence those declarations do not
  state stays ``OPEN_FORMAL_TAIL``. Companion non-goals from the 2026-10-24
  rejudge are written on that same row.

Nothing here sets ``discharges_archived_manuscript_gaps``. The live tip-pin
retarget does not close an ``OPEN_FORMAL_TAIL`` row and does not authorize
``math_flip``. Gate run 39960871624 is not a close. Local Lean is not invoked.
"""

from __future__ import annotations

# clause -> (file, short, role) witnesses that are audited but are not already
# the clause's listed declarations. Roles say what the witness is, not that it
# discharges a stronger manuscript sentence.
EXTRA_WIRED: dict[str, list[tuple[str, str, str]]] = {
    "U10.1": [
        ("Temporal.lean", "u08_1_selection_stable", "reused fixed-history selection stability"),
        ("Trace.lean", "u10_2_finite_trace_composition", "reused finite trace composition"),
    ],
    "U07.1": [
        (
            "Acceptance.lean",
            "n07_1_constant_family_not_separating",
            "constant two-point observation does not separate",
        ),
        (
            "Acceptance.lean",
            "a07_1_identity_observation_separates",
            "adding the identity observation separates the two points",
        ),
        (
            "Acceptance.lean",
            "n07_1_retraction_need_not_encode_surjectively",
            "a retraction need not make the encode map surjective",
        ),
    ],
    "U07.2": [
        (
            "Representation.lean",
            "n07_2_incompatible_fiber",
            "two singleton fibers over distinct points have no common value",
        ),
    ],
    "U02.2": [
        (
            "Acceptance.lean",
            "a02_transaction_actual_commit",
            "synthetic commit example",
        ),
        (
            "Acceptance.lean",
            "a02_transaction_actual_replay",
            "synthetic replay example",
        ),
        (
            "Acceptance.lean",
            "n02_cancelled_attempt_no_commit",
            "cancelled attempt does not commit",
        ),
    ],
    "U02.3": [
        (
            "Harness.lean",
            "zero_coverage_not_zero_risk",
            "empty-successor / zero-coverage ratio is not a zero risk",
        ),
        (
            "Acceptance.lean",
            "a02_common_idle_remains_allowed",
            "common idle stays in the finite safe intersection",
        ),
    ],
    "U03.1": [
        (
            "Acceptance.lean",
            "n03_must_facts_closure_is_not_robust_closure",
            "robust-intersection countermodel body; not a connection proof",
        ),
    ],
    "U03.2": [
        (
            "Acceptance.lean",
            "n03_incomplete_fuel_is_not_closure",
            "insufficient fuel is not a checked closure",
        ),
    ],
    "U04.4": [
        (
            "Acceptance.lean",
            "n04_zero_variance_not_finite_count",
            "zero-denominator branch u04_4_variance_equivalent 2 (-1) = degenerateZeroVariance",
        ),
    ],
    "U05.2": [
        (
            "Acceptance.lean",
            "n05_raising_score_threshold_increases_risk",
            "raising a score threshold can increase risk; not the rare-group example",
        ),
    ],
    "U10.3": [
        (
            "Progress.lean",
            "multistep_simulation_not_one_step",
            "a length-sum can exceed the step count; not a zero-step prohibition",
        ),
        (
            "Progress.lean",
            "two_cycle_has_no_strict_rank",
            "two-cycle has no strict rank; not business-observation faithfulness",
        ),
    ],
    "U12.4": [
        (
            "Policy.lean",
            "distinguishable_signal_insufficient",
            "distinguishability counterexample for the frozen inequalities",
        ),
    ],
    "U15.3": [
        (
            "Iteration.lean",
            "two_round_exact_risks",
            "exact two-point risks used by the second-round consumer",
        ),
    ],
}

# Pack companion notes that must appear in the same row as the close.
COMPANION_NOTES: dict[str, str] = {
    "U01.4": "The frozen finite label/truth, source/deployment, dependence, and grouping witnesses are mapped to exact existing declarations; the finite models do not assert real-data behavior or deployment acceptance.",
    "U02.2": "companion_缩: 真实DB精化/外部副作用/最终完成",
    "U04.4": "The variance-derived effective count is conditional on the archived equal-variance/equal-correlation model; it does not imply independence or validate a software consumer.",
    "U02.4": "The finite/countable risk bounds and single global-attempt cumulative-budget contract are audited under the stated premises; Finset.sum_range_add identifies each prefix plus its suffix. No separate reserve/commit object or runtime execution is introduced.",
    "U09.2": "The existing rational-valued finite cash theorems are audited under the archived per-event balance and closed-account premises; no actual occurrence, boundary-account completeness, lawful discharge, or 15-edge consumer call is claimed.",
    "U10.1": "companion_缩: external legal authority / 真实授权合法性",
    "U08.3": "non_goal: 现实真值定理",
    "U10.3": "companion_缩: 公平/外部响应",
    "U13.1": "authority 集成＝另证（NON_GOAL）",
    "U09.1": "companion_缩: legal allocation effects / 法律关系消灭",
    "U04.3": "companion_缩: 校准/因果/数值求准＝另证（非本条声称）",
    "U12.4": "companion_缩: 真实成本/偏好/审计合法性",
    "U13.4": "companion_缩: RSI全称改进定理",
    "U15.3": "companion_缩: external load readback path",
}

# Paths after 未决改判_20261024. abandon is intentionally absent.
PATHS: dict[str, str] = {
    "U07.1": "证",
    "U07.2": "证",
    "U07.3": "证",
    "U03.1": "证",
    "U03.2": "证",
    "U02.1": "证",
    "U02.2": "证",
    "U02.3": "证",
    "U02.4": "证",
    "U08.1": "证",
    "U10.1": "证",
    "U10.2": "证",
    "U08.2": "证",
    "U08.3": "证",
    "U10.3": "证",
    "U09.1": "证",
    "U09.2": "证",
    "U09.3": "证",
    "U01.0": "证",
    "U01.1": "证",
    "U01.2": "证",
    "U01.3": "证",
    "U01.4": "证",
    "U04.1": "缩",
    "U04.2": "证",
    "U04.3": "证",
    "U04.4": "证",
    "U04.5": "证",
    "U05.1": "缩",
    "U05.2": "证",
    "U06.1": "证",
    "U06.2": "证",
    "U06.3": "证",
    "U06.4": "证",
    "U06.5": "缩",
    "U11.1": "证",
    "U12.1": "证",
    "U12.2": "证",
    "U12.3": "证",
    "U12.4": "证",
    "U13.1": "证",
    "U13.2": "证",
    "U13.3": "证",
    "U13.4": "证",
    "U14.1": "证",
    "U15.1": "证",
    "U14.2": "证",
    "U15.2": "证",
    "U15.3": "证",
    "U00": "缩",
}

# Explicit non-goals. Narrow rows must have some. Prove rows carry the pack
# companion here, in the same record as the wiring.
NON_GOALS: dict[str, list[str]] = {
    "U01.4": [
        "The finite counterexamples and variance models are not claims that real data follow the bad mechanism, that source labels are authentic, or that deployment is accepted.",
        "The split-map result is only a within-domain single-valued grouping statement; it does not prove iid or exclude future/source bias.",
    ],
    "U02.1": [
        "The result is conditional on the frozen finite Bool-world/action table and the manuscript's d0≥0 opening-debt premise; it does not derive the real legal permission domain or world table from source materials.",
        "The theorem covers runs that report a concrete current poststate; it makes no claim about unknownCommit outcomes without a known poststate, deployment, or general operation beyond this pipeline.",
    ],
    "U04.2": [
        "The declarations prove the stated probability and measure claims under their explicit mathematical premises; invalid examples mark failed premises and are not runtime input validators.",
        "This package does not close original-question 04.4: missing-group all-failure/all-success models, endpoint identified sets, and external identification conditions shared with U11.1 were not individually checked here.",
        "U00 edge 6 remains numerically unconnected: the old decision consumer still reads i.alternatives probabilities; this package does not wire the new probability results into that consumer.",
    ],
    "U07.2": [
        "This close covers the conditional joint object produced by a successful frozen sourceModel output only; it does not assert real-source truth/faithfulness or compatibility for arbitrary supplied layers.",
        "No universal StrongSameCase/localSound premise is added, and the CAND8 negative boundary declarations remain historical evidence rather than positive close evidence.",
    ],
    "U07.3": [
        "The semantic interpretation of the selected finite catalog row is an explicit external condition; this proof does not derive source truth or historical identity O05 from raw material.",
        "The clause is not quantified over every extractor. This package does not connect the old Final20261021.Pipeline consumer to the new source-model witness, nor close all original-question 07.3/07.5/07.6 obligations.",
    ],
    "U02.2": [
        "Full refinement of concrete Ledger/Pipeline into Store/Trace, including external occurrences, is an explicit non-goal.",
        "真实DB精化、外部副作用、最终完成 are explicit non-goals. China-law discharge is not decided here.",
    ],
    "U02.4": [
        "No deployed/runtime execution or actual old-Harness consumer execution is claimed; the package audits the stated mathematical risk and global cumulative-budget premises.",
        "Each new global attempt still requires its conditional-risk premise under the complete history; an arbitrary learner update does not itself preserve the per-attempt bound. U14.1's learning-evaluation round ledger is not used as evidence for the global attempt sequence.",
    ],
    "U10.1": [
        "External legal authority and 真实授权合法性 are explicit non-goals. A reference or a Lean check does not prove legal authority. The China-law column stays separate.",
    ],
    "U08.3": [
        "现实真值定理 is an explicit non-goal. The four-state product is a classification contract, not a theorem about real-world truth.",
    ],
    "U10.3": [
        "公平 and 外部响应 are explicit non-goals of this clause (exact_scope: 另证).",
    ],
    "U13.1": [
        "Authority integration is an explicit non-goal of this candidate row (exact_scope: 另证).",
    ],
    "U13.3": [
        "This close is limited to same-law/same-loss risk transfer on represented inputs under the used-domain inverse premise, plus the existing two-world nonidentification boundary.",
        "U13.2 rule-update permission and complete observation/exchange relation; U13.4 fallback applicability, provenance, error handling and original examples; and 原题13.5 InScope criteria and normative/retrieval/prediction fallback consumption remain to be checked against existing implementations and original-question instances.",
    ],
    "U09.1": [
        "Full legal allocation effects are an explicit non-goal. 金额清零不等法律关系消灭; this wiring does not close a China-law extinction claim.",
    ],
    "U09.2": [
        "Actual occurrence of the cash events is an explicit external premise of the frozen proposition, not a theorem of the finite closed-account sum.",
        "Completeness of boundary accounts is an explicit external premise; fees and boundary flows must be included or named.",
        "A real transfer does not by itself establish lawful discharge. The China-law column stays separate.",
    ],
    "U01.4": [
        "The named finite witnesses are not a claim that real data follow the bad mechanism.",
        "Run 39783481932 compiling these declarations does not discharge a real-data claim.",
    ],
    "U04.1": [
        "A non-integer pointwise density identity beyond the real Gamma weight ratio is an explicit non-goal.",
        "Run 39783481932 compiling the integer-shape reuse and the 5/6-versus-2/3 witness does not discharge that identity.",
    ],
    "U04.3": [
        "Calibration, causal identification, and numerical attainment (校准/因果/数值求准) are explicit non-goals and are not this clause's claim.",
    ],
    "U04.4": [
        "The effective count summarizes the variance of the aggregate mean and does not restore independence among the original coordinates.",
        "No full covariance-matrix classification or original-coordinate independence theorem is claimed.",
    ],
    "U05.1": [
        "The continuous tie-break that produces a uniform rank is an assumption of this finite identity, not a density theorem. That density theorem is an explicit non-goal.",
        "Deployment-shift failure is the marginal-versus-group split, not a separate process theorem.",
        "Run 39783481932 compiling the finite rank identities does not discharge a continuous tie-break density theorem.",
    ],
    "U06.5": [
        "Brouwer/mixed equilibrium is not claimed and is an explicit non-goal.",
        "Hidden-information sequential equilibrium is not bi_one_step_no_gain and is an explicit non-goal.",
        "The T113 perfect-information carrier remains JurisLean.Seams.UnifiedW4Games.bi_one_step_no_gain and is not re-labeled as the hidden-information statement.",
        "Run 39783481932 compiling the signal-value, (4,6) tree, and matching-pennies declarations does not discharge Brouwer/mixed equilibrium or hidden-information sequential equilibrium.",
    ],
    "U12.4": [
        "真实成本, 偏好, and 审计合法性 are explicit non-goals. China-law audit legitimacy is not decided by the frozen inequalities.",
    ],
    "U06.1": [
        "This package proves the finite, fully observed, single-branch Markov control model and its actual trajectory law; it does not establish a common feasible policy or max-min value across legal branches.",
        "Signal acquisition/stopping costs and partially observed belief updates are not modeled here. The old Pipeline decision consumer has not been wired to these finite-control values, and this is not deployment or legal/empirical validation.",
    ],
    "U06.2": [
        "The positive-affine and ε+2η results are mathematical payoff-transfer statements, not a general equilibrium-existence theorem.",
        "The W4 bridge is the fixed two-round instance; it does not claim the old Pipeline consumes these numeric KernelGame values or close original-question 06.7 as a whole.",
    ],
    "U12.3": [
        "The finite selector result is conditional on the stated iid law, score bounds, support and frozen causal assumptions; it does not derive causal truth from SourceRef fields.",
        "The MAR result keeps the recording indicator and visible Option projection explicit under assignment/recording support. Sequential transport is finite-horizon, uses a shared full-history environment kernel and target-reachable-history coverage, and is not an infinite-horizon RL theorem.",
        "The old Pipeline numeric consumer and RSI feedback path remain unwired; no U00 consumer edge is newly closed.",
    ],
    "U13.4": [
        "An RSI全称改进定理 is an explicit non-goal. This clause is a type/selection contract, not an improvement theorem.",
    ],
    "U15.3": [
        "The external load readback path is an explicit non-goal. An external link does not prove the two-round construction.",
    ],
    "U00": [
        "All 50 subclaims are NOT closed by the finite source-to-decision-to-two-payment-to-feedback paths.",
        "A common statistical law, full operation refinement, and authorized Loaded consumption are NOT closed.",
        "This narrow is not an abandonment of the other forty-nine clauses.",
    ],
}

CLAIMED_SCOPE: dict[str, str] = {
    "U02.4": "For finite T and countably many rounds, under the actual conditional measure P_H=P(·|H), conditional failure bounds and finite-prefix cumulative risk budgets imply conditional union risk ≤ ε; with P(Hᶜ) ≤ α, the actual H/Hᶜ event partition gives unconditional union risk ≤ α+ε. For one global attempt sequence, Finset.sum_range_add gives S_(n+m)=S_n+suffix, so a total cap ε bounds the suffix by ε−S_n without resetting on retry grouping. The retained H=B witness has marginal 1/10 and conditional risk 1.",
    "U09.2": "Finite closed-account event-sum and per-account conservation for rational-valued cash vectors, under the frozen same-unit closed-account and per-event balance premises.",
    "U01.4": "The frozen finite claims are checked by existing point-mass train/deployment risk and actual-fit witnesses; the independent 1/(4n), copied 1/4, common-cause n>1, and same-training two-world witnesses; plus the existing within-explanation-domain grouping theorem. No real-data claim is made.",
    "U04.1": "Integer-shape density conjugacy, predictive mean, real Gamma weight ratio, and the exchangeable 5/6 versus Beta(1,1) 2/3 witness.",
    "U04.4": "Under the archived equal-variance/equal-correlation premises, the actual empirical-mean variance is v(1+(n-1)r)/n and the factor is nonnegative. For positive denominator the finite effective count n_eff=n/(1+(n-1)r) gives the same variance as v/n_eff; the zero-denominator branch proves the actual mean variance is zero and connects the forced rational boundary to the existing degenerate constructor. The B/(1-B) fair-coin witness and reused common-cause counterexample distinguish aggregate variance from coordinate independence.",
    "U05.1": "Tie-free rank prefix mass, threshold inequality k/(n+1)≥1-α, infinity branch, and the marginal-versus-group numeric split.",
    "U06.5": "Signal value 3/10-cost, cost>3/10 net negative, the given two-round tree (4,6), and matching-pennies with no pure equilibrium.",
    "U06.2": "Finite mixed expected-payoff ε+2η transfer and the fixed two-round W4 bargaining strategy/tree/terminal-ledger payoff bridge; no general mixed-equilibrium existence claim or old Pipeline numeric-consumer claim.",
    "U12.3": "Generic finite-class 2ε winner bound plus the actual find? Some-branch oracle bound with computed empirical optimization gap and None abstention; finite logging-law expectation equals policyValue; explicit finite MAR/visible-recording correction; and finite-horizon full-history shared-kernel likelihood-ratio transport under per-history support.",
    "U11.1": "Finite-X binary-treatment real-valued causal bridge, original finite instances for 04.4/11.2/11.6, and reused measurement/selection/transport evidence for original 11.1–11.6; arbitrary measurable selection weights remain a conditional paper derivation.",
    "U13.4": "Audited population forecasts consume actual fitted calibration inputs under explicit sampling/law/iid/measurability/loss/radius premises; sampled fallback returns the equal-weight mean of checked mature observations under explicit iid conditions; declared priors remain separate model inputs; and absent/invalid sources return named UNKNOWN results.",
    "U10.1": "Actual full-context authorized refresh-to-Step protocol connection: the checked actualPost.env is passed through selectedHorn/fullHorn, full Gamma/history/permission/process is rechecked after each nonempty internal refresh, and an empty tail terminates. Existing authorization, selection stability, and trace declarations are reused; actual legal authority remains an external boundary.",
    "U12.1": "General finite-action causal IPW bridge and actual measured-policy connection under explicit causal/measurement premises; reused clipping and selector proofs; affine real support-range characterization plus existing same-log endpoint evidence; and three finite original-question examples for 12.3 and 12.6. No real-world premise derivation or old Pipeline consumer wiring is claimed.",
    "U00": "Actual finite source-to-decision-to-two-payment-to-feedback paths named by the clause declarations.",
}

# Formal sentences the wired declarations do not state. Empty means the
# suggested path is fully dispositioned (narrow, or wiring plus non-goals).
UNWIRED: dict[str, list[str]] = {
    "U02.4": [],  # The original finite/countable risk, partition, and global-attempt budget contract is independently audited.
    "U07.2": [],  # Closed only by the independent successful-source joint-object package.
    "U07.3": [],  # Finite selected-row semantics and actual projections are audited by the independent U07.3 package; O05 truth remains a non-goal.
    "U03.1": [],  # Independently proved and audited by the later U03 closure package.
    "U03.2": [],  # Independently proved and audited by the later U03 closure package.
    "U02.1": [],  # Closed by the independent actual-pipeline refinement package.
    "U10.1": [],  # Independent protocol package closes the exact refresh-to-Step residual.
    "U01.1": [],  # Original residual proved in the independent U01 package.
    "U01.2": [],  # Original residual proved in the independent U01 package.
    "U01.3": [],  # Original residual proved in the independent U01 package.
    "U01.4": [],  # Frozen finite witnesses are independently audited against the exact archived residual.
    "U04.2": [],  # Independently audited against the full frozen probability residual in the U04.2 close pack.
    "U04.4": [],  # The archived equicorrelated variance residual is independently audited in its exact scope.
    "U04.5": [],  # General event likelihood and copy-information proofs independently accepted.
    "U06.1": [
    ],  # The independent finite Bellman/trajectory package closes this archived residual.
    "U06.2": [],  # The independent mixed-payoff and fixed W4 strategy/tree package closes the archived residual.
    "U11.1": [],  # The independent U11.1 package audits the archived residual.
    "U12.1": [],  # Independent U12.1 causal and original-instance package closes this archived residual.
    "U12.3": [],  # Independent selector, MAR, and finite-horizon history-kernel proofs close this archived residual.
    "U12.4": [],  # Independently audited against the full frozen model in the U12.4 close pack.
    "U13.3": [],  # The source-audited independent package closes this row only.

    "U13.4": [],  # Independent fallback selector and conditional risk bridges close this archived residual.
    "U14.1": [],  # Independently proved and audited by the U14.1 closure package.
}

SCOPE_REVIEW: dict[str, str] = {
    "U01.4": (
        "Independent U01.4 finite-scope close: `pointWeight_is_probability`, `pointPopulationRisk_eq`, and `actualConstantFit_value` witness the frozen literal Y=false/T=true/actualConstantFit false construction with train risk 0 and deployment risk 1. For `allowed(action) := action = true`, the same finite set has the witness `action = true`, while the actual fit output `false` is not allowed. The existing `LearningERM20261027.u01_1_actual_empirical_fit_minimizes` theorem supplies the nonempty finite empirical-fit minimization contract as context; no duplicate minimization theorem or production Fit/provenance claim is added. `u01_6_perfect_fit_does_not_supply_authorization` retains its opposite-label authorization boundary. For source/deployment, point masses P(false)/Q(true), target `id`, and fitted `actualConstantFit false` give source 0/deployment 1; the same-training two-world theorem is for finite samples generated from P and every deterministic learner. The dependence audit checks independent fair Bernoulli variance 1/(4n), copied variance 1/4, and the distinct-ID common-cause counterexample for n>1. `grouped_unit_not_split` only states within-domain single-valued grouping and does not imply iid or exclude future/source bias. These 10 declarations and five object checks were independently audited at subject f80e790e6d6ecbd8449f2181433673945540e5af, run 41081311144, job 124150886815. This closes only the archived finite U01.4 witnesses; it does not claim real data follow the bad mechanism, universal empirical truth, source authenticity, deployment acceptance, the separate U01.4 representation-error question, or completion of original-question rows 01.1/01.3/01.5/04.2."
    ),
    "U04.4": (
        "Independent U04.4 source-bound close: under n≥2, common variance v>0, coordinate measurability and the archived common off-diagonal covariance v*r premise, `equicorrelated_mean_variance` proves the actual empirical-mean variance v*(1+(n-1)*r)/n and nonnegativity of the factor D=1+(n-1)*r. `equicorrelated_mean_branches` proves the positive-D branch has n_eff=n/D and variance v/n_eff; at D=0 it proves actual mean variance zero, forces r=-1/(n-1), and connects the rational boundary to the existing `u04_4_variance_equivalent` degenerate constructor. The `fair_coin_complement_witness` gives the actual B/(1-B) model with variances 1/4, covariance -1/4, constant mean 1/2 and mean variance 0. Reused `u01_4_concrete_common_cause_counterexample` gives distinct identifiers with non-independent coordinates and empirical-mean variance 1/4 for n>1; when r=1, D=n and n_eff=1, which is an aggregate-variance summary rather than restored independence. The existing zero-denominator constructor remains rational-valued; this is not a claim that an old software API accepts arbitrary real inputs. Four targets and four object checks were independently audited at subject 7dcee7f360758bebc15e7a2efc49ee76c7d97201, run 41098286355, job 124209655817. This closes only the archived U04.4 mathematical scope; no full PSD classification, Gaussian assumption, restored independence, real-data claim, original-question 04.4 row, or consumer-edge call is claimed. Original-question 04.2 receives only the effective-count subparagraph evidence and remains PARTIAL."
    ),
    "U09.2": (
        "Independent U09.2 original-scope close: the two existing `Ledger` theorems establish that rational-valued event vectors with zero sum over a finite closed account type yield zero total event sum and zero summed per-account cash vector. This matches the frozen U09.2 finite-sum claim and original-question 09.8 cash paragraph, under its same-unit, closed-account, and per-event balance premises. The original residual is retained verbatim: actual event occurrence and completeness of boundary accounts remain external premises; fees and boundary flows must be included or named. The audit checks both theorem types/axioms and `cashVector`’s object type in run 41065859816, job 124096972537. It does not prove lawful discharge, refund-stage or debt-decomposition claims, or any actual call edge; other 09.8 obligations and U09.3 remain outside this close."
    ),
    "U02.4": (
        "Independent U02.4 original-scope close: finite `finite_conditional_union_bound` / `finite_adaptive_union_bound` and the new finite theorem establish the finite conditional-risk consequence under the actual P_H=P(.|H); the old `countable_conditional_risk_budget`/`countable_summable_risk_budget`, `bernoulliPaths`, `bernoulli_coordinates_are_independent`, `bernoulli_cylinder_probability`, `bernoulli_one_attempt_risk`, `no_failure_is_the_false_cylinder`, `independent_constant_risk_accumulates`, `positive_constant_risk_has_no_fixed_subunit_horizon_limit`, and new `countable_prefix_external_condition_bound` cover countable summable bounds, actual Bernoulli products, and every finite T under the frozen model assumptions. The actual H/Hᶜ partition gives α+ε. For paragraph 129's one global attempt sequence, each ω has f(t)=budget(t,ω), and Mathlib `Finset.sum_range_add` gives S_(n+m)=S_n+suffix; the total cap bounds the suffix by ε−S_n without retry-grouping reset. The conditional δ premise must remain valid under each complete history and is not automatically preserved by arbitrary model updates. The retained H=B counterexample and old 17-target evidence remain in the progress record. Two new declarations, three reused repository declarations, and the Mathlib identity were independently audited at subject 814c10b0d404eaba8848636de8169b815460d70a, run 41062973614, job 124087082984. The original scope archive remains byte-for-byte unchanged; historical wording is preserved in original_residuals and interpreted against exact_scope rather than rewritten."
    ),
    "U02.1": (
        "Independent U02.1 actual-pipeline close: the actual public Pipeline.run path binds its two accepted payment payloads and checked rule output to the frozen finite Bool-world/action gate; a reported current poststate is shown to preserve Trace.Invariant and to be the true successor-table state. The proof uses the manuscript's d0≥0 opening-debt premise and the original Bool-world/action table; it does not derive a real-world permission domain or the table from source materials. The finite counterexamples retain the distinctions between schema and norm checks, checked action and executed action, and context-version invalidation, plus the common idle/empty-successor boundary. Unknown-commit outcomes without a reported concrete poststate are outside the reported-result premise. Exact named evidence: docs/formal-release/evidence/u02-1-debt-close-20261029; independent changed-module CI audits the named declarations and source binding only."
    ),
    "U04.2": (
        "Independent U04.2 frozen probability residual close: the package audits the general real interval width connection, the exact Beta(2,3) half-point integral/rate instance, and a common Fin 8 probability mass function realizing every admissible real three-event joint probability for arbitrary marginals, including endpoints and same-margin mixtures. It also audits the actual contamination measure and conditional difference bound under the stated positive-conditioning premises, including the zero-Q(B) branch and a numerical amplification witness. The invalid-input examples indicate failed premises or infeasible endpoints; they are not runtime validators. The four archived U04.2 residual components are thereby addressed. This does not close original-question 04.4: its missing-group all-failure/all-success models, endpoint identified sets, and external identification conditions shared with U11.1 were not individually checked; no absence-of-code claim is made. U00 edge 6 remains numerically unconnected because the old Pipeline decision path still reads i.alternatives probabilities. Exact named evidence: docs/formal-release/evidence/u04-2-debt-close-20261029; independent changed-module CI audits the named declarations and source binding only."
    ),
    "U07.2": (
        "Independent U07.2 source-model close: for an actually accepted sourceModel output, construct x=(frame,n) so suppliedLayers equals jointLayers and the JointContract records the actual extracted source, both bound payments, exact sourceModel modelOf output, exact amount, LegacyContracts, frozen background fields, sequential four-stage projections, and final ledger balance/conservation/cash/quantity projections. The implication is conditional on sourceModel returning .ok; the ambient JointObject type does not assert every pair succeeds. This does not establish real-source fidelity, arbitrary-layer compatibility, StrongSameCase/localSound, or close U07.3. The two CAND8 negative declarations remain negative boundaries and are not positive close evidence. Exact named evidence: docs/formal-release/evidence/u07-2-debt-close-20261029; independent changed-module CI audits the named declarations and source binding only."
    ),
    "U07.3": (
        "Independent U07.3 conditional source-model close: given an accepted sourceModel output and an explicit interpretation relation for the selected finite catalog row, the audit reads back recordOf key/claimedAmount/registered, the observed relation, and the first payment's history key and full payload meaning; it also proves equality of the named paymentFields projections for two successful outputs with the same frozen background/material/branch/catalog. The finite counterexamples show that amount alone does not identify event or obligor and that identical CaseRecord values do not determine semantics across different catalogs. The clause's original 17.2 wording does not quantify over every extractor; this is a bounded selected-row Extract/Interpret connection, not real-source truth or historical identity O05. The external interpretation inputs are not derived from raw material. It does not claim the old Final20261021.Pipeline calls this driver, or close all original-question 07.3/07.5/07.6 obligations. Exact named evidence: docs/formal-release/evidence/u07-3-debt-close-20261029; independent changed-module CI audits the named declarations and source binding only."
    ),
    "U13.3": (
        "Independent U13.3 source-bound close: the existing representation-transfer declaration supplies pointwise prediction equality for the bijective representation change; the new audit bridge substitutes equality under the frozen used-input inverse premise inside the same-law, same-loss integral; and the existing two-world theorem supplies a finite nonidentification witness, with the empty-sample instance and two endpoint worlds. The missing-checkpoint declaration supplies UNKNOWN when all checkpoint inputs are absent. Exact named evidence: docs/formal-release/evidence/u13-3-debt-close-20261028. This does not establish that every unsupported-domain case is represented by these witnesses, nor does it close U13.2/U13.4/原题13.5 obligations listed as non-goals; those remain to be checked against existing implementations and original-question instances. The CI run audits named Lean declarations and their source binding only."
    ),
    "U12.4": (
        "Independent U12.4 source-bound close: the frozen finite binary-audit, "
        "three-action model proves nonnegative normalized audit masses for each "
        "nonzero action, zero reward for the zero action, and the exact payoffs "
        "0, pE-3/5, and pG-1/10. Its strict-best-action-1 iff reuses the existing "
        "Policy theorem, with all three actions compared and pE,pG quantified over "
        "their probability-valid range. The existing distinguishability counterexample, "
        "finite response payoff table, and score-only quality separation are also "
        "audited by the same changed-module run. Exact named evidence: "
        "docs/formal-release/evidence/u12-4-debt-close-20261029. Real costs, "
        "preferences, and audit legality remain non-goals; this does not close the "
        "other U12.1 causal/measurement or support-gap obligations, nor adjacent "
        "OPE consumer edges. The CI run audits named Lean declarations and source "
        "binding only."
    ),
    "U06.2": (
        "Independent U06.2 close: the finite mixed-payoff declarations establish the general allowed-deviation real payoff transfer with ε+2η and preserve the existing full-deviation and positive-affine conditions. The fixed W4 instance connects complete strategies, the two-round tree, action/history/information data, deterministic kernel, terminal ledger payoff and the equilibrium-transfer declarations. This is not a general mixed-equilibrium existence theorem and does not assert that the old Pipeline consumes the new numeric KernelGame values. For original-question 06.7, only the fixed two-round tree and KernelGame payoff bridge are mapped; the manuscript's mixed-NE existence conditions, matching-pennies/general backward-induction alignment, and overall seven-question obligation remain PARTIAL. No U00 edge is newly connected. Exact named evidence: docs/formal-release/evidence/u06-2-debt-close-20261030; independent changed-module CI audits the named declarations and source binding only."
    ),
    "U12.3": (
        "Independent U12.3 source-bound close: the generic finite-class 2ε winner bound is reused; the actual find? selector is connected on its Some branch to a 2ε plus computed empirical optimization-gap oracle inequality, while None is abstention. Under the explicitly constructed finite logging law, the actual score expectation is connected to finite policyValue. The MAR bridge keeps the recording indicator and visible Option projection explicit and proves the assignment/recording weighted correction under stated support. The finite-horizon sequential bridge generates trajectories from a shared full-history environment kernel, proves the product of per-history target/logging ratios, and transports expected returns under target-reachable-history coverage. These results are conditional on the stated law and causal identification premises; SourceRef does not prove them. The old Pipeline numeric consumer and RSI feedback path remain unwired, and this is not an infinite-horizon RL theorem or deployment claim. Exact named evidence: docs/formal-release/evidence/u12-3-debt-close-20261030; independent changed-module CI audits the named declarations and source binding only."
    ),
    "U10.1": (
        "Independent U10.1 protocol close: the checked actualPost.env is used to select and evaluate the actual selectedHorn/fullHorn rule set. The initial state and every nonempty internal refresh recheck full Gamma, history, permission, and process before the remaining protocol continues; a successful refresh with an empty tail terminates directly. Existing authorization, fixed-history selection stability, and finite trace path/invariant results are reused. Pay, replay, and unknownCommit remain handled by the existing one-step executor. This connects the archived refresh-to-Step obligation without asserting that ActionMeaning proves legal authority or that checkNext is a complete checkBranch world/successor semantics. Exact named evidence: docs/formal-release/evidence/u10-1-debt-close-20261030; independent changed-module CI audits named declarations and source binding only."
    ),
    "U12.1": (
        "Independent U12.1 close: the general finite-action causal IPW bridge is stated for an arbitrary probability space and measurable covariate space with integrable real outcomes, under explicit consistency, conditional exchangeability, and target support. The actual measured-policy corollary connects the checked measurement and policy score to that theorem under the frozen measurement and causal premises. Existing support-gap endpoints are reused; the new real interval result characterizes their affine range, while the endpoint worlds remain tied to the existing same-log construction. The three original finite instances directly address the 12.3 value range and the 12.6 behavior-only and proxy-score counterexamples. These proofs do not establish real identification, measurement validity, normative permission, or old Pipeline consumption; those remain external or unwired conditions. Exact named evidence: docs/formal-release/evidence/u12-1-debt-close-20261030; independent changed-module CI audits named declarations and source binding only."
    ),
    "U11.1": (
        "Independent U11.1 close: the named finite-X, binary-treatment bridge derives "
        "consistency from version/exposure alignment, observed conditional means from "
        "consistency, exchangeability and positivity, and the finite g formula for "
        "integrable real-valued potential outcomes. The actual finite instances cover "
        "the shared 04.4 missing-outcome endpoints and MCAR recovery, the 11.2 Bernoulli "
        "countermodels, and the 11.6 same-behavior/different-constraint example. Reused "
        "measurement and selection declarations cover the enumerated original 11.1–11.6 "
        "claims. The general selection-weight formula in the README is a conditional "
        "expectation derivation; the Lean MAR instance is finite and rational and is not "
        "a theorem for arbitrary measurable selection laws. This does not wire the old "
        "Pipeline's numeric consumers or establish real-world identification premises. "
        "Exact named evidence: docs/formal-release/evidence/u11-1-debt-close-20261030; "
        "independent changed-module CI audits named declarations and source binding only."
    ),
    "U13.4": (
        "Independent U13.4 fallback close: the audited branch reads the actual fitted table, calibration result, applicability input and optional personal checkpoint under the existing sample/law/iid/measurability/loss/radius premises; it is a conditional population-risk bound, not a per-case win-rate guarantee. The sampled branch reads checked mature measurement rows and labels and returns their actual equal-weight sample mean, with its error bound under the stated same-law and iid conditions. Declared prior input remains a separate model condition; absent or invalid source attempts return named UNKNOWN, while the normative partial function remains separate. Source references and applicability inputs do not prove source authenticity, physical applicability or iid sampling. This closes only U13.4; it does not establish an RSI-wide improvement theorem, change original-question 13.4, close original-question 13.5, or connect the old Pipeline/consumer. Exact named evidence: docs/formal-release/evidence/u13-4-debt-close-20261030; independent changed-module CI audits the named declarations and source binding only."
    ),
    "U06.1": (
        "Independent U06.1 finite-control close: in the finite, fully observed, single-branch timed Markov model with general terminal reward g, the manuscript requires the empty-action case to be explicitly terminal or BLOCKED with a specified value; this module chooses the terminal branch with value g(s). A history-based legal policy has a trajectory law built from the actual transition kernel. The package proves nonnegative trajectory weights of total mass one and equality of trajectory expected return with policy value, constructs a legal greedy policy attaining the Bellman optimum and dominating all legal history policies, and counts same-policy cost once. Its finite nonrectangular example separates a fixed model choice from statewise choices. The reused free-information theorem remains its existing finite-law/list-policy result. This does not prove a common feasible strategy or max-min value across legal branches, signal-acquisition/stopping costs, partial-observation belief updates, or actual numeric consumption by the old Pipeline; those remain outside this close. Exact named evidence: docs/formal-release/evidence/u06-1-debt-close-20261030; independent changed-module CI audits the named declarations and source binding only."
    ),
    "U14.1": (
        "Independent U14.1 residual closure: ProtectedFeedback20261027 supplies "
        "the independent statistical validation core: the iid joint event over "
        "the pre-declared finite class, the actual sampled-block confidence "
        "premise, the joint-event preservation of each protected-domain risk "
        "bound, and the separation of proven strict improvement from observed "
        "improvement. AdaptiveValidation20261027 and HarnessRisk20261027 supply "
        "the adaptive conditional budgets: predictable per-history failure "
        "budgets without cross-round independence, fresh iid validation inside "
        "each positive-mass history cell, the sample count that meets the "
        "radius, the random-budget adaptive union bound, and the actual round "
        "ledger keeping the declared limit under arbitrary finite round "
        "actions. ValidatedFeedbackLoad20261027, AdaptiveRoundLedger20261027 "
        "and BusinessFeedbackLoop20261027 supply the service-load integration: "
        "the loaded package is the actual written readback behind parent, "
        "snapshot, context, evaluation, protected-scope, sampling and "
        "authority gates; the loaded model follows the computed validation "
        "bounds; the assessed load comes from the actual activation; the "
        "newly loaded model is the next round actual parent; and the next "
        "production action reads the actual assessment post. Exact named "
        "evidence: docs/formal-release/evidence/u14-1-debt-close-20261028. "
        "This does not certify real-world label truth, the supplied sampling "
        "laws, deployed services, or legal validity; those stay external "
        "premises of the original contract."
    ),
    "U04.5": (
        "Independent U04.5 residual closure: MeasurementLikelihood20261027 proves "
        "the joint event likelihood chain under explicit positive denominators, "
        "derives multiplication from measurement independence under EACH hypothesis "
        "law, and proves that an observed deterministic copy leaves the event and "
        "likelihood unchanged. A zero reference mass gives no finite ratio; a "
        "nondegenerate measurement cannot be independent of itself. "
        "ExactProbability20261027 proves equality of the generated sigma-fields "
        "and conditional expectations. Exact named evidence: "
        "docs/formal-release/evidence/u04-5-debt-close-20261027. "
        "This does not certify real identities, the supplied laws or independence, "
        "or assign a density likelihood to a zero-probability observation."
    ),
    "U01.1": (
        "Independent U01 residual closure: LearningFiniteClass20261027 derives the "
        "actual iid sample-mean bound with sqrt(log(2M/delta)/(2n)) and the "
        "data-selected approximate ERM oracle for a fixed nonempty finite class. "
        "LearningRisk20261027 proves the three-part representation/head/estimation "
        "decomposition and the collapsed-representation half-gap counterexample. "
        "LearningERM20261027 separately consumes the oracle for its actual minimizer. "
        "Exact residual evidence: docs/formal-release/evidence/u01-debt-close-20261027. "
        "Sampling, common loss and population premises remain explicit; an adaptive "
        "class enlargement is not covered. This does not close all U00 obligations."
    ),
    "U01.2": (
        "Independent U01 residual closure: LearningBridge20261027 integrates the "
        "same measurable [0,1] loss under a probability measure and proves the "
        "classification event inclusion. Random label and bridge upper bounds "
        "combine by a union bound without an independence assumption. Each bound "
        "must satisfy its own failure budget; a point estimate is not that premise. "
        "Exact evidence: docs/formal-release/evidence/u01-debt-close-20261027. "
        "This neither changes the loss nor certifies the target's legal truth."
    ),
    "U01.3": (
        "Independent U01 residual closure: LearningBridge20261027 defines TV by "
        "measurable event differences on the full joint task space, derives the "
        "general measurable [0,1]-loss integral bound by layer cake in both "
        "directions, and applies it to every member of a model class. "
        "Exact evidence: docs/formal-release/evidence/u01-debt-close-20261027. "
        "No finite-support reduction, marginal-only TV, estimated TV certificate "
        "or unsupported-domain validity is substituted for the original theorem."
    ),
    "U03.1": (
        "Independent U03 residual closure: CompilerProvenance20261027 checks a finite "
        "acyclic graph and passes its actual accepted leaves and enabled rules into "
        "CompilerClosure20261026. The executable robust-query countermodel is strict "
        "beyond the common-facts closure. SourceCompilation20261027 consumes that "
        "actual output; semantic soundness keeps source/rule truth as explicit premises. "
        "Exact named evidence: docs/formal-release/evidence/u03-debt-close-20261027. "
        "This does not derive source truth, rule legal force, or absence of exceptions."
    ),
    "U03.2": (
        "Independent U03 residual closure: CompilerClosure20261026 bounds the actual "
        "duplicate-list computation by the number of distinct initial facts and rule "
        "heads, proves closure for every sufficient fuel and checked derivability "
        "equivalence. The actual provenance/source consumer supplies that bound. "
        "Exact named evidence: docs/formal-release/evidence/u03-debt-close-20261027. "
        "No infinite-generation termination or real-world negation is claimed."
    ),
    "U01.0": (
        "Wired statements are the independent bounded-sum two-tail at a strictly "
        "positive threshold and the D=0 null tail, together with the clause-listed "
        "mgf bounds those statements use. Assumptions are the theorem binders "
        "(independence, bounds, positive threshold). This review does not extend "
        "them and does not treat gate run 39960871624 as acceptance."
    ),
    "U02.2": (
        "Wired statements are the abstract transaction-safety lemmas, the "
        "commit/replay/cancel examples, and the complete-read CAS snapshot lemma "
        "accepted on tip-pin job 120936221970. Concrete store refinement and "
        "external effects are non-goals in this same row, not proved omissions."
    ),
    "U06.4": (
        "Wired statements remain the tip-pin audited Decision threshold identities. "
        "This close admits the FormalTail20261024 out-of-range / unit-interval "
        "corollaries named in evidence/ci-tip-f85ebe44 (named_count=25; "
        "candidate_axiom_audit PASS) as discharging the prior UNWIRED q-in-[0,1] "
        "corollary gap. It does not claim a stronger manuscript sentence, China-law "
        "discharge, or discharges_archived_manuscript_gaps."
    ),
    "U08.1": (
        "Wired statements remain the tip-pin audited Temporal selection/history "
        "lemmas. This close admits the FormalTail20261024 late-record / disguise / "
        "mutable-current-status theorems named in evidence/ci-tip-f85ebe44 as "
        "discharging the prior UNWIRED countermodel gap. It does not claim a "
        "stronger manuscript sentence or flip discharges."
    ),
    "U10.3": (
        "Wired statements remain the tip-pin audited Progress length/rank lemmas. "
        "This close admits the FormalTail20261024 zero-step / business-observation "
        "theorems named in evidence/ci-tip-f85ebe44 as discharging the prior "
        "UNWIRED faithfulness/zero-step gap. 公平 and 外部响应 remain explicit "
        "non-goals on this same row. It does not flip discharges."
    ),
    "U12.2": (
        "Wired statements remain the tip-pin audited Policy contraction-sufficiency "
        "lemma. This close admits the FormalTail20261024 damping / oscillation / "
        "noncontraction counterexamples named in evidence/ci-tip-f85ebe44 as "
        "discharging the prior UNWIRED gap. It does not claim a stronger manuscript "
        "sentence or flip discharges."
    ),
    "U14.2": (
        "Wired statements remain the tip-pin audited Feedback cluster lemmas. This "
        "close admits the FormalTail20261024 zero-N / endogenous-size / common-cause "
        "theorems named in evidence/ci-tip-f85ebe44 as discharging the prior "
        "UNWIRED gap. It does not claim a stronger manuscript sentence or flip "
        "discharges."
    ),
    "U08.2": (
        "Wired statements remain the tip-pin audited Temporal selection/history lemmas. "
        "This close admits the FormalTail20261024 theorems "
        "u08_2_current_singleton_does_not_exhaust_reachable and "
        "u08_2_nonempty_observation_preserves_chosen_answer named in the live tip-pin "
        "expand evidence (CAND5bis; named_count=37) as discharging the prior UNWIRED "
        "current-vs-reachable / nonempty-observation gap. It does not claim a stronger "
        "manuscript sentence, China-law discharge, or discharges_archived_manuscript_gaps."
    ),
    "U09.3": (
        "Wired statements remain the tip-pin audited Policy/Decision lemmas. This close "
        "admits the FormalTail20261024 theorems u09_3_greedy_prefix_misses_second_claim "
        "and u09_3_same_institution_accrual_is_not_cash_effect named in the live tip-pin "
        "expand evidence as discharging the prior UNWIRED greedy-prefix / same-institution "
        "legal-effect gap. It does not claim a stronger manuscript sentence or flip discharges."
    ),
    "U13.1": (
        "Wired statements remain the tip-pin audited Feedback/evidence lemmas. This close "
        "admits the FormalTail20261024 theorems u13_1_lawful_stat_input_change_changes_estimate "
        "and u13_1_personal_update_preserves_rule_service named in the live tip-pin expand "
        "evidence as discharging the prior UNWIRED lawful statistical-evidence input-change "
        "gap. Authority integration remains an explicit non-goal on this same row. It does "
        "not flip discharges."
    ),
    "U15.1": (
        "Wired statements remain the tip-pin audited Progress/Learning lemmas. This close "
        "admits the FormalTail20261024 theorems u15_1_finite_state_strict_improve_length_bound, "
        "u15_1_no_parameter_successor_has_no_fixed_point, and "
        "u15_1_telescoping_consumes_cumulative_improvement named in the live tip-pin expand "
        "evidence as discharging the prior UNWIRED finite-state strict-improvement / "
        "no-parameter-convergence gap. It does not claim a stronger manuscript sentence or "
        "flip discharges."
    ),
    "U15.2": (
        "Wired statements remain the tip-pin audited Progress/Learning lemmas. This close "
        "admits the FormalTail20261024 theorems u15_2_key_point_regression_changes_exact_risk, "
        "u15_2_finite_obs_agree_not_global, and u15_2_full_agreement_preserves_risk named in "
        "the live tip-pin expand evidence as discharging the prior UNWIRED key-point regression "
        "/ finite-observation indistinguishability gap. It does not claim a stronger manuscript "
        "sentence or flip discharges."
    ),
    "U08.3": (
        "本条关项范围＝FormalTail 覆盖的形式义务；不扩展到 companion／中国法／原稿更强句。"
        "Wired statements remain the tip-pin audited EvidenceProcedure lemmas. "
        "This close admits the FormalTail20261024 theorems "
        "u08_3_four_states_do_not_exhaust_dependency_policies, "
        "u08_3_judgment_not_compatibility_world_classification, and "
        "u08_3_opposition_preserves_support_not_full_reflection named in the live "
        "tip-pin expand evidence (CAND6; named_count=49) as discharging the prior "
        "UNWIRED four-state／dependency-policy／compatibility-world gap. "
        "NON_GOAL（同条旁注保留）：现实真值定理＝另证. "
        "It does not claim a stronger manuscript sentence, China-law discharge, "
        "or discharges_archived_manuscript_gaps."
    ),
    "U15.3": (
        "本条关项范围＝FormalTail 覆盖的形式义务；不扩展到 companion／中国法／原稿更强句。"
        "Wired statements remain the tip-pin audited Iteration lemmas. "
        "This close admits the FormalTail20261024 theorems "
        "u15_3_two_point_risks_do_not_complete_five_evidence_levels and "
        "u15_3_second_round_consumer_is_not_evidence_ladder named in the live "
        "tip-pin expand evidence as discharging the prior UNWIRED "
        "two-point／second-round／five-evidence-level gap. "
        "NON_GOAL（同条旁注保留）：external load readback path＝另证. "
        "It does not claim a stronger manuscript sentence or flip discharges."
    ),
    "U13.2": (
        "本条关项范围＝FormalTail 覆盖的形式义务；不扩展到 companion／中国法／原稿更强句。"
        "Wired statements remain the tip-pin audited RSI lemmas. "
        "This close admits the FormalTail20261024 theorems "
        "u13_2_frames_do_not_imply_authorized_rule_load and "
        "u13_2_condition_does_not_train_not_persistent_storage_refinement named in "
        "the live tip-pin expand evidence as discharging the prior UNWIRED "
        "authorized-rule-load／persistent-storage-refinement gap. "
        "It does not claim a stronger manuscript sentence or flip discharges."
    ),
    "U09.1": (
        "本条关项范围＝FormalTail 覆盖的形式义务；不扩展到 companion／中国法／原稿更强句。"
        "Wired statements remain the tip-pin audited Ledger／Trace lemmas. "
        "This close admits the FormalTail20261024 theorems "
        "u09_1_conservation_not_receipt_revision_order, "
        "u09_1_receipt_coherent_not_cash_uniqueness, and "
        "u09_1_at_most_once_not_product_protocol_refinement named in the live "
        "tip-pin expand evidence as discharging the prior UNWIRED "
        "receipt-revision-order／cash-uniqueness／product-protocol gap. "
        "NON_GOAL（同条旁注保留）：法律分配效果／法律关系消灭＝另证. "
        "It does not claim a stronger manuscript sentence or flip discharges."
    ),
    "U10.2": (
        "本条关项范围＝FormalTail 覆盖的形式义务；不扩展到 companion／中国法／原稿更强句。"
        "Wired statements remain the tip-pin audited Trace／Pipeline lemmas. "
        "This close admits the FormalTail20261024 theorems "
        "u10_2_executor_and_trace_not_full_mixed_operation_coverage and "
        "u10_2_post_invariant_not_gamma_frame_or_service_refinement named in the "
        "live tip-pin expand evidence as discharging the prior UNWIRED "
        "mixed-operation／Gamma-frame／service-refinement gap. "
        "It does not claim a stronger manuscript sentence or flip discharges."
    ),
    "U07.1": (
        "本条关项范围＝FormalTail 覆盖的形式义务；不扩展到 companion／中国法／原稿更强句。"
        "Wired statements remain the tip-pin audited Representation／Acceptance lemmas. "
        "This close admits the FormalTail20261024 theorems "
        "u07_1_retraction_not_full_observation_decoding_acceptance, "
        "u07_1_separation_monotone_not_history_decoding, and "
        "u07_1_encode_nonsurjective_not_full_decode_acceptance named in the live "
        "tip-pin expand evidence (CAND7; named_count=61) as discharging the prior "
        "UNWIRED full-observation／history-decoding-acceptance gap. "
        "It does not claim a stronger manuscript sentence, China-law discharge, "
        "or discharges_archived_manuscript_gaps."
    ),
    "U02.3": (
        "本条关项范围＝FormalTail 覆盖的形式义务；不扩展到 companion／中国法／原稿更强句。"
        "Wired statements remain the tip-pin audited Harness／Acceptance lemmas. "
        "This close admits the FormalTail20261024 theorems "
        "u02_3_finite_enumeration_not_generator_support_coverage and "
        "u02_3_common_idle_and_zero_coverage_not_support_coverage named in the live "
        "tip-pin expand evidence as discharging the prior UNWIRED "
        "generator-support-coverage gap. It does not claim a stronger manuscript "
        "sentence or flip discharges."
    ),
    "U04.3": (
        "本条关项范围＝FormalTail 覆盖的形式义务；不扩展到 companion／中国法／原稿更强句。"
        "Wired statements remain the tip-pin audited Probability lemmas. "
        "This close admits the FormalTail20261024 theorems "
        "u04_3_unpenalized_positive_not_penalized_minimizer_existence, "
        "u04_3_unpenalized_improves_not_uniqueness, and "
        "u04_3_arbitrarily_small_not_intercept_coordinate_solved named in the live "
        "tip-pin expand evidence as discharging the prior UNWIRED "
        "penalized-minimizer-existence／uniqueness／intercept-coordinate gap. "
        "NON_GOAL（同条旁注保留）：校准／因果／数值求准＝另证. "
        "It does not claim a stronger manuscript sentence or flip discharges."
    ),
    "U05.2": (
        "本条关项范围＝FormalTail 覆盖的形式义务；不扩展到 companion／中国法／原稿更强句。"
        "Wired statements remain the tip-pin audited Calibration／Acceptance lemmas. "
        "This close admits the FormalTail20261024 theorems "
        "u05_2_bernoulli_brier_not_conditional_expectation_decomposition and "
        "u05_2_selected_risk_not_simultaneous_threshold_or_rare_group named in the live "
        "tip-pin expand evidence as discharging the prior UNWIRED "
        "conditional-expectation-Brier／simultaneous-threshold／rare-group gap. "
        "It does not claim a stronger manuscript sentence or flip discharges."
    ),
    "U06.3": (
        "本条关项范围＝FormalTail 覆盖的形式义务；不扩展到 companion／中国法／原稿更强句。"
        "Wired statements remain the tip-pin audited Decision lemmas. "
        "This close admits the FormalTail20261024 theorems "
        "u06_3_eval_exists_unique_not_interval_multiplication_enclosure and "
        "u06_3_decision_respects_allowed_not_general_uncertainty_comparison named in "
        "the live tip-pin expand evidence as discharging the prior UNWIRED "
        "interval-multiplication-enclosure／general-uncertainty-comparison gap. "
        "It does not claim a stronger manuscript sentence or flip discharges."
    ),
}

DOES_NOT_CLAIM = [
    "tip Authority 39960871624 SUCCESS is gate only and does not close this archive row",
    "empty live exact_scope and remaining_obligations do not close this archive row",
    "PASS_REEXTRACTED_STANDARD_AXIOMS_ONLY does not by itself prove the manuscript sentence",
    "prior tip-pin work on e87543d did not close this archive obligation",
    "this row does not set discharges_archived_manuscript_gaps",
]

TIP_PIN = {
    "subject": "21862d9bdd94bfa15e5da39079538b5eb30ff235",
    "run_id": 40274167574,
    "job_id": 121413235107,
    "axiom_audit": "PASS_REEXTRACTED_STANDARD_AXIOMS_ONLY",
    "verification": "evidence/ci-tip-21862d9b/verification.json",
}

# Expand-audit naming for CAND5+CAND5bis+CAND6+CAND7 FormalTail theorems. Live
# tip_pin is bound to tip Authority 40274167574 / job 121413235107 (SUCCESS) on
# subject 21862d9b. Prior tip-pin 1c72e444 / 40257646857 remains historical
# CAND5+CAND5bis+CAND6 (named_count=49). dc7b7430 / 40190504653 remains
# CAND5+CAND5bis (named_count=37). f85ebe44 remains CAND5-only (named_count=25).
# This retarget does not close debt.
FORMAL_TAIL_EXPAND = {
    "subject": "21862d9bdd94bfa15e5da39079538b5eb30ff235",
    "tip_authority_run_id": 40274167574,
    "job_id": 121413235107,
    "verification": "evidence/ci-tip-21862d9b/verification.json",
    "live_tip_pin_retarget": "BOUND",
    "tip_authority_run_status": "SUCCESS",
    "criteria_pack": "tip_pin_扩审计_CAND7_20261026",
}

GATE_ONLY_RUN = 39960871624
GATE_ONLY_SHA = "f080eee0ffeadb09d8fe404adb3dcddf326b4a11"
CRITERIA_PACK = "/home/box/shared/legal-math-reviewer/archive_gap_判据包_20261024/"
PREFIX = "JurisLean.Candidates.Final20261021."

# Formal-tail round on the same pipeline. The live tip-pin may move when an
# authorized retarget says so. That move does not close a tail, does not
# authorize discharges, and does not open a second track.
FORMAL_TAIL_PACK = "/home/box/shared/legal-math-reviewer/formal_tail_判据包_20261024/"
FORMAL_TAIL_PACK_FILES = (
    "判据包.md",
    "施工放行条件.md",
    "TAIL40清单.md",
    "TAIL40清单.json",
)
FORMAL_TAIL_ROUND = "formal_tail_20261024"
# Tip Authority after archive-gap PR #9. Recorded as gate-only. Not the pin.
LATER_TIP_GATE = {
    "subject": "c0b90b6998dfd6bf3a23792bed83af118726d6da",
    "run_id": 40063377178,
    "closes_debt": False,
    "retargets_tip_pin": False,
    "step_2_closed": False,
}
CANDIDATE_MODULE = "proofs/lean/juris_lean/JurisLean/Candidates/FormalTail20261024.lean"
CANDIDATE_MODULE_NAME = "JurisLean.Candidates.FormalTail20261024"
# These eight stay on the prove path and must carry non-goals in the same row.
COMPANION_TAIL_IDS = (
    "U08.3",
    "U10.3",
    "U09.1",
    "U04.3",
    "U12.4",
    "U13.4",
    "U15.3",
)
CLOSED_NARROW_IDS = (
    "U04.1",
    "U05.1",
    "U06.5",
    "U00",
)
CLOSED_WIRING_IDS = (
    "U13.3",
    "U12.4",
    "U14.1",
    "U04.5",
    "U01.1", "U01.2", "U01.3",
    "U03.1",
    "U03.2",
    "U02.2",
    "U01.0",
    "U06.4",
    "U08.1",
    "U10.3",
    "U12.2",
    "U14.2",
    "U08.2",
    "U09.3",
    "U13.1",
    "U15.1",
    "U15.2",
    "U08.3",
    "U15.3",
    "U13.2",
    "U09.1",
    "U10.2",
    "U07.1",
    "U02.3",
    "U04.3",
    "U05.2",
    "U06.3",
    "U07.2",
    "U07.3",
    "U02.1",
    "U04.2",
    "U06.1",
    "U06.2",
    "U12.3",
    "U13.4",
    "U11.1",
    "U12.1",
    "U10.1",
    "U02.4",
    "U09.2",
    "U01.4",
    "U04.4",
)
# Historical CAND5 wiring closes (pack formal_tail_关≥1_CAND5_20261025).
CAND5_CLOSED_IDS = ("U06.4", "U08.1", "U10.3", "U12.2", "U14.2")
FORMAL_TAIL_CAND5BIS_PACK = (
    "/home/box/shared/legal-math-reviewer/formal_tail_真证CAND5bis_20261025/"
)
CAND5BIS_IDS = ("U08.2", "U09.3", "U13.1", "U15.1", "U15.2")
# Historical CAND5bis wiring closes. The live closed_this_round field is CAND7.
CAND5BIS_CLOSED_IDS = CAND5BIS_IDS
CAND5BIS_CLOSED_THIS_ROUND = 5
FORMAL_TAIL_CAND5BIS_CLOSE_PACK = (
    "/home/box/shared/legal-math-reviewer/formal_tail_关≥1_CAND5bis_20261025/"
)
# Expand-audit naming (pack tip_pin_扩审计_CAND6_20261026). Naming is not a close.
# Source order in FormalTail20261024.lean is this tuple, appended after the
# earlier 37 theorems. Archive order is different; the module-order check
# keeps the suffix instead of interleaving these clauses.
CAND6_IDS = ("U08.3", "U15.3", "U13.2", "U09.1", "U10.2")
FORMAL_TAIL_CAND6_PACK = (
    "/home/box/shared/legal-math-reviewer/tip_pin_扩审计_CAND6_20261026/"
)
# Historical CAND6 wiring closes (pack formal_tail_关≥1_CAND6_20261026).
CAND6_CLOSED_IDS = CAND6_IDS
CAND6_CLOSED_THIS_ROUND = 5
FORMAL_TAIL_CAND6_CLOSE_PACK = (
    "/home/box/shared/legal-math-reviewer/formal_tail_关≥1_CAND6_20261026/"
)
# Expand-audit naming (pack tip_pin_扩审计_CAND7_20261026). Naming is not a close.
CAND7_IDS = ("U07.1", "U02.3", "U04.3", "U05.2", "U06.3")
FORMAL_TAIL_CAND7_PACK = (
    "/home/box/shared/legal-math-reviewer/tip_pin_扩审计_CAND7_20261026/"
)
# This round (pack formal_tail_关≥1_CAND7_20261026). Count is this round only.
CAND7_CLOSED_IDS = CAND7_IDS
CAND7_CLOSED_THIS_ROUND = 5
FORMAL_TAIL_CLOSE_PACK = (
    "/home/box/shared/legal-math-reviewer/formal_tail_关≥1_CAND7_20261026/"
)
# CAND8 true-proof v1.1 (pack formal_tail_真证CAND8_20261026). Naming is not a close.
# U01.1/U01.2 stay in the pack id set as deferred OPEN rows; theorems for them are out.
CAND8_IDS = ("U03.1", "U03.2", "U07.2", "U01.1", "U01.2")

# Later owner-authorized debt closure; never a retarget or promotion of CAND8.
POST_PIN_CLOSED_IDS = ("U03.1", "U03.2")
POST_PIN_CLOSE_PACK = "docs/formal-release/evidence/u03-debt-close-20261027"
POST_PIN_RECEIPT = POST_PIN_CLOSE_PACK + "/verification.json"
POST_PIN_OPEN_REMAINING = 12
POST_PIN_NAMES = {
    "U03.1": [
        "JurisLean.Candidates.CompilerProvenance20261027.u03_1_checked_provenance_sound",
        "JurisLean.Candidates.CompilerProvenance20261027.u03_1_checked_provenance_acyclic",
        "JurisLean.Candidates.CompilerProvenance20261027.u03_1_provenance_consumed_by_finite_closure",
        "JurisLean.Candidates.CompilerProvenance20261027.u03_1_provenance_semantic_composition",
        "JurisLean.Candidates.Final20261021.Compiler.u03_1_common_facts_closure_subset_robust",
        "JurisLean.Candidates.Final20261021.Compiler.u03_1_robust_query_strictly_beyond_common_facts",
        "JurisLean.Candidates.SourceCompilation20261027.compiler_reads_actual_extracted_output",
        "JurisLean.Candidates.SourceCompilation20261027.actual_compilation_enters_finite_closure",
        "JurisLean.Candidates.SourceCompilation20261027.interpreted_material_to_query",
    ],
    "U03.2": [
        "JurisLean.Candidates.Final20261021.Compiler.exists_closed_fuel_le_carrier",
        "JurisLean.Candidates.Final20261021.Compiler.u03_2_closed_at_finite_fuel",
        "JurisLean.Candidates.Final20261021.Compiler.u03_2_bounded_executable_closure_complete",
        "JurisLean.Candidates.Final20261021.Compiler.u03_2_computed_at_carrier_iff",
        "JurisLean.Candidates.Final20261021.Compiler.u03_2_robust_queries_exact",
        "JurisLean.Candidates.Final20261021.Compiler.u03_2_empty_interpretations_rejected",
        "JurisLean.Candidates.SourceCompilation20261027.actual_compilation_enters_finite_closure",
    ],
}
POST_PIN_DRIVER = "proofs/lean/juris_lean/JurisLean/Candidates/U03DebtClosureAudit20261027.lean"
POST_PIN_SOURCES = (
    "proofs/lean/juris_lean/JurisLean/Candidates/CompilerClosure20261026.lean",
    "proofs/lean/juris_lean/JurisLean/Candidates/CompilerProvenance20261027.lean",
    "proofs/lean/juris_lean/JurisLean/Candidates/SourceCompilation20261027.lean",
    POST_PIN_DRIVER,
)

# Each independent package keeps its own audited source, receipt and debt delta.
U01_CLOSED_IDS = ("U01.1", "U01.2", "U01.3")
U01_CLOSE_PACK = "docs/formal-release/evidence/u01-debt-close-20261027"
U01_RECEIPT = U01_CLOSE_PACK + "/verification.json"
U01_NAMES = {
    "U01.1": [
        "JurisLean.Candidates.LearningRisk20261027.u01_1_three_part_risk_decomposition",
        "JurisLean.Candidates.LearningRisk20261027.u01_1_uniform_event_erm_oracle",
        "JurisLean.Candidates.LearningRisk20261027.u01_1_total_excess_bound",
        "JurisLean.Candidates.LearningRisk20261027.u01_1_sufficient_representation_zero_gap",
        "JurisLean.Candidates.LearningRisk20261027.u01_1_collapsed_representation_half_gap",
        "JurisLean.Candidates.LearningFiniteClass20261027.row_mean_two_tail",
        "JurisLean.Candidates.LearningFiniteClass20261027.finite_class_mean_uniform",
        "JurisLean.Candidates.LearningFiniteClass20261027.u01_1_iid_empirical_risk_uniform",
        "JurisLean.Candidates.LearningFiniteClass20261027.u01_1_iid_approximate_erm"
    ],
    "U01.2": [
        "JurisLean.Candidates.LearningBridge20261027.u01_2_classification_label_bridge",
        "JurisLean.Candidates.LearningBridge20261027.u01_2_same_bounded_loss_label_bridge",
        "JurisLean.Candidates.LearningBridge20261027.u01_2_joint_failure_budget"
    ],
    "U01.3": [
        "JurisLean.Candidates.LearningBridge20261027.u01_3_same_bounded_loss_tv",
        "JurisLean.Candidates.LearningBridge20261027.u01_3_all_models_tv"
    ]
}
U01_DRIVER = "proofs/lean/juris_lean/JurisLean/Candidates/LearningTheoryAudit20261027.lean"
U01_SOURCES = (
    "proofs/lean/juris_lean/JurisLean/Candidates/LearningRisk20261027.lean",
    "proofs/lean/juris_lean/JurisLean/Candidates/LearningFiniteClass20261027.lean",
    "proofs/lean/juris_lean/JurisLean/Candidates/LearningBridge20261027.lean",
    U01_DRIVER,
)
U04_5_CLOSED_IDS = ("U04.5",)
U04_5_CLOSE_PACK = "docs/formal-release/evidence/u04-5-debt-close-20261027"
U04_5_RECEIPT = U04_5_CLOSE_PACK + "/verification.json"
U04_5_NAMES = {
    "U04.5": [
        "JurisLean.Candidates.MeasurementLikelihood20261027.joint_likelihood_chain",
        "JurisLean.Candidates.MeasurementLikelihood20261027.independent_measurement_joint_mass",
        "JurisLean.Candidates.MeasurementLikelihood20261027.independent_measurement_likelihood_multiplies",
        "JurisLean.Candidates.MeasurementLikelihood20261027.deterministic_copy_observation_event",
        "JurisLean.Candidates.MeasurementLikelihood20261027.deterministic_copy_likelihood_unchanged",
        "JurisLean.Candidates.MeasurementLikelihood20261027.zero_reference_mass_has_no_finite_ratio",
        "JurisLean.Candidates.MeasurementLikelihood20261027.nondegenerate_measurement_is_not_independent_of_itself",
        "JurisLean.Candidates.ExactProbability20261027.deterministic_copy_preserves_generated_information",
        "JurisLean.Candidates.ExactProbability20261027.deterministic_copy_keeps_integrable_conditional_expectation"
    ]
}
U04_5_DRIVER = "proofs/lean/juris_lean/JurisLean/Candidates/MeasurementLikelihoodAudit20261027.lean"
U04_5_SOURCES = (
    "proofs/lean/juris_lean/JurisLean/Candidates/MeasurementLikelihood20261027.lean",
    "proofs/lean/juris_lean/JurisLean/Candidates/ExactProbability20261027.lean",
    U04_5_DRIVER,
)
U14_1_CLOSED_IDS = ("U14.1",)
U14_1_CLOSE_PACK = "docs/formal-release/evidence/u14-1-debt-close-20261028"
U14_1_RECEIPT = U14_1_CLOSE_PACK + "/verification.json"
U14_1_NAMES = {
    "U14.1": [
        "JurisLean.Candidates.ProtectedFeedback20261027.protected_iid_joint_event",
        "JurisLean.Candidates.ProtectedFeedback20261027.actual_protected_evaluation_confidence",
        "JurisLean.Candidates.ProtectedFeedback20261027.bounds_gate_on_joint_event_preserves_each_risk",
        "JurisLean.Candidates.ProtectedFeedback20261027.strict_bounds_prove_strict_improvement",
        "JurisLean.Candidates.ProtectedFeedback20261027.observed_improvement_is_not_certified_improvement",
        "JurisLean.Candidates.AdaptiveValidation20261027.predictable_failure_budget",
        "JurisLean.Candidates.AdaptiveValidation20261027.fresh_iid_history_budget",
        "JurisLean.Candidates.AdaptiveValidation20261027.sample_count_covers_radius",
        "JurisLean.Candidates.HarnessRisk20261027.finite_adaptive_union_bound",
        "JurisLean.Candidates.AdaptiveRoundLedger20261027.assessed_load_comes_from_actual_activation",
        "JurisLean.Candidates.AdaptiveRoundLedger20261027.arbitrary_finite_round_actions_keep_budget",
        "JurisLean.Candidates.ValidatedFeedbackLoad20261027.loaded_package_is_actual_written_readback",
        "JurisLean.Candidates.ValidatedFeedbackLoad20261027.actual_loaded_risk_follows_computed_domain_bounds",
        "JurisLean.Candidates.ValidatedFeedbackLoad20261027.newly_loaded_model_is_next_actual_parent",
        "JurisLean.Candidates.BusinessFeedbackLoop20261027.next_action_reads_actual_assessment_post",
    ]
}
U14_1_DRIVER = "proofs/lean/juris_lean/JurisLean/Candidates/U14_1DebtClosureAudit20261028.lean"
U14_1_SOURCES = (
    "proofs/lean/juris_lean/JurisLean/Candidates/ProtectedFeedback20261027.lean",
    "proofs/lean/juris_lean/JurisLean/Candidates/AdaptiveValidation20261027.lean",
    "proofs/lean/juris_lean/JurisLean/Candidates/HarnessRisk20261027.lean",
    "proofs/lean/juris_lean/JurisLean/Candidates/AdaptiveRoundLedger20261027.lean",
    "proofs/lean/juris_lean/JurisLean/Candidates/ValidatedFeedbackLoad20261027.lean",
    "proofs/lean/juris_lean/JurisLean/Candidates/BusinessFeedbackLoop20261027.lean",
    U14_1_DRIVER,
)
U13_3_CLOSED_IDS = ("U13.3",)
U13_3_CLOSE_PACK = "docs/formal-release/evidence/u13-3-debt-close-20261028"
U13_3_RECEIPT = U13_3_CLOSE_PACK + "/verification.json"
U13_3_NAMES = {
    "U13.3": [
        "JurisLean.Candidates.Final20261021.RSI.u13_3_representation_transfer",
        "JurisLean.Candidates.Final20261021.RSI.u13_1_noninterference",
        "JurisLean.Candidates.LearningBoundary20261027.pointWeight_is_probability",
        "JurisLean.Candidates.LearningBoundary20261027.u01_3_two_worlds_same_training_uncontrolled_deployment",
        "JurisLean.Candidates.U13_3DebtClosureAudit20261028.same_loss_risk_under_used_inverse",
        "JurisLean.Candidates.Final20261021.RSI.u13_4_missing_checkpoint_no_default",
    ]
}
U13_3_DRIVER = "proofs/lean/juris_lean/JurisLean/Candidates/U13_3DebtClosureAudit20261028.lean"
U13_3_SOURCES = (
    "proofs/lean/juris_lean/JurisLean/Candidates/Final20261021/RSI.lean",
    "proofs/lean/juris_lean/JurisLean/Candidates/LearningBoundary20261027.lean",
    "proofs/lean/juris_lean/JurisLean/Candidates/LearningBridge20261027.lean",
    U13_3_DRIVER,
)
U12_4_CLOSED_IDS = ("U12.4",)
U12_4_CLOSE_PACK = "docs/formal-release/evidence/u12-4-debt-close-20261029"
U12_4_RECEIPT = U12_4_CLOSE_PACK + "/verification.json"
U12_4_NAMES = {
    "U12.4": [
        "JurisLean.Candidates.Final20261021.Policy.u12_4_signal_vs_incentive",
        "JurisLean.Candidates.Final20261021.Policy.distinguishable_signal_insufficient",
        "JurisLean.Candidates.PolicyResponse20261027.finite_response_payoffs",
        "JurisLean.Candidates.PolicyResponse20261027.score_only_cannot_distinguish_preparation",
        "JurisLean.Candidates.U12_4FrozenAuditModel20261029.frozen_audit_model_acceptance",
    ]
}
U12_4_DRIVER = "proofs/lean/juris_lean/JurisLean/Candidates/U12_4FrozenAuditModel20261029.lean"
U12_4_SOURCES = (
    "proofs/lean/juris_lean/JurisLean/Candidates/Final20261021/Policy.lean",
    "proofs/lean/juris_lean/JurisLean/Candidates/PolicyResponse20261027.lean",
    U12_4_DRIVER,
)
U07_2_CLOSED_IDS = ("U07.2",)
U07_2_CLOSE_PACK = "docs/formal-release/evidence/u07-2-debt-close-20261029"
U07_2_RECEIPT = U07_2_CLOSE_PACK + "/verification.json"
U07_2_NAMES = {
    "U07.2": [
        "JurisLean.Candidates.U07_2JointObject20261029.actual_source_has_joint_object",
        "JurisLean.Candidates.Final20261021.Representation.u07_2_common_fiber_nonempty",
        "JurisLean.Candidates.Final20261021.Representation.n07_2_incompatible_fiber",
        "JurisLean.Candidates.SourceStages20261027.public_model_consumes_the_actual_stage_frame",
        "JurisLean.Candidates.SourceStages20261027.four_stages_use_actual_previous_output",
        "JurisLean.Candidates.SourceStages20261027.successful_source_stages_conserve",
        "JurisLean.Seams.unified_legal_derivation_on_declared_fragment",
    ]
}
U07_2_DRIVER = "proofs/lean/juris_lean/JurisLean/Candidates/U07_2JointObject20261029.lean"
U07_2_SOURCES = (
    U07_2_DRIVER,
    "proofs/lean/juris_lean/JurisLean/Candidates/Final20261021/Representation.lean",
    "proofs/lean/juris_lean/JurisLean/Candidates/SourceStages20261027.lean",
    "proofs/lean/juris_lean/JurisLean/Seams/Unified.lean",
)
U07_3_CLOSED_IDS = ("U07.3",)
U07_3_CLOSE_PACK = "docs/formal-release/evidence/u07-3-debt-close-20261029"
U07_3_RECEIPT = U07_3_CLOSE_PACK + "/verification.json"
U07_3_NAMES = {
    "U07.3": [
        "JurisLean.Candidates.U07_3FixedBindingAudit20261029.fixed_binding_model_projection_unique",
        "JurisLean.Candidates.U07_3FixedBindingAudit20261029.amount_does_not_identify_payment_fields",
        "JurisLean.Candidates.U07_3FixedBindingAudit20261029.fixed_binding_boundary_examples",
        "JurisLean.Candidates.U07_3FixedBindingAudit20261029.actual_record_and_binding_interpretation",
        "JurisLean.Candidates.U07_3FixedBindingAudit20261029.actual_source_model_projection_unique",
        "JurisLean.Candidates.U07_3FixedBindingAudit20261029.same_material_record_do_not_determine_semantics",
        "JurisLean.Candidates.Final20261021.Representation.u07_3_projection_unique_under_fixed_binding",
        "JurisLean.Candidates.SourceStages20261027.deterministic_binding_data_unique",
        "JurisLean.Candidates.SourceStages20261027.exact_nat_bridge_is_unique",
        "JurisLean.Candidates.U07_2JointObject20261029.actual_source_has_joint_object",
        "JurisLean.Candidates.SourceStages20261027.static_source_semantic_and_quantity_bridge",
        "JurisLean.Candidates.SourceCompilation20261027.extracted_view_is_exact_selected_payload",
    ]
}
U07_3_DRIVER = "proofs/lean/juris_lean/JurisLean/Candidates/U07_3FixedBindingAudit20261029.lean"
U07_3_SOURCES = (
    U07_3_DRIVER,
    "proofs/lean/juris_lean/JurisLean/Candidates/Final20261021/Representation.lean",
    "proofs/lean/juris_lean/JurisLean/Candidates/SourceStages20261027.lean",
    U07_2_DRIVER,
    "proofs/lean/juris_lean/JurisLean/Candidates/SourceCompilation20261027.lean",
)
U02_1_CLOSED_IDS = ("U02.1",)
U02_1_CLOSE_PACK = "docs/formal-release/evidence/u02-1-debt-close-20261029"
U02_1_RECEIPT = U02_1_CLOSE_PACK + "/verification.json"
U02_1_NAMES = {
    "U02.1": [
        "JurisLean.Candidates.U02_1ActualPipeline20261029.actual_payment_pipeline_preserves_invariant",
        "JurisLean.Candidates.U02_1ActualPipeline20261029.actual_closed_pipeline_refines_gate",
        "JurisLean.Candidates.U02_1ActualPipeline20261029.actual_pipeline_refines_gate",
        "JurisLean.Candidates.U02_1ActualPipeline20261029.finite_failure_and_completion_boundaries",
        "JurisLean.Candidates.Final20261021.Harness.u02_1_gate_sound_under_Ke",
        "JurisLean.Candidates.Final20261021.Harness.u02_3_finite_gate_enumeration",
        "JurisLean.Candidates.Final20261021.Decision.u06_3_decision_respects_allowed",
        "JurisLean.Candidates.Final20261021.Trace.initial_invariant",
        "JurisLean.Candidates.Final20261021.Trace.step_preserves",
        "JurisLean.Candidates.Final20261021.Trace.u10_2_committed_executor_is_step",
        "JurisLean.Candidates.Final20261021.Trace.u10_2_known_executor_post_preserves",
        "JurisLean.Candidates.Final20261021.Pipeline.u10_1_authorized_refresh_is_step",
    ]
}
U02_1_DRIVER = "proofs/lean/juris_lean/JurisLean/Candidates/U02_1ActualPipeline20261029.lean"
U02_1_SOURCES = (
    U02_1_DRIVER,
    "proofs/lean/juris_lean/JurisLean/Candidates/Final20261021/Harness.lean",
    "proofs/lean/juris_lean/JurisLean/Candidates/Final20261021/Decision.lean",
    "proofs/lean/juris_lean/JurisLean/Candidates/Final20261021/Trace.lean",
    "proofs/lean/juris_lean/JurisLean/Candidates/Final20261021/Pipeline.lean",
)
U04_2_CLOSED_IDS = ("U04.2",)
U04_2_CLOSE_PACK = "docs/formal-release/evidence/u04-2-debt-close-20261029"
U04_2_RECEIPT = U04_2_CLOSE_PACK + "/verification.json"
U04_2_NAMES = {
    "U04.2": [
        "JurisLean.Candidates.ExactProbability20261027.supplied_enclosure_has_explicit_width_bound",
        "JurisLean.Seams.UnifiedNeedlesS3a.betaInt_eq",
        "JurisLean.Candidates.U04_2SharpConditioning20261029.frozen_enclosure_width",
        "JurisLean.Candidates.U04_2SharpConditioning20261029.beta_two_three_half",
        "JurisLean.Candidates.U04_2SharpConditioning20261029.three_event_bounds",
        "JurisLean.Candidates.U04_2SharpConditioning20261029.three_event_sharp_realization",
        "JurisLean.Candidates.U04_2SharpConditioning20261029.three_event_identified_interval",
        "JurisLean.Candidates.U04_2SharpConditioning20261029.three_event_endpoints",
        "JurisLean.Candidates.U04_2SharpConditioning20261029.contaminated_real",
        "JurisLean.Candidates.U04_2SharpConditioning20261029.contaminated_probability",
        "JurisLean.Candidates.U04_2SharpConditioning20261029.compatible_law_mixture",
        "JurisLean.Candidates.U04_2SharpConditioning20261029.conditional_contamination_bound",
        "JurisLean.Candidates.U04_2SharpConditioning20261029.conditional_contamination_zero_component",
        "JurisLean.Candidates.U04_2SharpConditioning20261029.conditioning_amplification_example",
        "JurisLean.Candidates.U04_2SharpConditioning20261029.invalid_conditioning_and_enclosure_inputs",
    ]
}
U04_2_DRIVER = "proofs/lean/juris_lean/JurisLean/Candidates/U04_2SharpConditioning20261029.lean"
U04_2_SOURCES = (
    U04_2_DRIVER,
    "proofs/lean/juris_lean/JurisLean/Candidates/ExactProbability20261027.lean",
    "proofs/lean/juris_lean/JurisLean/Seams/UnifiedNeedlesS3a.lean",
)
U06_1_CLOSED_IDS = ("U06.1",)
U06_1_CLOSE_PACK = "docs/formal-release/evidence/u06-1-debt-close-20261030"
U06_1_RECEIPT = U06_1_CLOSE_PACK + "/verification.json"
U06_1_NAMES = {
    "U06.1": [
        "JurisLean.Candidates.U06_1FiniteBellman20261030.terminal_and_empty_action",
        "JurisLean.Candidates.U06_1FiniteBellman20261030.policy_value_le_bellman",
        "JurisLean.Candidates.U06_1FiniteBellman20261030.greedy_step",
        "JurisLean.Candidates.U06_1FiniteBellman20261030.greedy_value_eq_bellman",
        "JurisLean.Candidates.U06_1FiniteBellman20261030.bellman_full_policy_optimum",
        "JurisLean.Candidates.U06_1FiniteBellman20261030.trajectory_weight_nonneg",
        "JurisLean.Candidates.U06_1FiniteBellman20261030.trajectory_weight_one",
        "JurisLean.Candidates.U06_1FiniteBellman20261030.trajectory_law_mass",
        "JurisLean.Candidates.U06_1FiniteBellman20261030.trajectory_expectation_eq_policy_value",
        "JurisLean.Candidates.U06_1FiniteBellman20261030.bellman_optimum_of_actual_trajectory_expectation",
        "JurisLean.Candidates.U06_1FiniteBellman20261030.policy_value_sub",
        "JurisLean.Candidates.U06_1FiniteBellman20261030.cost_counted_once",
        "JurisLean.Candidates.U06_1FiniteBellman20261030.nonrectangular_bellman_counterexample",
        "JurisLean.Candidates.Final20261021.Decision.u06_1_value_of_free_information",
    ]
}
U06_1_DRIVER = "proofs/lean/juris_lean/JurisLean/Candidates/U06_1FiniteBellman20261030.lean"
U06_1_SOURCES = (
    U06_1_DRIVER,
    "proofs/lean/juris_lean/JurisLean/Candidates/Final20261021/Decision.lean",
)

U06_2_CLOSED_IDS = ("U06.2",)
U06_2_CLOSE_PACK = "docs/formal-release/evidence/u06-2-debt-close-20261030"
U06_2_RECEIPT = U06_2_CLOSE_PACK + "/verification.json"
U06_2_DRIVER = "proofs/lean/juris_lean/JurisLean/Candidates/U06_2EquilibriumTransfer20261030.lean"
U06_2_NAMES = {
    "U06.2": [
        "JurisLean.Candidates.U06_2EquilibriumTransfer20261030.finite_expect_disturbance",
        "JurisLean.Candidates.U06_2EquilibriumTransfer20261030.finite_expect_affine",
        "JurisLean.Candidates.U06_2EquilibriumTransfer20261030.finite_expect_positiveAffine_preference",
        "JurisLean.Candidates.U06_2EquilibriumTransfer20261030.product_pmf_equilibrium_transfer",
        "JurisLean.Candidates.U06_2EquilibriumTransfer20261030.equiv_deviation_equilibrium_transfer",
        "JurisLean.Candidates.U06_2EquilibriumTransfer20261030.legalGame_mixedExtension_expect",
        "JurisLean.Candidates.U06_2EquilibriumTransfer20261030.legalGame_mixed_equilibrium_transfer",
        "JurisLean.Candidates.U06_2EquilibriumTransfer20261030.legalGame_mixedExtension_affine",
        "JurisLean.Candidates.U06_2EquilibriumTransfer20261030.legalGame_positiveAffine_bestResponse",
        "JurisLean.Candidates.U06_2EquilibriumTransfer20261030.added_action_counterexample",
        "JurisLean.Candidates.U06_2EquilibriumTransfer20261030.strictMono_expected_preference_reversal",
        "JurisLean.Candidates.Final20261021.Decision.u06_2_approx_equilibrium_transfer",
        "JurisLean.Seams.UnifiedEquilExist.legalGame_mixedExtension_eu",
        "JurisLean.Candidates.U06_2EquilibriumTransfer20261030.bargainProfileEquiv_update",
        "JurisLean.Candidates.U06_2EquilibriumTransfer20261030.bargain_allowedDeviation_iff",
        "JurisLean.Candidates.U06_2EquilibriumTransfer20261030.bargain_actions_preserved",
        "JurisLean.Candidates.U06_2EquilibriumTransfer20261030.bargain_trace_terminal",
        "JurisLean.Candidates.U06_2EquilibriumTransfer20261030.bargain_trace_preserved",
        "JurisLean.Candidates.U06_2EquilibriumTransfer20261030.bargain_perfect_information",
        "JurisLean.Candidates.U06_2EquilibriumTransfer20261030.bargain_publicInfo_preserved",
        "JurisLean.Candidates.U06_2EquilibriumTransfer20261030.bargain_deterministic_kernel_preserved",
        "JurisLean.Candidates.U06_2EquilibriumTransfer20261030.bargain_delay_loss_formula",
        "JurisLean.Candidates.U06_2EquilibriumTransfer20261030.bargain_ledger_values",
        "JurisLean.Candidates.U06_2EquilibriumTransfer20261030.bargain_ledger_payoff_eq",
        "JurisLean.Candidates.U06_2EquilibriumTransfer20261030.bargain_profile_payoff_eq",
        "JurisLean.Candidates.U06_2EquilibriumTransfer20261030.bargain_games_eq",
        "JurisLean.Candidates.U06_2EquilibriumTransfer20261030.bargain_treeGame_eu",
        "JurisLean.Candidates.U06_2EquilibriumTransfer20261030.bargain_abstractGame_eu",
        "JurisLean.Candidates.U06_2EquilibriumTransfer20261030.bargain_bi_profile_payoff",
        "JurisLean.Candidates.U06_2EquilibriumTransfer20261030.bargain_bi_all_deviations_nonpositive",
        "JurisLean.Candidates.U06_2EquilibriumTransfer20261030.bargain_equilibrium_transfer_instance",
        "JurisLean.Candidates.U06_2EquilibriumTransfer20261030.bargain_mixed_transfer_instance",
    ]
}
U06_2_SOURCES = (
    U06_2_DRIVER,
    "proofs/lean/juris_lean/JurisLean/Candidates/Final20261021/Decision.lean",
    "proofs/lean/juris_lean/JurisLean/Seams/UnifiedEquilExist.lean",
    "proofs/lean/juris_lean/JurisLean/Seams/UnifiedW4Games.lean",
)

U12_3_CLOSED_IDS = ("U12.3",)
U12_3_CLOSE_PACK = "docs/formal-release/evidence/u12-3-debt-close-20261030"
U12_3_RECEIPT = U12_3_CLOSE_PACK + "/verification.json"
U12_3_DRIVER = "proofs/lean/juris_lean/JurisLean/Candidates/U12_3PolicyLearningAudit20261030.lean"
U12_3_NAMES = {
    "U12.3": [
        "JurisLean.Candidates.U12_3MeasuredPolicyBridge20261030.frozenPolicyAtom_probability",
        "JurisLean.Candidates.U12_3MeasuredPolicyBridge20261030.actual_policy_score_measurable",
        "JurisLean.Candidates.U12_3MeasuredPolicyBridge20261030.actual_policy_score_integrable_and_mean",
        "JurisLean.Candidates.U12_3MeasuredPolicyBridge20261030.policyOptimizationGap_dominates",
        "JurisLean.Candidates.U12_3MeasuredPolicyBridge20261030.actual_find_policy_oracle_on_uniform_event",
        "JurisLean.Candidates.U12_3MeasuredPolicyBridge20261030.actual_find_policy_oracle_probability",
        "JurisLean.Candidates.U12_3MeasuredPolicyBridge20261030.actual_find_frozen_policyValue_probability",
        "JurisLean.Candidates.U12_3MeasuredPolicyBridge20261030.clipped_weighted_expectation_exact",
        "JurisLean.Candidates.U12_3MeasuredPolicyBridge20261030.actual_policy_clipping_bias",
        "JurisLean.Candidates.U12_3MeasuredPolicyBridge20261030.zero_bound_policy_scores_and_regret",
        "JurisLean.Candidates.U12_3MARSequential20261030.finiteMARRow_factorization",
        "JurisLean.Candidates.U12_3MARSequential20261030.mar_generated_row_independent",
        "JurisLean.Candidates.U12_3MARSequential20261030.mar_weighted_sum",
        "JurisLean.Candidates.U12_3MARSequential20261030.mar_visible_score_expectation",
        "JurisLean.Candidates.U12_3MARSequential20261030.mar_visible_score_integral",
        "JurisLean.Candidates.U12_3MARSequential20261030.mar_reported_score_joint_weight",
        "JurisLean.Candidates.PolicyEvaluation20261027.bounded_policy_score_uniform",
        "JurisLean.Candidates.PolicyEvaluation20261027.empirical_policy_winner_regret",
        "JurisLean.Candidates.PolicyEvaluation20261027.bounded_policy_winner_probability",
        "JurisLean.Candidates.PolicyEvaluation20261027.finite_policy_ipw",
        "JurisLean.Candidates.Final20261021.Policy.u12_1_finite_ipw",
        "JurisLean.Candidates.Final20261021.Policy.u12_3_clipped_bias",
        "JurisLean.Candidates.PolicyEvaluation20261027.rational_clipping_loss",
        "JurisLean.Candidates.PolicyEvaluation20261027.finite_clipping_bias_bound",
        "JurisLean.Candidates.LearningRisk20261027.u01_1_uniform_event_erm_oracle",
        "JurisLean.Candidates.LearningFiniteClass20261027.u01_1_iid_approximate_erm",
        "JurisLean.Candidates.LearningERM20261027.empiricalScore_cast",
        "JurisLean.Candidates.MeasuredPolicy20261027.supported_scores_are_bounded",
        "JurisLean.Candidates.MeasuredPolicy20261027.selected_policy_reads_numeric_bounds_and_permission",
        "JurisLean.Candidates.MeasuredPolicy20261027.actual_policy_advice_confidence",
        "JurisLean.Candidates.U12_3SequentialFinite20261030.sequentialLaw_step_mass",
        "JurisLean.Candidates.U12_3SequentialFinite20261030.sequential_mass_transport",
        "JurisLean.Candidates.U12_3SequentialFinite20261030.sequential_expectation_transport",
        "JurisLean.Candidates.U12_3SequentialFinite20261030.sequential_integral_transport",
    ]
}
U12_3_OBJECT_CHECKS = (
    "JurisLean.Candidates.U12_3MeasuredPolicyBridge20261030.frozenPolicyAtom",
    "JurisLean.Candidates.U12_3MeasuredPolicyBridge20261030.frozenPolicyJointPMF",
    "JurisLean.Candidates.U12_3MeasuredPolicyBridge20261030.policyOptimizationGap",
    "JurisLean.Candidates.U12_3MARSequential20261030.recordingMass",
    "JurisLean.Candidates.U12_3MARSequential20261030.finiteMARRow",
    "JurisLean.Candidates.U12_3MARSequential20261030.MARWorld",
    "JurisLean.Candidates.U12_3MARSequential20261030.MARVisible",
    "JurisLean.Candidates.U12_3MARSequential20261030.marReport",
    "JurisLean.Candidates.U12_3MARSequential20261030.marVisibleLaw",
    "JurisLean.Candidates.U12_3MARSequential20261030.marVisibleScore",
    "JurisLean.Candidates.U12_3MARSequential20261030.marWorldLaw",
    "JurisLean.Candidates.U12_3SequentialFinite20261030.SequentialHistory",
    "JurisLean.Candidates.U12_3SequentialFinite20261030.sequentialHistoryFintype",
    "JurisLean.Candidates.U12_3SequentialFinite20261030.SequentialPolicy",
    "JurisLean.Candidates.U12_3SequentialFinite20261030.SequentialKernel",
    "JurisLean.Candidates.U12_3SequentialFinite20261030.sequentialLaw",
    "JurisLean.Candidates.U12_3SequentialFinite20261030.sequentialRatio",
    "JurisLean.Candidates.U12_3SequentialFinite20261030.sequentialSupported",
)
U12_3_DRIVER_SOURCES = (
    "proofs/lean/juris_lean/JurisLean/Candidates/U12_3MeasuredPolicyBridge20261030.lean",
    "proofs/lean/juris_lean/JurisLean/Candidates/U12_3MARSequential20261030.lean",
    "proofs/lean/juris_lean/JurisLean/Candidates/U12_3SequentialFinite20261030.lean",
)
U12_3_SOURCES = (
    U12_3_DRIVER,
    *U12_3_DRIVER_SOURCES,
    "proofs/lean/juris_lean/JurisLean/Candidates/PolicyEvaluation20261027.lean",
    "proofs/lean/juris_lean/JurisLean/Candidates/Final20261021/Policy.lean",
    "proofs/lean/juris_lean/JurisLean/Candidates/LearningRisk20261027.lean",
    "proofs/lean/juris_lean/JurisLean/Candidates/LearningFiniteClass20261027.lean",
    "proofs/lean/juris_lean/JurisLean/Candidates/LearningERM20261027.lean",
    "proofs/lean/juris_lean/JurisLean/Candidates/MeasuredPolicy20261027.lean",
)

U13_4_CLOSED_IDS = ("U13.4",)
U13_4_CLOSE_PACK = "docs/formal-release/evidence/u13-4-debt-close-20261030"
U13_4_RECEIPT = U13_4_CLOSE_PACK + "/verification.json"
U13_4_DRIVER = "proofs/lean/juris_lean/JurisLean/Candidates/U13_4ColdStartFallbackAudit20261030.lean"
U13_4_NAMES = {
    "U13.4": [
        "JurisLean.Candidates.U13_4ColdStartFallback20261030.audited_success_reads_actual_inputs",
        "JurisLean.Candidates.U13_4ColdStartFallback20261030.prior_success_is_declared",
        "JurisLean.Candidates.U13_4ColdStartFallback20261030.description_success_reads_measurements",
        "JurisLean.Candidates.U13_4ColdStartFallback20261030.sample_success_reads_actual_mean",
        "JurisLean.Candidates.U13_4ColdStartFallback20261030.selected_prediction_has_executed_source",
        "JurisLean.Candidates.U13_4ColdStartFallback20261030.missing_personal_preserves_fallbacks",
        "JurisLean.Candidates.U13_4ColdStartFallback20261030.no_valid_source_unknown",
        "JurisLean.Candidates.U13_4ColdStartFallback20261030.normative_query_uses_only_G",
        "JurisLean.Candidates.U13_4ColdStartFallback20261030.audited_prediction_risk_under_existing_conditions",
        "JurisLean.Candidates.U13_4ColdStartFallback20261030.sample_prediction_error_under_existing_conditions",
        "JurisLean.Candidates.U13_4ColdStartFallback20261030.original_fee_service_example",
        "JurisLean.Candidates.U13_4ColdStartFallback20261030.original_unknown_win_rate_service_example",
        "JurisLean.Candidates.Final20261021.RSI.u13_1_noninterference",
        "JurisLean.Candidates.Final20261021.RSI.u13_4_missing_checkpoint_no_default",
        "JurisLean.Candidates.SampleCalibrationConsumer20261027.prediction_reads_actual_fitted_table",
        "JurisLean.Candidates.SampleCalibrationConsumer20261027.actual_certificate_consumes_population_risk_bound",
        "JurisLean.Candidates.SampleCalibrationConsumer20261027.radius_verification_sound",
        "JurisLean.Candidates.PolicyEvaluation20261027.bounded_policy_score_uniform",
        "JurisLean.Candidates.LearningBoundary20261027.u01_3_two_worlds_same_training_uncontrolled_deployment",
    ]
}
U13_4_OBJECT_CHECKS = (
    "JurisLean.Candidates.U13_4ColdStartFallback20261030.Query",
    "JurisLean.Candidates.U13_4ColdStartFallback20261030.ScopeBasis",
    "JurisLean.Candidates.U13_4ColdStartFallback20261030.basisMatches",
    "JurisLean.Candidates.U13_4ColdStartFallback20261030.queryCompatible",
    "JurisLean.Candidates.U13_4ColdStartFallback20261030.ModelSource",
    "JurisLean.Candidates.U13_4ColdStartFallback20261030.PriorSource",
    "JurisLean.Candidates.U13_4ColdStartFallback20261030.DataSource",
    "JurisLean.Candidates.U13_4ColdStartFallback20261030.Prediction",
    "JurisLean.Candidates.U13_4ColdStartFallback20261030.predictionValue",
    "JurisLean.Candidates.U13_4ColdStartFallback20261030.Description",
    "JurisLean.Candidates.U13_4ColdStartFallback20261030.Output",
    "JurisLean.Candidates.U13_4ColdStartFallback20261030.auditProduction",
    "JurisLean.Candidates.U13_4ColdStartFallback20261030.auditedReady",
    "JurisLean.Candidates.U13_4ColdStartFallback20261030.auditedPrediction",
    "JurisLean.Candidates.U13_4ColdStartFallback20261030.priorPrediction",
    "JurisLean.Candidates.U13_4ColdStartFallback20261030.dataReady",
    "JurisLean.Candidates.U13_4ColdStartFallback20261030.dataValues",
    "JurisLean.Candidates.U13_4ColdStartFallback20261030.descriptionService",
    "JurisLean.Candidates.U13_4ColdStartFallback20261030.samplePrediction",
    "JurisLean.Candidates.U13_4ColdStartFallback20261030.sourceAttempts",
    "JurisLean.Candidates.U13_4ColdStartFallback20261030.forecastService",
    "JurisLean.Candidates.U13_4ColdStartFallback20261030.normativeService",
    "JurisLean.Candidates.U13_4ColdStartFallback20261030.service",
)
U13_4_SOURCES = (
    "proofs/lean/juris_lean/JurisLean/Candidates/U13_4ColdStartFallback20261030.lean",
    U13_4_DRIVER,
    "proofs/lean/juris_lean/JurisLean/Candidates/Final20261021/RSI.lean",
    "proofs/lean/juris_lean/JurisLean/Candidates/LearningBoundary20261027.lean",
    "proofs/lean/juris_lean/JurisLean/Candidates/SampleCalibrationConsumer20261027.lean",
    "proofs/lean/juris_lean/JurisLean/Candidates/PolicyEvaluation20261027.lean",
    "proofs/lean/juris_lean/JurisLean/Candidates/U13_3DebtClosureAudit20261028.lean",
)

U12_1_CLOSED_IDS = ("U12.1",)
U12_1_CLOSE_PACK = "docs/formal-release/evidence/u12-1-debt-close-20261030"
U12_1_RECEIPT = U12_1_CLOSE_PACK + "/verification.json"
U12_1_DRIVER = "proofs/lean/juris_lean/JurisLean/Candidates/U12_1DebtClosureAudit20261030.lean"
U12_1_NAMES = {
    "U12.1": [
        "JurisLean.Candidates.U12_1CausalPolicyBridge20261030.finite_action_causal_ipw",
        "JurisLean.Candidates.U12_1CausalPolicyBridge20261030.actual_measured_policy_causal_value",
        "JurisLean.Candidates.PolicyEvaluation20261027.original_policy_values_and_clipping",
        "JurisLean.Candidates.PolicyEvaluation20261027.original_support_gap_sharp",
        "JurisLean.Candidates.PolicyEvaluation20261027.support_gap_endpoints_observationally_compatible",
        "JurisLean.Candidates.U12_3MeasuredPolicyBridge20261030.clipped_weighted_expectation_exact",
        "JurisLean.Candidates.MeasuredPolicy20261027.selected_policy_reads_numeric_bounds_and_permission",
        "JurisLean.Candidates.MeasuredPolicy20261027.actual_policy_advice_confidence",
        "JurisLean.Candidates.MeasuredPolicy20261027.advice_consumes_actual_measured_values_and_allowed_policy",
        "JurisLean.Candidates.MeasuredPolicy20261027.feedback_reads_actual_external_label",
        "JurisLean.Candidates.MeasuredPolicy20261027.measured_feedback_prepares_from_actual_loaded_and_journal",
        "JurisLean.Candidates.MeasuredPolicy20261027.measured_data_update_keeps_rules_loaded_and_budget",
        "JurisLean.Candidates.Final20261021.RSI.u13_1_noninterference",
        "JurisLean.Candidates.U11_1OriginalInstances20261030.original11_6_same_behavior_different_constraints",
        "JurisLean.Candidates.BusinessMeasurement20261027.measurement_reads_actual_state_and_rows",
        "JurisLean.Candidates.BusinessMeasurement20261027.negative_requires_complete_closed_window",
        "JurisLean.Candidates.BusinessMeasurement20261027.performance_magnitude_is_actual_allocation",
        "JurisLean.Candidates.U12_1OriginalInstances20261030.original12_3_real_support_range",
        "JurisLean.Candidates.U12_1OriginalInstances20261030.original12_6_behavior_only_cannot_recover_both",
        "JurisLean.Candidates.U12_1OriginalInstances20261030.original12_6_proxy_gain_true_loss",
    ]
}
U12_1_OBJECT_CHECKS = (
    "JurisLean.Candidates.U12_1CausalPolicyBridge20261030.JointOutcome",
    "JurisLean.Candidates.U12_1CausalPolicyBridge20261030.jointObservation",
    "JurisLean.Candidates.U12_1CausalPolicyBridge20261030.actualConditional",
    "JurisLean.Candidates.U12_1CausalPolicyBridge20261030.loggingMass",
    "JurisLean.Candidates.U12_1CausalPolicyBridge20261030.causalPolicyValue",
    "JurisLean.Candidates.U12_1CausalPolicyBridge20261030.actualLoggingScore",
    "JurisLean.Candidates.U12_1CausalPolicyBridge20261030.actualConditional_markov",
)
U12_1_SOURCES = (
    U12_1_DRIVER,
    "proofs/lean/juris_lean/JurisLean/Candidates/U12_1CausalPolicyBridge20261030.lean",
    "proofs/lean/juris_lean/JurisLean/Candidates/U12_1OriginalInstances20261030.lean",
    "proofs/lean/juris_lean/JurisLean/Candidates/PolicyEvaluation20261027.lean",
    "proofs/lean/juris_lean/JurisLean/Candidates/U12_3MeasuredPolicyBridge20261030.lean",
    "proofs/lean/juris_lean/JurisLean/Candidates/MeasuredPolicy20261027.lean",
    "proofs/lean/juris_lean/JurisLean/Candidates/Final20261021/RSI.lean",
    "proofs/lean/juris_lean/JurisLean/Candidates/U11_1OriginalInstances20261030.lean",
    "proofs/lean/juris_lean/JurisLean/Candidates/BusinessMeasurement20261027.lean",
)

U10_1_CLOSED_IDS = ("U10.1",)
U10_1_CLOSE_PACK = "docs/formal-release/evidence/u10-1-debt-close-20261030"
U10_1_RECEIPT = U10_1_CLOSE_PACK + "/verification.json"
U10_1_DRIVER = "proofs/lean/juris_lean/JurisLean/Candidates/U10_1DebtClosureAudit20261030.lean"
U10_1_NAMES = {
    "U10.1": [
        "JurisLean.Candidates.U10_1RefreshRuleProtocol20261030.evaluated_rules_use_actual_environment",
        "JurisLean.Candidates.U10_1RefreshRuleProtocol20261030.continued_protocol_refines_actual_calls",
        "JurisLean.Candidates.U10_1RefreshRuleProtocol20261030.stopped_protocol_keeps_committed_refresh",
        "JurisLean.Candidates.U10_1RefreshRuleProtocol20261030.reported_protocol_post_has_actual_path",
        "JurisLean.Candidates.U10_1RefreshRuleProtocol20261030.internal_refresh_rechecks_before_continuation",
        "JurisLean.Candidates.Final20261021.Authorization.u10_1_enable_append_select_refresh_consume",
        "JurisLean.Candidates.Final20261021.Temporal.u08_1_selection_stable",
        "JurisLean.Candidates.Final20261021.Trace.u10_2_finite_trace_composition",
    ]
}
U10_1_OBJECT_CHECKS = (
    "JurisLean.Candidates.U10_1RefreshRuleProtocol20261030.evaluateCurrentRules",
    "JurisLean.Candidates.U10_1RefreshRuleProtocol20261030.ProtocolRun",
    "JurisLean.Candidates.U10_1RefreshRuleProtocol20261030.RenewalRequest",
    "JurisLean.Candidates.U10_1RefreshRuleProtocol20261030.checkRenewal",
    "JurisLean.Candidates.U10_1RefreshRuleProtocol20261030.checkedTail",
    "JurisLean.Candidates.U10_1RefreshRuleProtocol20261030.refreshEvaluateContinue",
)
U10_1_SOURCES = (
    U10_1_DRIVER,
    "proofs/lean/juris_lean/JurisLean/Candidates/U10_1RefreshRuleProtocol20261030.lean",
    "proofs/lean/juris_lean/JurisLean/Candidates/Final20261021/Authorization.lean",
    "proofs/lean/juris_lean/JurisLean/Candidates/Final20261021/Temporal.lean",
    "proofs/lean/juris_lean/JurisLean/Candidates/Final20261021/Trace.lean",
)

U01_4_CLOSED_IDS = ("U01.4",)
U01_4_CLOSE_PACK = "docs/formal-release/evidence/u01-4-original-close-20261030"
U01_4_RECEIPT = U01_4_CLOSE_PACK + "/verification.json"
U01_4_DRIVER = "proofs/lean/juris_lean/JurisLean/Candidates/U01_4OriginalClosureAudit20261030.lean"
U01_4_NAMES = {
    "U01.4": [
        "JurisLean.Candidates.LearningBoundary20261027.pointWeight_is_probability",
        "JurisLean.Candidates.LearningBoundary20261027.pointPopulationRisk_eq",
        "JurisLean.Candidates.LearningBoundary20261027.actualConstantFit_value",
        "JurisLean.Candidates.LearningBoundary20261027.u01_3_actual_fit_zero_train_one_deploy",
        "JurisLean.Candidates.LearningBoundary20261027.u01_3_two_worlds_same_training_uncontrolled_deployment",
        "JurisLean.Candidates.LearningBoundary20261027.u01_6_perfect_fit_does_not_supply_authorization",
        "JurisLean.Candidates.LearningDependence20261027.u01_4_independent_empirical_mean_variance",
        "JurisLean.Candidates.LearningDependence20261027.u01_4_copied_empirical_mean_variance",
        "JurisLean.Candidates.LearningDependence20261027.u01_4_concrete_common_cause_counterexample",
        "JurisLean.Candidates.Final20261021.Learning.grouped_unit_not_split",
    ]
}
U01_4_OBJECT_CHECKS = (
    "JurisLean.Candidates.LearningDependence20261027.FairBinary",
    "JurisLean.Candidates.LearningDependence20261027.fairCoinMeasure",
    "JurisLean.Candidates.LearningBoundary20261027.actualConstantFit",
    "JurisLean.Candidates.LearningBoundary20261027.pointPopulationRisk",
    "JurisLean.Candidates.LearningFiniteClass20261027.empiricalMean",
)
U01_4_SOURCES = (
    U01_4_DRIVER,
    "proofs/lean/juris_lean/JurisLean/Candidates/LearningBoundary20261027.lean",
    "proofs/lean/juris_lean/JurisLean/Candidates/LearningDependence20261027.lean",
    "proofs/lean/juris_lean/JurisLean/Candidates/Final20261021/Learning.lean",
    "proofs/lean/juris_lean/JurisLean/Candidates/LearningERM20261027.lean",
    "proofs/lean/juris_lean/JurisLean/Candidates/LearningRisk20261027.lean",
    "proofs/lean/juris_lean/JurisLean/Candidates/LearningFiniteClass20261027.lean",
)

U04_4_CLOSED_IDS = ("U04.4",)
U04_4_CLOSE_PACK = "docs/formal-release/evidence/u04-4-original-close-20261031"
U04_4_RECEIPT = U04_4_CLOSE_PACK + "/verification.json"
U04_4_DRIVER = "proofs/lean/juris_lean/JurisLean/Candidates/U04_4OriginalClosureAudit20261031.lean"
U04_4_NAMES = {
    "U04.4": [
        "JurisLean.Candidates.EquicorrelatedMean20261030.equicorrelated_mean_variance",
        "JurisLean.Candidates.EquicorrelatedMean20261030.equicorrelated_mean_branches",
        "JurisLean.Candidates.EquicorrelatedMean20261030.fair_coin_complement_witness",
        "JurisLean.Candidates.LearningDependence20261027.u01_4_concrete_common_cause_counterexample",
    ]
}
U04_4_OBJECT_CHECKS = (
    "JurisLean.Candidates.LearningFiniteClass20261027.empiricalMean",
    "JurisLean.Candidates.LearningDependence20261027.fairCoinMeasure",
    "JurisLean.Candidates.Final20261021.Probability.EffectiveCount",
    "JurisLean.Candidates.Final20261021.Probability.u04_4_variance_equivalent",
)
U04_4_SOURCES = (
    U04_4_DRIVER,
    "proofs/lean/juris_lean/JurisLean/Candidates/EquicorrelatedMean20261030.lean",
    "proofs/lean/juris_lean/JurisLean/Candidates/LearningDependence20261027.lean",
    "proofs/lean/juris_lean/JurisLean/Candidates/LearningFiniteClass20261027.lean",
    "proofs/lean/juris_lean/JurisLean/Candidates/Final20261021/Probability.lean",
)

U02_4_CLOSED_IDS = ("U02.4",)
U02_4_CLOSE_PACK = "docs/formal-release/evidence/u02-4-original-close-20261030"
U02_4_RECEIPT = U02_4_CLOSE_PACK + "/verification.json"
U02_4_DRIVER = "proofs/lean/juris_lean/JurisLean/Candidates/U02_4OriginalClosureAudit20261030.lean"
U02_4_NAMES = {
    "U02.4": [
        "JurisLean.Candidates.U02_4ExternalConditionRisk20261030.finite_prefix_external_condition_bound",
        "JurisLean.Candidates.U02_4ExternalConditionRisk20261030.countable_prefix_external_condition_bound",
        "JurisLean.Candidates.HarnessRisk20261027.finite_adaptive_union_bound",
        "JurisLean.Candidates.Final20261021.Harness.u02_4_unconditional_budget",
        "JurisLean.Candidates.Final20261021.Harness.u02_4_hb_not_the_marginal_bound",
        "Finset.sum_range_add",
    ]
}
U02_4_SOURCES = (
    U02_4_DRIVER,
    "proofs/lean/juris_lean/JurisLean/Candidates/U02_4ExternalConditionRisk20261030.lean",
    "proofs/lean/juris_lean/JurisLean/Candidates/HarnessRisk20261027.lean",
    "proofs/lean/juris_lean/JurisLean/Candidates/Final20261021/Harness.lean",
)

U09_2_CLOSED_IDS = ("U09.2",)
U09_2_CLOSE_PACK = "docs/formal-release/evidence/u09-2-original-close-20261030"
U09_2_RECEIPT = U09_2_CLOSE_PACK + "/verification.json"
U09_2_DRIVER = "proofs/lean/juris_lean/JurisLean/Candidates/U09_2OriginalClosureAudit20261030.lean"
U09_2_NAMES = {
    "U09.2": [
        "JurisLean.Candidates.Final20261021.Ledger.u09_2_cash_conservation",
        "JurisLean.Candidates.Final20261021.Ledger.u09_2_cash_by_account",
    ]
}
U09_2_OBJECT_CHECKS = (
    "JurisLean.Candidates.Final20261021.Ledger.cashVector",
)
U09_2_SOURCES = (
    U09_2_DRIVER,
    "proofs/lean/juris_lean/JurisLean/Candidates/Final20261021/Ledger.lean",
)

U11_1_CLOSED_IDS = ("U11.1",)
U11_1_CLOSE_PACK = "docs/formal-release/evidence/u11-1-debt-close-20261030"
U11_1_RECEIPT = U11_1_CLOSE_PACK + "/verification.json"
U11_1_DRIVER = "proofs/lean/juris_lean/JurisLean/Candidates/U11_1DebtClosureAudit20261030.lean"
U11_1_NAMES = {
    "U11.1": [
        "JurisLean.Candidates.U11_1NamedCausalBridge20261030.consistency_from_version_and_exposure",
        "JurisLean.Candidates.U11_1NamedCausalBridge20261030.observed_cell_mean_eq_potential",
        "JurisLean.Candidates.U11_1NamedCausalBridge20261030.finite_g_formula_from_conditions",
        "JurisLean.Candidates.U11_1OriginalInstances20261030.original11_2_bernoulli_prediction_checks",
        "JurisLean.Candidates.U11_1OriginalInstances20261030.original11_6_same_behavior_different_constraints",
        "JurisLean.Candidates.U11_1OriginalInstances20261030.original04_4_two_feasible_endpoints",
        "JurisLean.Candidates.U11_1OriginalInstances20261030.original04_4_mcar_recovers",
        "JurisLean.Candidates.U11_1OriginalInstances20261030.original04_4_compatible_endpoints_not_singleton",
        "JurisLean.Candidates.BusinessMeasurement20261027.measurement_reads_actual_state_and_rows",
        "JurisLean.Candidates.BusinessMeasurement20261027.negative_requires_complete_closed_window",
        "JurisLean.Candidates.BusinessMeasurement20261027.duplicate_events_refused",
        "JurisLean.Candidates.BusinessMeasurement20261027.revocation_does_not_supply_defect_measurement",
        "JurisLean.Candidates.BusinessMeasurement20261027.original_appeal_frequencies",
        "JurisLean.Candidates.BusinessMeasurement20261027.unknown_appeal_labels_have_sharp_bounds",
        "JurisLean.Candidates.BusinessMeasurement20261027.appeal_observations_cannot_identify_population_rate",
        "JurisLean.Candidates.CausalSelection20261027.full_selection_kernel_normalized",
        "JurisLean.Candidates.CausalSelection20261027.full_selection_kernel_nonnegative",
        "JurisLean.Candidates.CausalSelection20261027.selected_weight_recovery",
        "JurisLean.Candidates.CausalSelection20261027.selected_database_requires_population_normalization",
        "JurisLean.Candidates.CausalSelection20261027.selection_countermodels_have_identical_visible_law",
        "JurisLean.Candidates.CausalSelection20261027.selected_association_is_not_population_effect",
        "JurisLean.Candidates.CausalSelection20261027.no_visible_law_estimator_identifies_both",
        "JurisLean.Candidates.CausalSelection20261027.transport_requires_overlap_and_mean_stability",
        "JurisLean.Candidates.CausalSelection20261027.actual_transport_reweights_the_target",
        "JurisLean.Candidates.CausalSelection20261027.source_and_target_mix_do_not_identify_new_effect",
        "JurisLean.Candidates.PolicyEvaluation20261027.unsupported_value_bounds",
        "JurisLean.Candidates.PolicyEvaluation20261027.support_gap_endpoints_observationally_compatible",
        "JurisLean.Candidates.MeasuredPolicy20261027.measured_policy_pipeline_reads_actual_measurement",
        "JurisLean.Candidates.MeasuredPolicy20261027.advice_consumes_actual_measured_values_and_allowed_policy",
        "JurisLean.Candidates.U12_3MARSequential20261030.finiteMARRow_factorization",
        "JurisLean.Candidates.U12_3MARSequential20261030.mar_visible_score_integral",
    ]
}
U11_1_OBJECT_CHECKS = (
    "JurisLean.Candidates.U11_1NamedCausalBridge20261030.C_cons",
    "JurisLean.Candidates.U11_1NamedCausalBridge20261030.I_nointerf",
    "JurisLean.Candidates.U11_1NamedCausalBridge20261030.ownExposure",
    "JurisLean.Candidates.U11_1NamedCausalBridge20261030.ownIntervention",
    "JurisLean.Candidates.U11_1NamedCausalBridge20261030.potentialOutcome",
    "JurisLean.Candidates.U11_1NamedCausalBridge20261030.E_exch",
    "JurisLean.Candidates.U11_1NamedCausalBridge20261030.P_pos",
    "JurisLean.Candidates.U11_1NamedCausalBridge20261030.observedCellMean",
    "JurisLean.Candidates.U11_1OriginalInstances20261030.originalMissingWorld",
    "JurisLean.Candidates.U11_1OriginalInstances20261030.originalMissingReport",
    "JurisLean.Candidates.U11_1OriginalInstances20261030.originalMissingMean",
    "JurisLean.Candidates.BusinessMeasurement20261027.MeasurementDictionary",
    "JurisLean.Candidates.BusinessMeasurement20261027.MeasurementRow",
    "JurisLean.Candidates.BusinessMeasurement20261027.measureBusiness",
    "JurisLean.Candidates.MeasuredPolicy20261027.PolicyEnvironment",
    "JurisLean.Candidates.MeasuredPolicy20261027.PolicyDesignReceipt",
    "JurisLean.Candidates.MeasuredPolicy20261027.PolicyPermission",
    "JurisLean.Candidates.MeasuredPolicy20261027.runMeasurementPolicy",
    "JurisLean.Candidates.MeasuredPolicy20261027.adviseMeasured",
    "JurisLean.Candidates.U12_3MARSequential20261030.marReport",
    "JurisLean.Candidates.U12_3MARSequential20261030.marVisibleScore",
)
U11_1_SOURCES = (
    U11_1_DRIVER,
    "proofs/lean/juris_lean/JurisLean/Candidates/U11_1NamedCausalBridge20261030.lean",
    "proofs/lean/juris_lean/JurisLean/Candidates/U11_1OriginalInstances20261030.lean",
    "proofs/lean/juris_lean/JurisLean/Candidates/BusinessMeasurement20261027.lean",
    "proofs/lean/juris_lean/JurisLean/Candidates/CausalSelection20261027.lean",
    "proofs/lean/juris_lean/JurisLean/Candidates/PolicyEvaluation20261027.lean",
    "proofs/lean/juris_lean/JurisLean/Candidates/MeasuredPolicy20261027.lean",
    "proofs/lean/juris_lean/JurisLean/Candidates/U12_3MARSequential20261030.lean",
    "proofs/lean/juris_lean/JurisLean/Candidates/Final20261021/Behavior.lean",
    "proofs/lean/juris_lean/JurisLean/Candidates/Final20261021/Probability.lean",
    "proofs/lean/juris_lean/JurisLean/Seams/UnifiedNeedlesXU.lean",
)

INDEPENDENT_CLOSE_PACKS = (
    {"closed_ids": POST_PIN_CLOSED_IDS, "pack": POST_PIN_CLOSE_PACK,
     "receipt": POST_PIN_RECEIPT, "names": POST_PIN_NAMES,
     "driver": POST_PIN_DRIVER, "sources": POST_PIN_SOURCES,
     "open_before": 20, "open_after": 18},
    {"closed_ids": U01_CLOSED_IDS, "pack": U01_CLOSE_PACK,
     "receipt": U01_RECEIPT, "names": U01_NAMES,
     "driver": U01_DRIVER, "sources": U01_SOURCES,
     "open_before": 18, "open_after": 15},
    {"closed_ids": U04_5_CLOSED_IDS, "pack": U04_5_CLOSE_PACK,
     "receipt": U04_5_RECEIPT, "names": U04_5_NAMES,
     "driver": U04_5_DRIVER, "sources": U04_5_SOURCES,
     "open_before": 15, "open_after": 14},
    {"closed_ids": U14_1_CLOSED_IDS, "pack": U14_1_CLOSE_PACK,
     "receipt": U14_1_RECEIPT, "names": U14_1_NAMES,
     "driver": U14_1_DRIVER, "sources": U14_1_SOURCES,
     "open_before": 14, "open_after": 13},
    {"closed_ids": U13_3_CLOSED_IDS, "pack": U13_3_CLOSE_PACK,
     "receipt": U13_3_RECEIPT, "names": U13_3_NAMES,
     "driver": U13_3_DRIVER, "sources": U13_3_SOURCES,
     "open_before": 13, "open_after": 12},
    {"closed_ids": U12_4_CLOSED_IDS, "pack": U12_4_CLOSE_PACK,
     "receipt": U12_4_RECEIPT, "names": U12_4_NAMES,
     "driver": U12_4_DRIVER, "sources": U12_4_SOURCES,
     "open_before": 12, "open_after": 11},
    {"closed_ids": U07_2_CLOSED_IDS, "pack": U07_2_CLOSE_PACK,
     "receipt": U07_2_RECEIPT, "names": U07_2_NAMES,
     "driver": U07_2_DRIVER, "sources": U07_2_SOURCES,
     "open_before": 11, "open_after": 10},
    {"closed_ids": U07_3_CLOSED_IDS, "pack": U07_3_CLOSE_PACK,
     "receipt": U07_3_RECEIPT, "names": U07_3_NAMES,
     "driver": U07_3_DRIVER, "sources": U07_3_SOURCES,
     "open_before": 10, "open_after": 9},
    {"closed_ids": U02_1_CLOSED_IDS, "pack": U02_1_CLOSE_PACK,
     "receipt": U02_1_RECEIPT, "names": U02_1_NAMES,
     "driver": U02_1_DRIVER, "sources": U02_1_SOURCES,
     "open_before": 9, "open_after": 8},
    {"closed_ids": U04_2_CLOSED_IDS, "pack": U04_2_CLOSE_PACK,
     "receipt": U04_2_RECEIPT, "names": U04_2_NAMES,
     "driver": U04_2_DRIVER, "sources": U04_2_SOURCES,
     "open_before": 8, "open_after": 7,
     "expected_subject": "5c8cf787c1d545a0ab1e037fa793d8f6417b886e",
     "expected_run_id": 40879691794, "expected_job_id": 123467594841,
     "expected_attempt": 1, "expected_artifact_id": 12899702798,
     "expected_artifact_sha256": "1187cd23da95b79f3ffbdf90c64f99588063009dace4b6bf886ab273621c1cc2"},
    {"closed_ids": U06_1_CLOSED_IDS, "pack": U06_1_CLOSE_PACK,
     "receipt": U06_1_RECEIPT, "names": U06_1_NAMES,
     "driver": U06_1_DRIVER, "sources": U06_1_SOURCES,
     "open_before": 7, "open_after": 6,
     "expected_subject": "8340ffa6d88138b89ec9083253414d8b69e96803",
     "expected_run_id": 40919387762, "expected_job_id": 123608188128,
     "expected_attempt": 1, "expected_artifact_id": 12917367581,
     "expected_artifact_sha256": "aaf0f038397ded7d503a055245d4921d686af680d9bf7751418ad18af0b553b8"},
    {"closed_ids": U06_2_CLOSED_IDS, "pack": U06_2_CLOSE_PACK,
     "receipt": U06_2_RECEIPT, "names": U06_2_NAMES,
     "driver": U06_2_DRIVER, "sources": U06_2_SOURCES,
     "open_before": 6, "open_after": 5,
     "expected_subject": "fe9e4b689d317e75d91415ea65d701583a205929",
     "expected_run_id": 40939134896, "expected_job_id": 123677528713,
     "expected_attempt": 1, "expected_artifact_id": 12925329796,
     "expected_artifact_sha256": "46591a17cd3591eccbd2ffc912718b10b538f159a9c05f32bea2762905bd820e"},
    {"closed_ids": U12_3_CLOSED_IDS, "pack": U12_3_CLOSE_PACK,
     "receipt": U12_3_RECEIPT, "names": U12_3_NAMES,
     "driver": U12_3_DRIVER, "sources": U12_3_SOURCES,
     "object_checks": U12_3_OBJECT_CHECKS,
     "open_before": 5, "open_after": 4,
     "expected_subject": "935b1bd8420c9433c9918d53d935b0948bf51089",
     "expected_run_id": 40964036223, "expected_job_id": 123763838851,
     "expected_attempt": 1, "expected_artifact_id": 12937870526,
     "expected_artifact_sha256": "dd8a379bec390cfc92478ea5a652f57e4ffb42f049a41d94758fa16bab82a77e"},
    {"closed_ids": U13_4_CLOSED_IDS, "pack": U13_4_CLOSE_PACK,
     "receipt": U13_4_RECEIPT, "names": U13_4_NAMES,
     "driver": U13_4_DRIVER, "sources": U13_4_SOURCES,
     "object_checks": U13_4_OBJECT_CHECKS,
     "open_before": 4, "open_after": 3,
     "expected_subject": "ad4beec80456a8562a4c2a0dbf231000fb922e8d",
     "expected_run_id": 40976943681, "expected_job_id": 123807204758,
     "expected_attempt": 1, "expected_artifact_id": 12943003053,
     "expected_artifact_sha256": "c2fa2f1e56fa4ee308883e63862cda2af7307f5acaa0aa78fa209fe94c02b1ff"},
    {"closed_ids": U11_1_CLOSED_IDS, "pack": U11_1_CLOSE_PACK,
     "receipt": U11_1_RECEIPT, "names": U11_1_NAMES,
     "driver": U11_1_DRIVER, "sources": U11_1_SOURCES,
     "object_checks": U11_1_OBJECT_CHECKS,
     "open_before": 3, "open_after": 2,
     "expected_subject": "95a7cc43bfbad5c5c9ba69894c7209b9a33e730e",
     "expected_run_id": 40987962686, "expected_job_id": 123843315122,
     "expected_attempt": 1, "expected_artifact_id": 12947703490,
     "expected_artifact_sha256": "2760b9b16a43f9e4f52b315b196f7164ac42256e68c64c55111fd14b3fac6b87"},
    {"closed_ids": U12_1_CLOSED_IDS, "pack": U12_1_CLOSE_PACK,
     "receipt": U12_1_RECEIPT, "names": U12_1_NAMES,
     "driver": U12_1_DRIVER, "sources": U12_1_SOURCES,
     "object_checks": U12_1_OBJECT_CHECKS,
     "open_before": 2, "open_after": 1,
     "expected_subject": "1959afb04058afbff8495baea92ef6ac1687a577",
     "expected_run_id": 41004233670, "expected_job_id": 123895367398,
     "expected_attempt": 1, "expected_artifact_id": 12954856579,
     "expected_artifact_sha256": "0fa985ccbd5247a8bc53d2638d84a0e01256ad64b92470722e510821e5f873be"},
    {"closed_ids": U10_1_CLOSED_IDS, "pack": U10_1_CLOSE_PACK,
     "receipt": U10_1_RECEIPT, "names": U10_1_NAMES,
     "driver": U10_1_DRIVER, "sources": U10_1_SOURCES,
     "object_checks": U10_1_OBJECT_CHECKS,
     "open_before": 1, "open_after": 0,
     "expected_subject": "bf95766f1e68a82b2bda80db8712b39611233482",
     "expected_run_id": 41018909983, "expected_job_id": 123941482566,
     "expected_attempt": 1, "expected_artifact_id": 12961061530,
     "expected_artifact_sha256": "542dd8f891c9628d0ac43dfe741b7ee4efe2c86aefe75b2c20def010e796e397"},
    {"closed_ids": U02_4_CLOSED_IDS, "pack": U02_4_CLOSE_PACK,
     "receipt": U02_4_RECEIPT, "names": U02_4_NAMES,
     "driver": U02_4_DRIVER, "sources": U02_4_SOURCES,
     "open_before": 0, "open_after": 0,
     "expected_subject": "814c10b0d404eaba8848636de8169b815460d70a",
     "expected_run_id": 41062973614, "expected_job_id": 124087082984,
     "expected_attempt": 1, "expected_artifact_id": 12980527206,
     "expected_artifact_sha256": "bbbb5f89a0d9d621b1322d4d3527106cfdb131d4e057b194da6359b6fff8eef4"},
    {"closed_ids": U09_2_CLOSED_IDS, "pack": U09_2_CLOSE_PACK,
     "receipt": U09_2_RECEIPT, "names": U09_2_NAMES,
     "driver": U09_2_DRIVER, "sources": U09_2_SOURCES,
     "object_checks": U09_2_OBJECT_CHECKS,
     "open_before": 0, "open_after": 0,
     "expected_subject": "22f281620cd861ec4308b8f0745064c332e1d7c2",
     "expected_run_id": 41065859816, "expected_job_id": 124096972537,
     "expected_attempt": 1, "expected_artifact_id": 12982083685,
     "expected_artifact_sha256": "6b584289dac1cfbc781c57f3d6d4e6c8a6ef8b9b75f77719c3ae16c779e9c514"},
    {"closed_ids": U01_4_CLOSED_IDS, "pack": U01_4_CLOSE_PACK,
     "receipt": U01_4_RECEIPT, "names": U01_4_NAMES,
     "driver": U01_4_DRIVER, "sources": U01_4_SOURCES,
     "object_checks": U01_4_OBJECT_CHECKS,
     "open_before": 0, "open_after": 0,
     "expected_subject": "f80e790e6d6ecbd8449f2181433673945540e5af",
     "expected_run_id": 41081311144, "expected_job_id": 124150886815,
     "expected_attempt": 1, "expected_artifact_id": 12989961441,
     "expected_artifact_sha256": "7a311f75069f797acfeb1efb879af00dae6e1e95f29016abe5fbfa3fa55497bc"},
    {"closed_ids": U04_4_CLOSED_IDS, "pack": U04_4_CLOSE_PACK,
     "receipt": U04_4_RECEIPT, "names": U04_4_NAMES,
     "driver": U04_4_DRIVER, "sources": U04_4_SOURCES,
     "object_checks": U04_4_OBJECT_CHECKS,
     "open_before": 0, "open_after": 0,
     "expected_subject": "7dcee7f360758bebc15e7a2efc49ee76c7d97201",
     "expected_run_id": 41098286355, "expected_job_id": 124209655817,
     "expected_attempt": 1, "expected_artifact_id": 12998165175,
     "expected_artifact_sha256": "c5c898f2f1a0b6a290781885cc98b40bf01b75335a90551b3014b969acd32199"},
)
CURRENT_CLOSE_IDS = INDEPENDENT_CLOSE_PACKS[-1]["closed_ids"]
CURRENT_CLOSE_PACK = INDEPENDENT_CLOSE_PACKS[-1]["pack"]
CURRENT_CLOSE_RECEIPT = INDEPENDENT_CLOSE_PACKS[-1]["receipt"]
INDEPENDENT_CLOSED_IDS = POST_PIN_CLOSED_IDS + U01_CLOSED_IDS + U04_5_CLOSED_IDS + U14_1_CLOSED_IDS + U13_3_CLOSED_IDS + U12_4_CLOSED_IDS + U07_2_CLOSED_IDS + U07_3_CLOSED_IDS + U02_1_CLOSED_IDS + U04_2_CLOSED_IDS + U06_1_CLOSED_IDS + U06_2_CLOSED_IDS + U12_3_CLOSED_IDS + U13_4_CLOSED_IDS + U11_1_CLOSED_IDS + U12_1_CLOSED_IDS + U10_1_CLOSED_IDS + U02_4_CLOSED_IDS + U09_2_CLOSED_IDS + U01_4_CLOSED_IDS + U04_4_CLOSED_IDS
INDEPENDENT_NAMES = POST_PIN_NAMES | U01_NAMES | U04_5_NAMES | U14_1_NAMES | U13_3_NAMES | U12_4_NAMES | U07_2_NAMES | U07_3_NAMES | U02_1_NAMES | U04_2_NAMES | U06_1_NAMES | U06_2_NAMES | U12_3_NAMES | U13_4_NAMES | U11_1_NAMES | U12_1_NAMES | U10_1_NAMES | U02_4_NAMES | U09_2_NAMES | U01_4_NAMES | U04_4_NAMES
INDEPENDENT_RECEIPTS = {
    clause: pack["receipt"] for pack in INDEPENDENT_CLOSE_PACKS for clause in pack["closed_ids"]
}

FORMAL_TAIL_CAND8_PACK = (
    "/home/box/shared/legal-math-reviewer/formal_tail_真证CAND8_20261026/"
)
# Theorems in CANDIDATE_MODULE. None is in the tip-pin audit. None closes a row.
# Order inside each clause is source order. Archive order concatenates them.
PROVE_CANDIDATES: dict[str, list[str]] = {
    "U06.4": [
        "u06_4_increasing_threshold_above_one_excludes",
        "u06_4_increasing_threshold_at_most_zero_includes",
        "u06_4_decreasing_threshold_below_zero_excludes",
        "u06_4_decreasing_threshold_at_least_one_includes",
        "u06_4_increasing_unit_interval_above_one_is_empty",
        "u06_4_increasing_unit_interval_at_most_zero_is_full",
        "u06_4_decreasing_unit_interval_below_zero_is_empty",
        "u06_4_decreasing_unit_interval_at_least_one_is_full",
    ],
    "U08.1": [
        "u08_1_recorded_after_cutoff_not_visible",
        "u08_1_late_append_uses_selection_stable",
        "u08_1_late_record_disguised_as_then_known_changes_applicability",
        "u08_1_mutable_current_status_disagrees_with_cutoff",
    ],
    "U10.3": [
        "u10_3_zero_step_ranked_path_is_identity",
        "u10_3_zero_step_prohibits_strict_progress",
        "u10_3_business_observation_faithful",
        "u10_3_zero_observation_is_not_progress",
        "u10_3_one_real_step_zero_abstract_is_not_progress",
    ],
    "U12.2": [
        "u12_2_halving_damps_toward_zero",
        "u12_2_negation_orbit_oscillates",
        "u12_2_one_minus_theta_oscillates",
        "u12_2_shift_has_no_fixed_point",
        "u12_2_cubic_reaches_zero_but_expands",
    ],
    "U14.2": [
        "u14_2_zero_N_rejects_positive_hypothesis",
        "u14_2_endogenous_equal_sizes_are_not_the_fixed_witness",
        "u14_2_common_cause_copy_exceeds_independent_variance",
    ],
    # CAND5bis (pack formal_tail_真证CAND5bis_20261025): candidate+expand only.
    "U08.2": [
        "u08_2_current_singleton_does_not_exhaust_reachable",
        "u08_2_nonempty_observation_preserves_chosen_answer",
    ],
    "U09.3": [
        "u09_3_greedy_prefix_misses_second_claim",
        "u09_3_same_institution_accrual_is_not_cash_effect",
    ],
    "U13.1": [
        "u13_1_lawful_stat_input_change_changes_estimate",
        "u13_1_personal_update_preserves_rule_service",
    ],
    "U15.1": [
        "u15_1_finite_state_strict_improve_length_bound",
        "u15_1_no_parameter_successor_has_no_fixed_point",
        "u15_1_telescoping_consumes_cumulative_improvement",
    ],
    "U15.2": [
        "u15_2_key_point_regression_changes_exact_risk",
        "u15_2_finite_obs_agree_not_global",
        "u15_2_full_agreement_preserves_risk",
    ],
    # CAND6 (pack formal_tail_关≥1_CAND6_20261026): CLOSED_BY_WIRING this round.
    # Expand-audit naming in ci-tip-1c72e444 is the qualification, not the close.
    # Order inside each clause is source order. Short names stay out of wired_declarations.
    "U08.3": [
        "u08_3_four_states_do_not_exhaust_dependency_policies",
        "u08_3_judgment_not_compatibility_world_classification",
        "u08_3_opposition_preserves_support_not_full_reflection",
    ],
    "U15.3": [
        "u15_3_two_point_risks_do_not_complete_five_evidence_levels",
        "u15_3_second_round_consumer_is_not_evidence_ladder",
    ],
    "U13.2": [
        "u13_2_frames_do_not_imply_authorized_rule_load",
        "u13_2_condition_does_not_train_not_persistent_storage_refinement",
    ],
    "U09.1": [
        "u09_1_conservation_not_receipt_revision_order",
        "u09_1_receipt_coherent_not_cash_uniqueness",
        "u09_1_at_most_once_not_product_protocol_refinement",
    ],
    "U10.2": [
        "u10_2_executor_and_trace_not_full_mixed_operation_coverage",
        "u10_2_post_invariant_not_gamma_frame_or_service_refinement",
    ],
    # CAND7 (pack formal_tail_关≥1_CAND7_20261026): CLOSED_BY_WIRING this round.
    # Expand-audit naming in ci-tip-21862d9b is the qualification, not the close.
    "U07.1": [
        "u07_1_retraction_not_full_observation_decoding_acceptance",
        "u07_1_separation_monotone_not_history_decoding",
        "u07_1_encode_nonsurjective_not_full_decode_acceptance",
    ],
    "U02.3": [
        "u02_3_finite_enumeration_not_generator_support_coverage",
        "u02_3_common_idle_and_zero_coverage_not_support_coverage",
    ],
    "U04.3": [
        "u04_3_unpenalized_positive_not_penalized_minimizer_existence",
        "u04_3_unpenalized_improves_not_uniqueness",
        "u04_3_arbitrarily_small_not_intercept_coordinate_solved",
    ],
    "U05.2": [
        "u05_2_bernoulli_brier_not_conditional_expectation_decomposition",
        "u05_2_selected_risk_not_simultaneous_threshold_or_rare_group",
    ],
    "U06.3": [
        "u06_3_eval_exists_unique_not_interval_multiplication_enclosure",
        "u06_3_decision_respects_allowed_not_general_uncertainty_comparison",
    ],
}
# Audited declaration names the candidate proofs actually call. Listing them
# is not a tip-pin citation of the candidate, and it does not close the row.
CANDIDATE_USES_AUDITED: dict[str, list[str]] = {
    "U06.4": [
        "JurisLean.Candidates.Final20261021.Decision.u06_4_threshold_increasing",
        "JurisLean.Candidates.Final20261021.Decision.u06_4_threshold_decreasing",
    ],
    "U08.1": [
        "JurisLean.Candidates.Final20261021.Temporal.u08_1_selection_stable",
    ],
    "U10.3": [
        "JurisLean.Candidates.Final20261021.Progress.u10_3_simulation_length",
    ],
    "U14.2": [
        "JurisLean.Candidates.Final20261021.Feedback.u14_2_unequal_cluster_effective_size",
        "JurisLean.Candidates.Final20261021.Learning.u01_4_copied_mean_variance",
        "JurisLean.Candidates.Final20261021.Learning.u01_4_independent_mean_variance",
        "JurisLean.Candidates.Final20261021.Learning.u01_4_copy_is_not_independent",
    ],
    "U08.2": [
        "JurisLean.Candidates.Final20261021.Temporal.u08_2_finite_compression_reflection",
    ],
    "U09.3": [
        "JurisLean.Candidates.Final20261021.Ledger.u09_3_accrual_not_cash",
    ],
    "U13.1": [
        "JurisLean.Candidates.Final20261021.RSI.u13_1_noninterference",
    ],
    "U15.1": [
        "JurisLean.Candidates.Final20261021.Iteration.u15_1_finite_cumulative_improvement",
    ],
    "U15.2": [
        "JurisLean.Candidates.Final20261021.Iteration.u15_2_preserved_predictions_equal_risk",
    ],
    "U08.3": [
        "JurisLean.Candidates.Final20261021.EvidenceProcedure.u08_3_evidence_four_states",
        "JurisLean.Candidates.Final20261021.EvidenceProcedure.u08_3_judgment_not_truth",
        "JurisLean.Candidates.Final20261021.EvidenceProcedure.u08_3_opposition_does_not_erase_support",
    ],
    "U15.3": [
        "JurisLean.Candidates.Final20261021.Iteration.two_round_exact_risks",
        "JurisLean.Candidates.Final20261021.Iteration.u15_3_two_round_actual_state",
    ],
    "U13.2": [
        "JurisLean.Candidates.Final20261021.RSI.u13_2_personal_frame",
        "JurisLean.Candidates.Final20261021.RSI.u13_2_data_frame",
        "JurisLean.Candidates.Final20261021.RSI.u13_2_condition_does_not_train",
    ],
    "U09.1": [
        "JurisLean.Candidates.Final20261021.Ledger.u09_1_quantity_conservation",
        "JurisLean.Candidates.Final20261021.Trace.u09_1_actual_trace_at_most_once",
    ],
    "U10.2": [
        "JurisLean.Candidates.Final20261021.Trace.u10_2_committed_executor_is_step",
        "JurisLean.Candidates.Final20261021.Trace.u10_2_known_executor_post_preserves",
        "JurisLean.Candidates.Final20261021.Trace.u10_2_finite_trace_composition",
        "JurisLean.Candidates.Final20261021.Pipeline.u10_2_pipeline_second_post_invariant",
    ],
    "U07.1": [
        "JurisLean.Candidates.Final20261021.Representation.u07_1_retraction_injective",
        "JurisLean.Candidates.Final20261021.Representation.u07_1_section_surjective",
        "JurisLean.Candidates.Final20261021.Representation.u07_1_rho_idempotent",
        "JurisLean.Candidates.Final20261021.Representation.u07_1_separation_monotone",
        "JurisLean.Candidates.Final20261021.Acceptance.n07_1_constant_family_not_separating",
        "JurisLean.Candidates.Final20261021.Acceptance.a07_1_identity_observation_separates",
        "JurisLean.Candidates.Final20261021.Acceptance.n07_1_retraction_need_not_encode_surjectively",
    ],
    "U02.3": [
        "JurisLean.Candidates.Final20261021.Harness.u02_3_finite_gate_enumeration",
        "JurisLean.Candidates.Final20261021.Harness.zero_coverage_not_zero_risk",
        "JurisLean.Candidates.Final20261021.Acceptance.a02_common_idle_remains_allowed",
    ],
    "U04.3": [
        "JurisLean.Candidates.Final20261021.Probability.u04_3_unpenalized_intercept_positive",
        "JurisLean.Candidates.Final20261021.Probability.u04_3_unpenalized_intercept_improves",
        "JurisLean.Candidates.Final20261021.Probability.u04_3_unpenalized_never_zero",
        "JurisLean.Candidates.Final20261021.Probability.u04_3_unpenalized_arbitrarily_small",
    ],
    "U05.2": [
        "JurisLean.Candidates.Final20261021.Calibration.u05_2_brier_decomposition",
        "JurisLean.Candidates.Final20261021.Calibration.u05_2_brier_unique_optimum",
        "JurisLean.Candidates.Final20261021.Calibration.u05_2_selected_risk",
        "JurisLean.Candidates.Final20261021.Acceptance.n05_raising_score_threshold_increases_risk",
    ],
    "U06.3": [
        "JurisLean.Candidates.Final20261021.Decision.u06_3_eval_exists",
        "JurisLean.Candidates.Final20261021.Decision.u06_3_eval_unique",
        "JurisLean.Candidates.Final20261021.Decision.u06_3_decision_respects_allowed",
    ],
}
CANDIDATE_COVERS_ONLY: dict[str, str] = {
    "U06.4": (
        "Four corollaries of the audited threshold identities when the implied "
        "threshold lies outside [0,1], plus unit-interval empty/full forms. "
        "Named in expand-audit evidence/ci-tip-f85ebe44 (named_count=25; "
        "candidate_axiom_audit PASS). Prior 40079130550 is not FormalTail coverage. "
        "Pack formal_tail_关≥1_CAND5_20261025 authorized CLOSED_BY_WIRING for this "
        "row; FormalTail short names stay out of wired_declarations."
    ),
    "U08.1": (
        "Late-record invisibility, selection-stable append, disguise, and "
        "mutable-current-status disagreement. Named in expand-audit "
        "evidence/ci-tip-f85ebe44 (named_count=25; candidate_axiom_audit PASS). "
        "Prior 40079130550 is not FormalTail coverage. Pack "
        "formal_tail_关≥1_CAND5_20261025 authorized CLOSED_BY_WIRING for this row; "
        "FormalTail short names stay out of wired_declarations."
    ),
    "U10.3": (
        "A zero-step ranked path is the identity and does not strictly decrease rank. "
        "Business-observed length is the sum of per-operation abstract steps and obeys the "
        "audited simulation-length bound; a zero observation is not positive progress. "
        "公平 and 外部响应 are explicit non-goals of this clause (exact_scope: 另证). "
        "Named in expand-audit evidence/ci-tip-f85ebe44 (named_count=25; "
        "candidate_axiom_audit PASS). Prior 40079130550 is not FormalTail coverage. "
        "Pack formal_tail_关≥1_CAND5_20261025 authorized CLOSED_BY_WIRING for this "
        "row; FormalTail short names stay out of wired_declarations."
    ),
    "U12.2": (
        "Halving damping, negation/one-minus-theta oscillation, shift without fixed "
        "point, and cubic reaching zero while expanding. Named in expand-audit "
        "evidence/ci-tip-f85ebe44 (named_count=25; candidate_axiom_audit PASS). "
        "Prior 40079130550 is not FormalTail coverage. Pack "
        "formal_tail_关≥1_CAND5_20261025 authorized CLOSED_BY_WIRING for this row; "
        "FormalTail short names stay out of wired_declarations."
    ),
    "U14.2": (
        "Zero-N rejects a positive hypothesis; endogenous equal sizes are not the "
        "fixed witness; common-cause copy exceeds independent variance. Named in "
        "expand-audit evidence/ci-tip-f85ebe44 (named_count=25; "
        "candidate_axiom_audit PASS). Prior 40079130550 is not FormalTail coverage. "
        "Pack formal_tail_关≥1_CAND5_20261025 authorized CLOSED_BY_WIRING for this "
        "row; FormalTail short names stay out of wired_declarations."
    ),
    "U08.2": (
        "Current-singleton does not exhaust a two-point reachable set; nonempty "
        "observation preserves the chosen answer via audited finite-compression "
        "reflection. Named in expand-audit evidence/ci-tip-dc7b7430 (named_count=37; "
        "pack tip_pin_扩审计_CAND5bis_20261025). Pack "
        "formal_tail_关≥1_CAND5bis_20261025 authorized CLOSED_BY_WIRING for this row; "
        "FormalTail short names stay out of wired_declarations."
    ),
    "U09.3": (
        "Greedy prefix on a two-claim budget misses a full optimum; same-institution "
        "accrual does not move cash (audited accrual_not_cash). Named in expand-audit "
        "evidence/ci-tip-dc7b7430 (named_count=37; pack tip_pin_扩审计_CAND5bis_20261025). "
        "Pack formal_tail_关≥1_CAND5bis_20261025 authorized CLOSED_BY_WIRING for this row; "
        "FormalTail short names stay out of wired_declarations."
    ),
    "U13.1": (
        "Lawful statistical-evidence input change moves the conditional estimate; "
        "personal update preserves rule service (audited noninterference). Authority "
        "integration is an explicit NON_GOAL. Named in expand-audit evidence/ci-tip-dc7b7430 "
        "(named_count=37; pack tip_pin_扩审计_CAND5bis_20261025). Pack "
        "formal_tail_关≥1_CAND5bis_20261025 authorized CLOSED_BY_WIRING for this row; "
        "FormalTail short names stay out of wired_declarations."
    ),
    "U15.1": (
        "Finite-state strict-improvement length is bounded by starting rank; "
        "parameter-free successor has no fixed point; telescoping consumes audited "
        "finite_cumulative_improvement. Named in expand-audit evidence/ci-tip-dc7b7430 "
        "(named_count=37; pack tip_pin_扩审计_CAND5bis_20261025). Pack "
        "formal_tail_关≥1_CAND5bis_20261025 authorized CLOSED_BY_WIRING for this row; "
        "FormalTail short names stay out of wired_declarations."
    ),
    "U15.2": (
        "Key-point regression changes exact risk; finite-observation agreement is "
        "not global agreement; full agreement preserves risk via audited "
        "preserved_predictions_equal_risk. Named in expand-audit evidence/ci-tip-dc7b7430 "
        "(named_count=37; pack tip_pin_扩审计_CAND5bis_20261025). Pack "
        "formal_tail_关≥1_CAND5bis_20261025 authorized CLOSED_BY_WIRING for this row; "
        "FormalTail short names stay out of wired_declarations."
    ),
    "U08.3": (
        "Four judgment states, a supported judgment parked as unfinished "
        "world-classification, and opposition that keeps support do not exhaust "
        "dependency policies or a compatibility-world partition. Reality-truth "
        "stays a non-goal on this same row. Named in expand-audit "
        "evidence/ci-tip-1c72e444 (named_count=49; pack tip_pin_扩审计_CAND6_20261026). "
        "Pack formal_tail_关≥1_CAND6_20261026 authorized CLOSED_BY_WIRING for this row; "
        "FormalTail short names stay out of wired_declarations."
    ),
    "U15.3": (
        "Two exact-risk points and the second-round consumer do not complete five "
        "evidence levels. External load readback stays a non-goal on this same row. "
        "Named in expand-audit evidence/ci-tip-1c72e444 (named_count=49; pack "
        "tip_pin_扩审计_CAND6_20261026). Pack formal_tail_关≥1_CAND6_20261026 "
        "authorized CLOSED_BY_WIRING for this row; FormalTail short names stay out "
        "of wired_declarations."
    ),
    "U13.2": (
        "Personal and data frames do not load an authorized rule; a condition "
        "update that leaves the state unchanged does not append persistent storage. "
        "Named in expand-audit evidence/ci-tip-1c72e444 (named_count=49; pack "
        "tip_pin_扩审计_CAND6_20261026). Pack formal_tail_关≥1_CAND6_20261026 "
        "authorized CLOSED_BY_WIRING for this row; FormalTail short names stay out "
        "of wired_declarations."
    ),
    "U09.1": (
        "Quantity conservation does not order receipt revisions; receipt coherence "
        "does not force cash-event uniqueness; at-most-once replay refusal does not "
        "state a product-protocol refinement. Legal allocation and extinction stay "
        "non-goals on this same row. Named in expand-audit evidence/ci-tip-1c72e444 "
        "(named_count=49; pack tip_pin_扩审计_CAND6_20261026). Pack "
        "formal_tail_关≥1_CAND6_20261026 authorized CLOSED_BY_WIRING for this row; "
        "FormalTail short names stay out of wired_declarations."
    ),
    "U10.2": (
        "A committed pay step plus one accrue step is not full mixed-operation "
        "coverage; the pipeline post-invariant does not force a service jurisdiction "
        "or a service refinement. Named in expand-audit evidence/ci-tip-1c72e444 "
        "(named_count=49; pack tip_pin_扩审计_CAND6_20261026). Pack "
        "formal_tail_关≥1_CAND6_20261026 authorized CLOSED_BY_WIRING for this row; "
        "FormalTail short names stay out of wired_declarations."
    ),
    "U07.1": (
        "Retraction, section, and idempotent image do not state full observation or "
        "history decoding acceptance; separation and encode witnesses stay non-sufficient. "
        "Named in expand-audit evidence/ci-tip-21862d9b (named_count=61; pack "
        "tip_pin_扩审计_CAND7_20261026). Pack formal_tail_关≥1_CAND7_20261026 "
        "authorized CLOSED_BY_WIRING for this row; FormalTail short names stay out "
        "of wired_declarations."
    ),
    "U02.3": (
        "Finite enumeration, common idle, and zero-coverage witnesses do not state "
        "generator support coverage. Named in expand-audit evidence/ci-tip-21862d9b "
        "(named_count=61; pack tip_pin_扩审计_CAND7_20261026). Pack "
        "formal_tail_关≥1_CAND7_20261026 authorized CLOSED_BY_WIRING for this row; "
        "FormalTail short names stay out of wired_declarations."
    ),
    "U04.3": (
        "Unpenalized-intercept counterexamples do not state penalized minimizer "
        "existence, uniqueness, or intercept solved. Calibration, causal identification, "
        "and numerical attainment stay non-goals on this same row. Named in expand-audit "
        "evidence/ci-tip-21862d9b (named_count=61; pack tip_pin_扩审计_CAND7_20261026). "
        "Pack formal_tail_关≥1_CAND7_20261026 authorized CLOSED_BY_WIRING for this row; "
        "FormalTail short names stay out of wired_declarations."
    ),
    "U05.2": (
        "Bernoulli Brier algebra and selected-risk witnesses do not state conditional "
        "expectation decomposition, simultaneous threshold control, or rare-group coverage. "
        "Named in expand-audit evidence/ci-tip-21862d9b (named_count=61; pack "
        "tip_pin_扩审计_CAND7_20261026). Pack formal_tail_关≥1_CAND7_20261026 "
        "authorized CLOSED_BY_WIRING for this row; FormalTail short names stay out "
        "of wired_declarations."
    ),
    "U06.3": (
        "Eval exists, uniqueness, and decision-respects-allowed do not state interval "
        "multiplication enclosure or general uncertainty comparison. Named in expand-audit "
        "evidence/ci-tip-21862d9b (named_count=61; pack tip_pin_扩审计_CAND7_20261026). "
        "Pack formal_tail_关≥1_CAND7_20261026 authorized CLOSED_BY_WIRING for this row; "
        "FormalTail short names stay out of wired_declarations."
    ),
}
TAIL_BLOCKER = (
    "The unwired formal obligation is not a declaration accepted by tip-pin "
    "axiom audit subject 21862d9bdd94bfa15e5da39079538b5eb30ff235, run "
    "40274167574, job 121413235107. Candidates/Final20261021/*.lean stays "
    "byte-locked to that receipt, so this round cannot edit those files or "
    "cite a new name as audited. A candidate module outside that directory "
    "is not closure. Gate SUCCESS does not close the row. Retargeting the "
    "tip-pin does not close the row. "
    "discharges_archived_manuscript_gaps stays false. Step 2 stays open."
)


def status_for(clause: str) -> str:
    path = PATHS[clause]
    if path == "缩":
        if UNWIRED.get(clause):
            raise RuntimeError(f"{clause}: narrow row still has an unwired formal tail")
        if not NON_GOALS.get(clause):
            raise RuntimeError(f"{clause}: narrow row has no non-goal")
        return "CLOSED_BY_NARROW"
    if UNWIRED.get(clause):
        return "OPEN_FORMAL_TAIL"
    if not SCOPE_REVIEW.get(clause):
        raise RuntimeError(f"{clause}: wiring close has no scope review")
    return "CLOSED_BY_WIRING"


def formal_tail_record(clause: str) -> dict:
    """Prove-round record. Closed narrow/wiring rows are not reopened."""

    status = status_for(clause)
    if status != "OPEN_FORMAL_TAIL":
        return {
            "in_this_round": False,
            "not_reopened": True,
            "archive_gap_status": status,
            # close_admitted admits the formal-tail row only; never discharges.
            "close_admitted": (
                clause in CAND5_CLOSED_IDS
                or clause in CAND5BIS_CLOSED_IDS
                or clause in CAND6_CLOSED_IDS
                or clause in CAND7_CLOSED_IDS
                or clause in INDEPENDENT_CLOSED_IDS
            ),
            "step_2_closed": False,
            "discharges_archived_manuscript_gaps": False,
        }
    candidates = list(PROVE_CANDIDATES.get(clause, []))
    # Live tip-pin ci-tip-21862d9b names CAND5 (25) + CAND5bis (12) + CAND6 (12)
    # + CAND7 (12) = 61. Historical 1c72e444 (49), dc7b7430 (37), f85ebe44 (25).
    cand5bis = clause in CAND5BIS_IDS
    cand6 = clause in CAND6_IDS
    cand7 = clause in CAND7_IDS
    in_tip_pin_audit = bool(candidates)
    record = {
        "in_this_round": True,
        "round": FORMAL_TAIL_ROUND,
        "criteria_pack": FORMAL_TAIL_PACK,
        "pack_files": list(FORMAL_TAIL_PACK_FILES),
        "suggested_close_path": "证",
        "close_admitted": False,
        "disposition": "CANDIDATE_NOT_AUDITED" if candidates else "BLOCKED_NOT_IN_TIP_PIN_AUDIT",
        "candidate_module": CANDIDATE_MODULE if candidates else "",
        "candidate_module_name": CANDIDATE_MODULE_NAME if candidates else "",
        "candidate_theorems": candidates,
        "candidate_in_tip_pin_audit": in_tip_pin_audit,
        "candidate_covers_only": CANDIDATE_COVERS_ONLY.get(clause, ""),
        "unwired_formal_obligations": list(UNWIRED[clause]),
        "non_goals_same_row": list(NON_GOALS.get(clause, [])),
        "companion_scope_notes": COMPANION_NOTES.get(clause, ""),
        "companion_required": clause in COMPANION_TAIL_IDS,
        "local_lean_is_not_closure": True,
        "step_2_closed": False,
        "discharges_archived_manuscript_gaps": False,
        "blocker": TAIL_BLOCKER,
    }
    uses = CANDIDATE_USES_AUDITED.get(clause, [])
    if uses:
        record["uses_audited_declarations"] = list(uses)
    if candidates:
        record["tip_pin_expand_audit"] = dict(FORMAL_TAIL_EXPAND)
        if cand7:
            record["criteria_pack_cand7"] = FORMAL_TAIL_CAND7_PACK
            record["blocker"] = (
                "This CAND7 id is still OPEN_FORMAL_TAIL. Pack "
                "formal_tail_关≥1_CAND7_20261026 authorizes CLOSED_BY_WIRING only "
                "with empty UNWIRED and a scope review. Expand-audit naming in "
                "evidence/ci-tip-21862d9b (named_count=61) is not itself a close. "
                "discharges stays false. Step 2 stays open."
            )
            record["close_blocked_reason"] = (
                "Row is not in the authorized closed shape. "
                "discharges_archived_manuscript_gaps stays false. Step 2 stays open."
            )
        elif cand6:
            record["criteria_pack_cand6"] = FORMAL_TAIL_CAND6_PACK
            record["blocker"] = (
                "This CAND6 id is still OPEN_FORMAL_TAIL. Pack "
                "formal_tail_关≥1_CAND6_20261026 authorizes CLOSED_BY_WIRING only "
                "with empty UNWIRED and a scope review. Expand-audit naming in "
                "evidence/ci-tip-1c72e444 (named_count=49) is not itself a close. "
                "discharges stays false. Step 2 stays open."
            )
            record["close_blocked_reason"] = (
                "Row is not in the authorized closed shape. "
                "discharges_archived_manuscript_gaps stays false. Step 2 stays open."
            )
        elif cand5bis:
            record["criteria_pack_cand5bis"] = FORMAL_TAIL_CAND5BIS_PACK
            record["blocker"] = (
                "This CAND5bis id is still OPEN_FORMAL_TAIL. Pack "
                "formal_tail_关≥1_CAND5bis_20261025 authorizes CLOSED_BY_WIRING only "
                "with empty UNWIRED and a scope review. Expand-audit naming in "
                "evidence/ci-tip-dc7b7430 (named_count=37) is not itself a close. "
                "discharges stays false. Step 2 stays open."
            )
            record["close_blocked_reason"] = (
                "Row is not in the authorized closed shape. "
                "discharges_archived_manuscript_gaps stays false. Step 2 stays open."
            )
        else:
            record["blocker"] = (
                "FormalTail theorems are named in expand-audit "
                "evidence/ci-tip-dc7b7430/verification.json (pack "
                "tip_pin_扩审计_CAND5bis_20261025; named_count=37). Prior tip-pin "
                "f85ebe44 / 40115638107 must not be cited as the live FormalTail "
                "coverage. Disposition stays CANDIDATE_NOT_AUDITED until math debt-layer. "
                "discharges_archived_manuscript_gaps stays false. Step 2 stays open."
            )
            record["close_blocked_reason"] = (
                "Expand-audit naming wires candidate_in_tip_pin_audit evidence only. "
                "Math has not authorized disposition change, discharges, or a close. "
                "discharges_archived_manuscript_gaps stays false. Step 2 stays open."
            )
    return record


def formal_tail_summary(rows: list[dict]) -> dict:
    open_rows = [row for row in rows if row.get("archive_gap_status") == "OPEN_FORMAL_TAIL"]
    return {
        "round": FORMAL_TAIL_ROUND,
        "criteria_pack": FORMAL_TAIL_PACK,
        "pack_files": list(FORMAL_TAIL_PACK_FILES),
        "one_pipeline": "archive-gap close ledger; no second track",
        "open_formal_tail_remaining": len(open_rows),
        "closed_this_round": len(CURRENT_CLOSE_IDS),
        "historical_cand7_closed": CAND7_CLOSED_THIS_ROUND,
        "historical_u03_closed": len(POST_PIN_CLOSED_IDS),
        "historical_u01_closed": len(U01_CLOSED_IDS),
        "independent_closed_ids": list(INDEPENDENT_CLOSED_IDS),
        "independent_closed_total": len(INDEPENDENT_CLOSED_IDS),
        "independent_receipts": [p["receipt"] for p in INDEPENDENT_CLOSE_PACKS],
        "independent_receipt": CURRENT_CLOSE_RECEIPT,
        "close_pack": CURRENT_CLOSE_PACK,
        "candidate_rows": sum(
            1 for row in open_rows if (row.get("formal_tail_prove") or {}).get("disposition") == "CANDIDATE_NOT_AUDITED"
        ),
        "blocked_rows": sum(
            1
            for row in open_rows
            if (row.get("formal_tail_prove") or {}).get("disposition") == "BLOCKED_NOT_IN_TIP_PIN_AUDIT"
        ),
        "narrow_not_reopened": list(CLOSED_NARROW_IDS),
        "wiring_not_reopened": [c for c in CLOSED_WIRING_IDS if c not in CURRENT_CLOSE_IDS],
        "companion_tail_ids": list(COMPANION_TAIL_IDS),
        "candidate_module": CANDIDATE_MODULE,
        "candidate_module_quarantine": (
            "CAND5+CAND5bis+CAND6+CAND7 named in expand-audit evidence/ci-tip-21862d9b "
            f"(named_count=61). CAND5 U06.4/U08.1/U10.3/U12.2/U14.2 closed by wiring under "
            "pack formal_tail_关≥1_CAND5_20261025. CAND5bis U08.2/U09.3/U13.1/U15.1/U15.2 "
            "closed by wiring under pack formal_tail_关≥1_CAND5bis_20261025 "
            f"(closed_this_round={CAND5BIS_CLOSED_THIS_ROUND} historical). "
            "CAND6 U08.3/U15.3/U13.2/U09.1/U10.2 closed by wiring under pack "
            "formal_tail_关≥1_CAND6_20261026 "
            f"(closed_this_round={CAND6_CLOSED_THIS_ROUND} historical). "
            "CAND7 U07.1/U02.3/U04.3/U05.2/U06.3 closed by wiring under pack "
            "formal_tail_关≥1_CAND7_20261026 "
            f"(closed_this_round={CAND7_CLOSED_THIS_ROUND} historical; OPEN_FORMAL_TAIL=20; "
            "CLOSED_BY_WIRING=22). Historical ci-tip-1c72e444 stays named_count=49; "
            "ci-tip-dc7b7430 stays 37. FormalTail short names stay out of "
            "wired_declarations; discharges stay false; step_2_closed stays false; "
            "tip_pin retarget to 21862d9b / 40274167574 / 121413235107 does not close "
            "debt. The later independent U03 package closes U03.1/U03.2 using new exact "
            "residual proofs (20 to 18). The subsequent independent U01 package closes "
            "U01.1/U01.2/U01.3 against the original residuals (18 to 15). The later "
            "independent U04.5 package proves general likelihood and copy information "
            "(15 to 14). The later independent U14.1 package names the existing "
            "independent statistical validation, adaptive conditional budgets and "
            "service-load proofs against its original residual (14 to 13). CAND8 still "
            "retains both U07.2 negative boundary declarations and they remain outside "
            "PROVE_CANDIDATES; a separate positive successful-source joint-object package "
            "closes only the current U07.2 residual. The later U07.3 package closes only "
            "its fixed-history selected-row semantic/projection residual under explicit "
            "interpretation inputs; source truth/O05 and old Pipeline consumption remain "
            "outside that proof. The later independent U04.2 package closes only its frozen "
            "probability residual and leaves original-question 04.4 identification "
            "obligations and U00 edge 6 numeric consumption open. The later U11.1 package supplies the two original-question 04.4 compatible missing-outcome endpoints and MCAR recovery; U00 edge 6 remains numerically unconnected. The U12.1 package now closes its finite-action causal-policy interpretation and original 12.3/12.6 examples; old Pipeline numeric consumption remains unwired. The U10.1 package closes the archived refresh-to-Step protocol residual while retaining external authority and full-world checkBranch limits. The U02.4 source package audits the finite/countable P_H conditional-risk bounds, H/Hᶜ α+ε partition, H=B witness, and the single global-attempt cumulative-budget prefix/suffix identity. It does not assert runtime execution. The U01.4 package audits the archived finite fit-label, point-mass deployment, dependence, and within-domain grouping witnesses without a real-data claim. The U04.4 package audits the stated equicorrelated mean-variance formula, positive effective-count and zero-denominator branches, and finite dependence boundaries without claiming independence restoration. Current "
        "OPEN_FORMAL_TAIL=0; CLOSED_BY_WIRING=46; the "
            "historical CAND8 and tip-pin receipts are unchanged."
        ),
        "discharges_archived_manuscript_gaps": False,
        "math_flip_authorized": False,
        "step_2_closed": False,
        "tip_pin_not_retargeted": False,
        "tip_pin": dict(TIP_PIN),
        "formal_tail_expand_audit": dict(FORMAL_TAIL_EXPAND),
        "later_tip_gate_not_a_close": dict(LATER_TIP_GATE),
        "gate_green_does_not_close_debt": True,
        "china_law_column": "separate; foreign law and arXiv do not close China-law items",
        "local_lean_is_not_closure": True,
    }


def remaining_after(clause: str) -> str:
    status = status_for(clause)
    goals = NON_GOALS.get(clause) or []
    if status == "OPEN_FORMAL_TAIL":
        text = "OPEN_FORMAL: " + " | ".join(UNWIRED[clause])
        if goals:
            text += " || NON_GOAL_POINTER: " + " | ".join(goals)
        return text
    if status == "CLOSED_BY_NARROW":
        return "NON_GOAL_POINTER: " + " | ".join(goals)
    text = ("WIRED_TO_INDEPENDENT_U10_1_PROOFS" if clause in U10_1_CLOSED_IDS else
            "WIRED_TO_INDEPENDENT_U04_4_PROOFS" if clause in U04_4_CLOSED_IDS else
            "WIRED_TO_INDEPENDENT_U01_4_PROOFS" if clause in U01_4_CLOSED_IDS else
            "WIRED_TO_INDEPENDENT_U09_2_PROOFS" if clause in U09_2_CLOSED_IDS else
            "WIRED_TO_INDEPENDENT_U02_4_PROOFS" if clause in U02_4_CLOSED_IDS else
            "WIRED_TO_INDEPENDENT_U12_1_PROOFS" if clause in U12_1_CLOSED_IDS else
            "WIRED_TO_INDEPENDENT_U11_1_PROOFS" if clause in U11_1_CLOSED_IDS else
            "WIRED_TO_INDEPENDENT_U06_2_PROOFS" if clause in U06_2_CLOSED_IDS else
            "WIRED_TO_INDEPENDENT_U12_3_PROOFS" if clause in U12_3_CLOSED_IDS else
            "WIRED_TO_INDEPENDENT_U06_1_PROOFS" if clause in U06_1_CLOSED_IDS else
            "WIRED_TO_INDEPENDENT_U04_2_PROOFS" if clause in U04_2_CLOSED_IDS else
            "WIRED_TO_INDEPENDENT_U02_1_PROOFS" if clause in U02_1_CLOSED_IDS else
            "WIRED_TO_INDEPENDENT_U07_3_PROOFS" if clause in U07_3_CLOSED_IDS else
            "WIRED_TO_INDEPENDENT_U07_2_PROOFS" if clause in U07_2_CLOSED_IDS else
            "WIRED_TO_INDEPENDENT_U13_3_PROOFS" if clause in U13_3_CLOSED_IDS else
            "WIRED_TO_INDEPENDENT_U12_4_PROOFS" if clause in U12_4_CLOSED_IDS else
            "WIRED_TO_INDEPENDENT_U14_1_PROOFS" if clause in U14_1_CLOSED_IDS else
            "WIRED_TO_INDEPENDENT_U04_5_PROOFS" if clause in U04_5_CLOSED_IDS else
            "WIRED_TO_INDEPENDENT_U01_PROOFS" if clause in U01_CLOSED_IDS else
            "WIRED_TO_INDEPENDENT_U03_PROOFS" if clause in POST_PIN_CLOSED_IDS else
            "WIRED_TO_TIP_PIN_DECLARATIONS")
    if goals:
        text += " || NON_GOAL_POINTER: " + " | ".join(goals)
    return text
