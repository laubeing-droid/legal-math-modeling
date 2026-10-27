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
    "U02.2": "companion_缩: 真实DB精化/外部副作用/最终完成",
    "U02.4": "claimed_scope: 分区预算α+ε与H=B反例；non_goal: general filtration/random-budget tower",
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
    "U02.4": "缩",
    "U08.1": "证",
    "U10.1": "证",
    "U10.2": "证",
    "U08.2": "证",
    "U08.3": "证",
    "U10.3": "证",
    "U09.1": "证",
    "U09.2": "缩",
    "U09.3": "证",
    "U01.0": "证",
    "U01.1": "证",
    "U01.2": "证",
    "U01.3": "证",
    "U01.4": "缩",
    "U04.1": "缩",
    "U04.2": "证",
    "U04.3": "证",
    "U04.4": "缩",
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
    "U02.2": [
        "Full refinement of concrete Ledger/Pipeline into Store/Trace, including external occurrences, is an explicit non-goal.",
        "真实DB精化、外部副作用、最终完成 are explicit non-goals. China-law discharge is not decided here.",
    ],
    "U02.4": [
        "A general filtration/random-budget tower beyond the named partition identity is an explicit non-goal, not an additional theorem of this clause.",
        "Run 39783481932 compiling the partition declarations does not discharge that tower. Tip-pin axiom-audit PASS does not discharge it either.",
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
    "U09.1": [
        "Full legal allocation effects are an explicit non-goal. 金额清零不等法律关系消灭; this wiring does not close a China-law extinction claim.",
    ],
    "U09.2": [
        "Actual occurrence of the cash events is an external premise, not a theorem of the finite closed-account sum.",
        "Completeness of boundary accounts is an external premise and an explicit non-goal.",
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
        "n_eff does not restore independence. Restoration of independence is an explicit non-goal.",
        "Run 39783481932 compiling the covariance expansion does not discharge a restoration of independence.",
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
    "U02.4": "Named partition budget α+ε, union bound in the supplied measure, and the H=B finite counterexample (marginal 1/10, conditional 1).",
    "U09.2": "Finite closed-account sum and per-account sums.",
    "U01.4": "Named finite witnesses: pointwise train 0 / target 1 / deployment 1, independent mean variance 1/(4n), copied mean variance 1/4, and the n>1 separation.",
    "U04.1": "Integer-shape density conjugacy, predictive mean, real Gamma weight ratio, and the exchangeable 5/6 versus Beta(1,1) 2/3 witness.",
    "U04.4": "Covariance expansion, positive-denominator effective count, constant average of B and 1-B, the r=-1 quadratic form, and the zero-denominator branch.",
    "U05.1": "Tie-free rank prefix mass, threshold inequality k/(n+1)≥1-α, infinity branch, and the marginal-versus-group numeric split.",
    "U06.5": "Signal value 3/10-cost, cost>3/10 net negative, the given two-round tree (4,6), and matching-pennies with no pure equilibrium.",
    "U00": "Actual finite source-to-decision-to-two-payment-to-feedback paths named by the clause declarations.",
}

# Formal sentences the wired declarations do not state. Empty means the
# suggested path is fully dispositioned (narrow, or wiring plus non-goals).
UNWIRED: dict[str, list[str]] = {
    "U07.2": [
        "Actual semantic compatibility of supplied layers remains a separate unproved obligation.",
    ],
    "U07.3": [
        "Source truth and arbitrary extractor fidelity are not proved by the fixed-history projection theorem.",
    ],
    "U03.1": [],  # Independently proved and audited by the later U03 closure package.
    "U03.2": [],  # Independently proved and audited by the later U03 closure package.
    "U02.1": [
        "Actual-world and actual-successor refinement of the concrete pipeline table remains unproved.",
    ],
    "U10.1": [
        "Complete protocol refinement remains unproved. The Pipeline refresh-to-Step link does not state it.",
    ],
    "U01.1": [],  # Original residual proved in the independent U01 package.
    "U01.2": [],  # Original residual proved in the independent U01 package.
    "U01.3": [],  # Original residual proved in the independent U01 package.
    "U04.2": [
        "Width, beta integrals, the three-event sharp identified set, and contamination subclaims remain unproved.",
    ],
    "U04.5": [
        "A general joint likelihood/copy theorem and the sigma-field information argument remain unproved.",
    ],
    "U06.1": [
        "The full Bellman optimum, the blocked terminal convention, and the nonrectangular counterexample remain unproved.",
    ],
    "U06.2": [
        "Mixed expectations and an explicit strategy/tree bridge remain unproved.",
    ],
    "U11.1": [
        "The g formula, K1/K2 selection, sharp support gaps, and measurement bridges remain unproved.",
    ],
    "U12.1": [
        "Complete causal/measurement interpretation and the support-gap identified range remain unproved. Finite IPW cancellation does not state them.",
    ],
    "U12.3": [
        "Weighted uniform selection, MAR, and the full sequential-kernel likelihood-ratio theorem remain UNPROVED. The clipping identity does not state them.",
    ],
    "U12.4": [
        "Full frozen-model acceptance beyond the two incentive inequalities and the distinguishability counterexample is not established by citing the tip-pin audit of those two declarations.",
    ],
    "U13.3": [
        "Same-loss risk transfer and unsupported-domain witnesses remain unproved.",
    ],
    "U13.4": [
        "Distinct provenance/scope policies for the fallback sources and nonidentification witnesses are not validated by the missing-checkpoint branch alone.",
    ],
    "U14.1": [
        "Independent statistical validation, adaptive conditional budgets, and service-load integration remain unproved.",
    ],
}

SCOPE_REVIEW: dict[str, str] = {
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
    "U10.1",
    "U08.3",
    "U10.3",
    "U09.1",
    "U04.3",
    "U12.4",
    "U13.4",
    "U15.3",
)
CLOSED_NARROW_IDS = (
    "U02.4",
    "U09.2",
    "U01.4",
    "U04.1",
    "U04.4",
    "U05.1",
    "U06.5",
    "U00",
)
CLOSED_WIRING_IDS = (
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
POST_PIN_OPEN_REMAINING = 15
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
INDEPENDENT_CLOSE_PACKS = (
    {"closed_ids": POST_PIN_CLOSED_IDS, "pack": POST_PIN_CLOSE_PACK,
     "receipt": POST_PIN_RECEIPT, "names": POST_PIN_NAMES,
     "driver": POST_PIN_DRIVER, "sources": POST_PIN_SOURCES,
     "open_before": 20, "open_after": 18},
    {"closed_ids": U01_CLOSED_IDS, "pack": U01_CLOSE_PACK,
     "receipt": U01_RECEIPT, "names": U01_NAMES,
     "driver": U01_DRIVER, "sources": U01_SOURCES,
     "open_before": 18, "open_after": 15},
)
INDEPENDENT_CLOSED_IDS = POST_PIN_CLOSED_IDS + U01_CLOSED_IDS
INDEPENDENT_NAMES = POST_PIN_NAMES | U01_NAMES
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
        "closed_this_round": len(U01_CLOSED_IDS),
        "historical_cand7_closed": CAND7_CLOSED_THIS_ROUND,
        "historical_u03_closed": len(POST_PIN_CLOSED_IDS),
        "independent_closed_ids": list(INDEPENDENT_CLOSED_IDS),
        "independent_closed_total": len(INDEPENDENT_CLOSED_IDS),
        "independent_receipts": [p["receipt"] for p in INDEPENDENT_CLOSE_PACKS],
        "independent_receipt": U01_RECEIPT,
        "close_pack": U01_CLOSE_PACK,
        "candidate_rows": sum(
            1 for row in open_rows if (row.get("formal_tail_prove") or {}).get("disposition") == "CANDIDATE_NOT_AUDITED"
        ),
        "blocked_rows": sum(
            1
            for row in open_rows
            if (row.get("formal_tail_prove") or {}).get("disposition") == "BLOCKED_NOT_IN_TIP_PIN_AUDIT"
        ),
        "narrow_not_reopened": list(CLOSED_NARROW_IDS),
        "wiring_not_reopened": [c for c in CLOSED_WIRING_IDS if c not in U01_CLOSED_IDS],
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
            "U01.1/U01.2/U01.3 against the original residuals; remaining OPEN are "
            "15 BLOCKED_NOT_IN_TIP_PIN_AUDIT."
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
    text = ("WIRED_TO_INDEPENDENT_U01_PROOFS" if clause in U01_CLOSED_IDS else
            "WIRED_TO_INDEPENDENT_U03_PROOFS" if clause in POST_PIN_CLOSED_IDS else
            "WIRED_TO_TIP_PIN_DECLARATIONS")
    if goals:
        text += " || NON_GOAL_POINTER: " + " | ".join(goals)
    return text
