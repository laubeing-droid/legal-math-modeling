"""Dispositions for the 50 archived manuscript gaps.

The manuscript pin ``evidence/ci-tip-e87543d8/scope-archive.json`` stays
verbatim. This module is the construction record that processes each pinned
``remaining_obligations`` string on the math pack's suggested path:

* ``缩`` rewrites the residual as an explicit non-goal in the same row as the
  claimed-scope declarations.
* ``证`` wires the formal candidate bodies to declarations accepted by the
  live tip-pin axiom audit (subject e87543d, run 39933015422, job
  120345670150). A sentence those declarations do not state stays
  ``OPEN_FORMAL_TAIL``. Companion non-goals from the 2026-10-24 rejudge are
  written on that same row.

Nothing here sets ``discharges_archived_manuscript_gaps``. Gate run
39960871624 is not a close. Local Lean is not invoked.
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
    "U09.1": "companion_缩: legal allocation effects / 法律关系消灭",
    "U04.3": "companion_缩: 校准/因果/数值求准（非本条声称）",
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
    "U07.1": [
        "Full observation/history decoding acceptance is not stated by the retraction, separation, or encode witnesses.",
    ],
    "U07.2": [
        "Actual semantic compatibility of supplied layers remains a separate unproved obligation.",
    ],
    "U07.3": [
        "Source truth and arbitrary extractor fidelity are not proved by the fixed-history projection theorem.",
    ],
    "U03.1": [
        "Provenance DAG validation is not connected to the executable finite closure, and the robust-intersection countermodel is not connected to that closure.",
    ],
    "U03.2": [
        "A verified finite carrier/fuel bound for this list implementation is still missing.",
    ],
    "U02.1": [
        "Actual-world and actual-successor refinement of the concrete pipeline table remains unproved.",
    ],
    "U02.3": [
        "Generator support coverage is not stated by the finite enumeration, the common-idle witness, or the zero-coverage witness.",
    ],
    "U08.1": [
        "Late retroactive-transition and mutable-current-status countermodels are not audited declarations of this clause.",
    ],
    "U10.1": [
        "Complete protocol refinement remains unproved. The Pipeline refresh-to-Step link does not state it.",
    ],
    "U10.2": [
        "Full mixed-operation coverage, Gamma frame/read-domain correspondence, and service refinement remain open.",
    ],
    "U08.2": [
        "Current versus reachable exhaustion and nonempty-state preservation of every observation remain only partially formalized.",
    ],
    "U08.3": [
        "Full finite dependency-policy reflection and compatibility-world classification still need an audit that these four-state declarations do not provide.",
    ],
    "U10.3": [
        "Business-observation faithfulness and an explicit zero-step prohibition are not stated by the length bound, the rank bound, or the two-cycle witness.",
    ],
    "U09.1": [
        "Receipt revision ordering, cash uniqueness beyond ReceiptCoherent, and product-protocol refinement remain open. They are not the legal-allocation non-goal.",
    ],
    "U09.3": [
        "Full greedy prefix/ordering and same-institution legal-effect countermodels remain unproved.",
    ],
    "U01.1": [
        "The iid sample-mean/sqrt-radius specialization and the representation-risk decomposition are not finished by fixed_class_tail or approximate_erm.",
    ],
    "U01.2": [
        "General measurable bounded-loss integration and a jointly estimated bridge budget remain unproved.",
    ],
    "U01.3": [
        "The manuscript general measurable-distribution TV theorem is UNPROVED and is not reduced to the finite-support bound.",
    ],
    "U04.2": [
        "Width, beta integrals, the three-event sharp identified set, and contamination subclaims remain unproved.",
    ],
    "U04.3": [
        "Existence and uniqueness of the fully penalized logistic minimizer, including the intercept coordinate, remain UNPROVED. The unpenalized-intercept counterexamples do not state them. Run 39783481932 does not discharge them.",
    ],
    "U04.5": [
        "A general joint likelihood/copy theorem and the sigma-field information argument remain unproved.",
    ],
    "U05.2": [
        "A conditional-expectation Brier decomposition, simultaneous threshold coverage, and rare-group examples remain unproved. The algebraic Bernoulli identity is not that decomposition.",
    ],
    "U06.1": [
        "The full Bellman optimum, the blocked terminal convention, and the nonrectangular counterexample remain unproved.",
    ],
    "U06.2": [
        "Mixed expectations and an explicit strategy/tree bridge remain unproved.",
    ],
    "U06.3": [
        "Arbitrary interval multiplication enclosure and general uncertainty comparison remain unproved.",
    ],
    "U06.4": [
        "The q-in-[0,1] out-of-range corollaries still have no audited declaration.",
    ],
    "U11.1": [
        "The g formula, K1/K2 selection, sharp support gaps, and measurement bridges remain unproved.",
    ],
    "U12.1": [
        "Complete causal/measurement interpretation and the support-gap identified range remain unproved. Finite IPW cancellation does not state them.",
    ],
    "U12.2": [
        "Damping, oscillation, and noncontraction-sufficiency counterexamples remain unproved.",
    ],
    "U12.3": [
        "Weighted uniform selection, MAR, and the full sequential-kernel likelihood-ratio theorem remain UNPROVED. The clipping identity does not state them.",
    ],
    "U12.4": [
        "Full frozen-model acceptance beyond the two incentive inequalities and the distinguishability counterexample is not established by citing the tip-pin audit of those two declarations.",
    ],
    "U13.1": [
        "The lawful statistical-evidence input-change counterexample and authority integration remain unproved.",
    ],
    "U13.2": [
        "Complete authorized rule/mechanism load and persistent storage refinement remain unproved.",
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
    "U15.1": [
        "Finite-state strict-improvement length and a no-parameter-convergence counterexample remain unproved.",
    ],
    "U14.2": [
        "Zero-N rejection and endogenous-size/common-cause counterexamples remain unproved.",
    ],
    "U15.2": [
        "Key-point regression and finite-observation indistinguishability examples remain unproved.",
    ],
    "U15.3": [
        "The five evidence levels are not completed by the two-point risks and the second-round consumer.",
    ],
}

SCOPE_REVIEW: dict[str, str] = {
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
        "accepted on tip-pin job 120345670150. Concrete store refinement and "
        "external effects are non-goals in this same row, not proved omissions."
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
    "subject": "e87543d836cd3cf83bbb5a65b74e47d9bfe31865",
    "run_id": 39933015422,
    "job_id": 120345670150,
    "axiom_audit": "PASS_REEXTRACTED_STANDARD_AXIOMS_ONLY",
    "verification": "evidence/ci-tip-e87543d8/verification.json",
}

GATE_ONLY_RUN = 39960871624
GATE_ONLY_SHA = "f080eee0ffeadb09d8fe404adb3dcddf326b4a11"
CRITERIA_PACK = "/home/box/shared/legal-math-reviewer/archive_gap_判据包_20261024/"
PREFIX = "JurisLean.Candidates.Final20261021."


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
    text = "WIRED_TO_TIP_PIN_DECLARATIONS"
    if goals:
        text += " || NON_GOAL_POINTER: " + " | ".join(goals)
    return text
