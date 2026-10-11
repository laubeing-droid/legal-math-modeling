"""W2-A batch B04 acceptance tests: D029-D036, group 04 请求权、抗辩及争点处理.

Six pieces per demand (docs/full-math/W2B_CLASSIFICATION.md §5.4):

1. Lean contract  — Contracts.demand_D029..D036 restated as this item's own
   semantics (verified by CI; the registration-format tests live in
   test_registration_bindings.py).
2. Python entry   — tools/full_math/implementation/claims_ref.py per-item
   entries computing the intermediate result from real structured input.
3. Independent checker — claims_check.py re-derives the contract inline;
   no witness callbacks, no expectations from the main implementation.
4. Downstream consumption — unified.pipeline run_case / step_event /
   run_trace consume the claims results through the adapters in
   claims_ref (build_case_input / build_environment /
   claims_trace_events).
5. Positive and adverse cases — the ALL_134 counterexample field of each
   demand is executed with per-item expectations.
6. Synthetic receipt — completion.validate_binding rows for DEMAND:D029-D036
   (the ``_binding_row`` template below is ready for the controller to
   back-fill BINDINGS.json).
"""
import json
import sys
from fractions import Fraction
from pathlib import Path

import pytest

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[2]
SPEC = REPO / 'tools/full_math/spec'
sys.path.insert(0, str(REPO))
sys.path.insert(0, str(REPO / 'tools/full_math'))
sys.path.insert(0, str(REPO / 'tools/unified_math_v2'))

# Shared bare module names (`reference`, `unified`, ...) exist in several
# tool trees.  Evict cached copies ONLY when the loaded copy is from a
# foreign tree: test_intake_group01 may already have imported the right
# tools/unified_math_v2 modules, and a blind re-import would create a
# second enum identity that fails `kind is LegalEventKind...` dispatch.
_existing_unified = sys.modules.get('unified')
if _existing_unified is None or \
        'unified_math_v2' not in str(getattr(_existing_unified, '__file__', '')):
    for _shared in ("reference", "unified", "unified_v21"):
        for _name in [m for m in sys.modules
                      if m == _shared or m.startswith(_shared + ".")]:
            del sys.modules[_name]

from tools.full_math.implementation import claims_check as K  # noqa: E402
from tools.full_math.implementation import claims_ref as R  # noqa: E402
import completion as C  # noqa: E402

# Pipeline-facing names are imported INSIDE the downstream test, not at
# module level: other suites in this directory re-resolve the shared bare
# `unified` tree at their own import time, and call-time imports are the
# only bindings that always match the lazy in-function imports inside
# unified.pipeline/process (claims_ref's adapters already import lazily).

DEMANDS = ("D029", "D030", "D031", "D032", "D033", "D034", "D035", "D036")

_RULE_TABLE = (("repay-principal", True, "principal-repayment"),
               ("pay-interest", True, "incidental-interest"),
               ("alternative-rescission", True, "rescission"))
_FILED_ROWS = (("repay-principal", True, True),
               ("pay-interest", True, False))
_ALLOWED_TABLE = (("repay-principal", True), ("pay-interest", True),
                  ("punitive-damages", True))
_SCENARIO_ROWS = (("loan", "loan_granted", "principal-repayment"),
                  ("investment", "risk_taken", "profit-sharing"))
_DEFENSE_ROUTE_ROWS = (("investment_relation", False, True),
                       ("loan_admitted", True, False))
_ISSUE_ROWS = (("iss-repayment", "repay-principal", "investment_relation",
                "defendant", "loan_granted"),
               ("iss-interest", "pay-interest", "rate_excessive",
                "plaintiff", "rate_clause"))
_DEFENSE_LINK_ROWS = (("loan_admitted", "repay-principal",
                       "transfer_receipt", True, True),
                      ("investment_relation", "repay-principal",
                       "chat_history", False, False),
                      ("debt_admitted", "repay-principal", "iou_note",
                       True, False))
_SHARES = (("D1", Fraction(2, 5)), ("D2", Fraction(3, 5)))
_TOTAL = Fraction(1_000_000)
_EXTERNAL = (("D1", Fraction(400_000)), ("D2", Fraction(600_000)))


# ---------------------------------------------------------------------------
# 2/3/5 — entry + independent checker, positive and adverse (per item)
# ---------------------------------------------------------------------------


def _run_D029():
    """互斥备位请求不能默认同时全额受偿（ALL_134 反例字段）."""
    claims = R.enumerate_claims(_RULE_TABLE, "repay-principal",
                                "alternative-rescission", True, True,
                                Fraction(1_000_000), Fraction(58_000))
    ok, reasons = K.check_D029(_RULE_TABLE, "repay-principal",
                               "alternative-rescission", True, True,
                               Fraction(1_000_000), Fraction(58_000), claims)
    return ok, reasons, claims


def _run_D030():
    """生成与原告诉请相同不获得全部合法请求证书（ALL_134 反例字段）."""
    stages = R.claim_stages(_FILED_ROWS, _ALLOWED_TABLE)
    ok, reasons = K.check_D030(_FILED_ROWS, _ALLOWED_TABLE, stages)
    return ok, reasons, stages


def _run_D031():
    """投资抗辩不得既当承认借款又作相反事实（ALL_134 反例字段）."""
    scenarios = R.alternative_scenarios(_SCENARIO_ROWS)
    routing = R.route_defenses(_DEFENSE_ROUTE_ROWS)
    ok, r1 = K.check_D031(_SCENARIO_ROWS, _DEFENSE_ROUTE_ROWS,
                          dict(scenarios, **routing))
    return ok, r1, (scenarios, routing)


def _run_D032():
    """有效分支取本金规则、无效分支取收益规则拼接不合法（ALL_134 反例）."""
    fork = R.branch_fork("repay-principal", "v7")
    ok, reasons = K.check_D032("repay-principal", "v7", fork)
    return ok, reasons, fork


def _run_D033():
    """只有到期、无抗辩提出，不自动按时效驳回（ALL_134 反例字段）."""
    limitation = R.limitation_state(True, False, True, 2400)
    ok, reasons = K.check_D033(True, False, True, 2400, 1095, limitation)
    return ok, reasons, limitation


def _run_D034():
    """把反驳未成立当作对方主张已证明须拒绝此跳步（ALL_134 反例字段）."""
    graph = R.build_issue_graph(_ISSUE_ROWS)
    proved = R.claim_proved(True)
    out = dict(graph, proved=proved)
    ok, reasons = K.check_D034(_ISSUE_ROWS, True, out)
    return ok, reasons, out


def _run_D035():
    """模板中无来源的债务承认应触发审查而非静默写入（ALL_134 反例字段）."""
    defenses = R.link_defenses(_DEFENSE_LINK_ROWS)
    ok, reasons = K.check_D035(_DEFENSE_LINK_ROWS, defenses)
    return ok, reasons, defenses


def _run_D036():
    """连带责任外部给付与内部份额不得混为每人比例给付（ALL_134 反例字段）."""
    liability = R.joint_liability_model(_SHARES, _TOTAL, _EXTERNAL)
    ok, reasons = K.check_D036(_SHARES, _TOTAL, _EXTERNAL, liability)
    return ok, reasons, liability


_POSITIVE = {"D029": _run_D029, "D030": _run_D030, "D031": _run_D031,
             "D032": _run_D032, "D033": _run_D033, "D034": _run_D034,
             "D035": _run_D035, "D036": _run_D036}


@pytest.mark.parametrize("dem", DEMANDS)
def test_demand_positive(dem):
    """Entry computes the intermediate result; the independent checker
    re-derives the contract from the same input and passes."""
    ok, reasons, _out = _POSITIVE[dem]()
    assert ok, f"{dem} contract violated: {reasons}"


@pytest.mark.parametrize("dem", DEMANDS)
def test_demand_counterexample(dem):
    """The ALL_134 counterexample field of each demand is distinguishable
    in the entry output with per-item expectations."""
    _ok, _reasons, out = _POSITIVE[dem]()
    if dem == "D029":
        claims = out
        # 主请求受偿时互斥备位不默认同额受偿；候选=前提为真的表行
        assert claims["candidates"] == ("repay-principal", "pay-interest",
                                        "alternative-rescission")
        assert claims["awards"] == ("repay-principal",)
        assert "alternative-rescission" not in claims["awards"]
        assert claims["debts"]["principal"]["kind"] == "principal"
        assert claims["debts"]["incidental"]["kind"] == "incidental"
        assert claims["debts"]["principal"]["amount"] == Fraction(1_000_000)
        assert claims["debts"]["incidental"]["amount"] == Fraction(58_000)
    elif dem == "D030":
        stages = out
        # 允许表有已提之外的行：回声已提清单不获得全部允许证书；
        # 受偿 ⊆ 支持 ⊆ 已提 逐层成立；四载体两两不同
        assert stages["echo_is_all_allowed"] is False
        assert "punitive-damages" in stages["allowed"]
        assert "punitive-damages" not in stages["filed"]
        assert set(stages["awarded"]) <= set(stages["supported"])
        assert set(stages["supported"]) <= set(stages["filed"])
        assert len(set(stages["stages"])) == 4
        assert stages["awarded"] == ("repay-principal",)
        assert stages["supported"] == ("repay-principal", "pay-interest")
    elif dem == "D031":
        scenarios, routing = out
        # 借贷/投资是共享同一交付的两张情景行；投资抗辩只进相反事实
        # 载体，绝不同时当承认借款
        rels = {s["relation"]: s for s in scenarios["scenarios"]}
        assert rels["loan"]["premise"] == "loan_granted"
        assert rels["investment"]["premise"] == "risk_taken"
        assert rels["loan"]["shared_delivery"] == \
            rels["investment"]["shared_delivery"]
        assert routing["admissions"] == ("loan_admitted",)
        assert routing["contras"] == ("investment_relation",)
        assert "investment_relation" not in routing["admissions"]
        assert routing["rejected_dual"] == ()
    elif dem == "D032":
        fork = out
        # 两支共享身份与版本；跨支拼接对 (valid, yield) 不在闭合表内
        b_valid, b_invalid = fork["branches"]
        assert b_valid[1:3] == b_invalid[1:3] == ("repay-principal", "v7")
        assert b_valid[0] != b_invalid[0]
        stitched = {row["pair"]: row["allowed"] for row in fork["stitched"]}
        assert stitched[("valid", "principal")] is True
        assert stitched[("invalid", "yield")] is True
        assert stitched[("valid", "yield")] is False
        assert stitched[("invalid", "principal")] is False
    elif dem == "D033":
        limitation = out
        # 到期而未抗辩：不自动驳回、债权存活；重新起算是另一本账
        assert limitation["expiry_met"] is True
        assert limitation["defense_raised"] is False
        assert limitation["dismissed"] is False
        assert limitation["claim_alive"] is True
        assert limitation["restart_from_ack"] == 2400 + 1095
    elif dem == "D034":
        graph = out
        # 五链逐节点分开携带；主张只由自身支持集证明；反驳不代行证明
        node = graph["nodes"][0]
        assert (node["claim"], node["rebuttal"], node["responsible_party"],
                node["attack_target"]) == ("repay-principal",
                                           "investment_relation",
                                           "defendant", "loan_granted")
        assert graph["proved"]["proved"] is True
        refused = R.claim_proved(False)
        assert refused["proved"] is False
    elif dem == "D035":
        defenses = out
        # 无来源承认进审查清单而非记录；每条答辩链接所回应请求/证据
        assert defenses["admissions"] == ("loan_admitted",)
        assert defenses["review_required"] == ("debt_admitted",)
        assert "debt_admitted" not in defenses["admissions"]
        by_prop = {l["prop"]: l for l in defenses["links"]}
        assert by_prop["investment_relation"]["responds_claim"] == \
            "repay-principal"
        assert by_prop["investment_relation"]["responds_evidence"] == \
            "chat_history"
    elif dem == "D036":
        liability = out
        # 同一模型联算：内部=份额×总额且守恒；外部=逐人给付账，
        # 不等额外部账不得混为每人比例（人均 500k ≠ D1 的 400k）
        assert [(r["party"], r["amount"]) for r in liability["internal"]] == \
            [("D1", Fraction(400_000)), ("D2", Fraction(600_000))]
        assert liability["internal_total"] == _TOTAL
        assert liability["external_total"] == _TOTAL
        assert [r["paid"] for r in liability["external"]] == \
            [Fraction(400_000), Fraction(600_000)]
        assert Fraction(_TOTAL, 2) == Fraction(500_000)
        assert liability["external"][0]["paid"] != Fraction(_TOTAL, 2)


@pytest.mark.parametrize("dem", DEMANDS)
def test_checker_rejects_tampered(dem):
    """The independent checker must fail a tampered intermediate result
    (the checker, not the entry, is the judge of the contract)."""
    ok, _reasons, out = _POSITIVE[dem]()
    assert ok  # sanity: the honest result passes its own checker
    if dem == "D029":
        claims = out
        tampered = dict(claims)
        tampered["awards"] = claims["awards"] + ("alternative-rescission",)
        bad, reasons = K.check_D029(_RULE_TABLE, "repay-principal",
                                    "alternative-rescission", True, True,
                                    Fraction(1_000_000), Fraction(58_000),
                                    tampered)
    elif dem == "D030":
        stages = out
        tampered = dict(stages, echo_is_all_allowed=True)
        bad, reasons = K.check_D030(_FILED_ROWS, _ALLOWED_TABLE, tampered)
    elif dem == "D031":
        scenarios, routing = out
        tampered = dict(routing)
        tampered["admissions"] = routing["admissions"] + \
            ("investment_relation",)
        bad, reasons = K.check_D031(_SCENARIO_ROWS, _DEFENSE_ROUTE_ROWS,
                                    dict(scenarios, **tampered))
    elif dem == "D032":
        fork = out
        tampered = dict(fork)
        tampered["stitched"] = tuple(
            dict(row, allowed=True) if row["pair"] == ("valid", "yield")
            else row for row in fork["stitched"])
        bad, reasons = K.check_D032("repay-principal", "v7", tampered)
    elif dem == "D033":
        limitation = out
        tampered = dict(limitation, dismissed=True, claim_alive=False)
        bad, reasons = K.check_D033(True, False, True, 2400, 1095, tampered)
    elif dem == "D034":
        graph = out
        tampered = dict(graph)
        tampered["nodes"] = tuple(
            dict(n, claim="伪造主张") if n["issue"] == "iss-repayment" else n
            for n in graph["nodes"])
        bad, reasons = K.check_D034(_ISSUE_ROWS, True, tampered)
    elif dem == "D035":
        defenses = out
        tampered = dict(defenses)
        tampered["admissions"] = defenses["admissions"] + ("debt_admitted",)
        bad, reasons = K.check_D035(_DEFENSE_LINK_ROWS, tampered)
    elif dem == "D036":
        liability = out
        tampered = dict(liability)
        tampered["external"] = ({"party": "D1", "paid": Fraction(500_000)},
                                {"party": "D2", "paid": Fraction(500_000)})
        bad, reasons = K.check_D036(_SHARES, _TOTAL, _EXTERNAL, tampered)
    assert not bad, f"{dem} checker accepted a tampered result: {reasons}"


# ---------------------------------------------------------------------------
# per-demand adverse specifics beyond the shared parametrized set
# ---------------------------------------------------------------------------


def test_D029_alternative_awarded_only_when_primary_fails():
    """主请求不成立时备位才受偿——互斥备位两个方向都不默认同额."""
    claims = R.enumerate_claims(_RULE_TABLE, "repay-principal",
                                "alternative-rescission", False, True,
                                Fraction(1_000_000), Fraction(58_000))
    assert claims["awards"] == ("alternative-rescission",)
    assert "repay-principal" not in claims["awards"]
    neither = R.enumerate_claims(_RULE_TABLE, "repay-principal",
                                 "alternative-rescission", False, False,
                                 Fraction(1_000_000), Fraction(58_000))
    assert neither["awards"] == ()


def test_D030_full_coverage_granted_when_nothing_beyond_filed():
    """允许集无已提之外的行时，回声清单才获得全部允许证书."""
    same = R.claim_stages(_FILED_ROWS, (("repay-principal", True),
                                        ("pay-interest", True)))
    assert same["echo_is_all_allowed"] is True


def test_D031_dual_flagged_defense_enters_neither_carrier():
    """双标记行（既承认又相反）不进任何载体并触发审查."""
    routing = R.route_defenses((("both_flag", True, True),
                                ("plain", True, False)))
    assert routing["admissions"] == ("plain",)
    assert routing["contras"] == ()
    assert routing["rejected_dual"] == ("both_flag",)


def test_D033_defense_raised_dismisses_expired_claim():
    """到期且抗辩提出才驳回（两开关齐备）."""
    dismissed_case = R.limitation_state(True, True, False, 100)
    assert dismissed_case["dismissed"] is True
    assert dismissed_case["claim_alive"] is False
    alive_case = R.limitation_state(False, True, False, 100)
    assert alive_case["dismissed"] is False


def test_D034_proof_status_never_reads_the_rebuttal():
    """支持集未立时主张不证明——反驳状态不代行证明."""
    assert R.claim_proved(False) == {"proved": False,
                                     "source": "own-support-set"}
    assert R.claim_proved(True)["source"] == "own-support-set"


def test_D035_sourced_only_record_when_no_unsourced_admission():
    """全部承认带来源时审查清单为空."""
    defenses = R.link_defenses((("a", "c0", "ev1", True, True),))
    assert defenses["admissions"] == ("a",)
    assert defenses["review_required"] == ()


def test_D036_equal_shares_internal_matches_per_capita_only_then():
    """份额相等时内部账才与人均账重合——不等额外部账永不混同."""
    liability = R.joint_liability_model((("D1", Fraction(1, 2)),
                                         ("D2", Fraction(1, 2))),
                                        _TOTAL, _EXTERNAL)
    assert [r["amount"] for r in liability["internal"]] == \
        [Fraction(500_000), Fraction(500_000)]
    ok, reasons = K.check_D036((("D1", Fraction(1, 2)), ("D2", Fraction(1, 2))),
                               _TOTAL, _EXTERNAL, liability)
    assert ok, reasons


# ---------------------------------------------------------------------------
# 4 — downstream consumption: run_case / step_event / run_trace
# ---------------------------------------------------------------------------


def test_downstream_pipeline_consumes_claims():
    """run_case consumes the CaseInput assembled from the claims results
    (the D029 primary candidate's remedy as issue, the D031-routed
    investment assertion as a defense targeting the claim — never an
    admission, the D035 sourced admission as the only newly admitted
    fact); run_trace consumes the candidates as evidence events plus the
    D036 per-obligor external payments."""
    # call-time imports: always the same unified copies the pipeline's own
    # lazy in-function imports resolve to (see module docstring note).
    # Call-time PATH re-assertion first: test_registration_bindings inserts
    # tools/full_math at sys.path[0] at its own import time, which happens
    # AFTER this module's import (e < r), and tools/full_math carries a
    # competing bare `reference` package (without unified_reference) that
    # would shadow tools/unified_math_v2 at the lazy-import moment.
    _v2 = str(REPO / 'tools/unified_math_v2')
    while _v2 in sys.path:
        sys.path.remove(_v2)
    sys.path.insert(0, _v2)
    from theory.spec.canonical_v2.case import RunStatus
    from theory.spec.canonical_v2.kernel import Judgment
    from unified.pipeline import run_case, run_trace, step_event
    from unified.process import gross_of

    intake = R.build_claims_intake()
    case = R.build_case_input(intake)
    env = R.build_environment(intake)

    # the assembled carriers are exactly the claims outputs
    assert case.issues == ("PRINCIPAL_REPAYMENT",)  # D029 primary remedy
    assert case.claims[0].claimant == "plaintiff"
    assert case.claims[0].respondent == "defendant"
    # D031/D035: the investment assertion is a defense targeting c0,
    # never an admission of the loan
    assert case.defenses[0].defense_id == "def-investment"
    assert case.defenses[0].basis == "investment_relation"
    assert case.defenses[0].target_claims == ("c0",)
    standings = {(f.proposition.predicate, f.standing.name)
                 for f in case.fact_records}
    # D035: the sourced admission is admitted; the unsourced template
    # admission stays awaiting review — nothing was silently written
    assert ("loan_granted", "ADMITTED_POSITIVE") in standings
    assert ("transfer_made", "ADMITTED_POSITIVE") in standings
    assert ("investment_relation", "AWAITING_ADMISSION") in standings

    run = run_case(case, env)
    assert run.status is RunStatus.COMPLETE
    assert run.failures == ()
    judgments = run.judgments_of("c0")
    assert judgments and Judgment.ESTABLISHED in judgments

    # trace: the D029 candidates become evidence events; the D036
    # external per-obligor payments land on the claim basis (the two
    # separate gross entries are 400k/600k, never a 500k/500k average)
    events = R.claims_trace_events(intake)
    assert [e.event.event_id for e in events[:2]] == \
        ["ev-repay-principal", "ev-pay-interest"]
    final, notes = run_trace(case.initial_state, events, env)
    assert "ev:ev-repay-principal" in [e.evidence_id for e in final.evidence]
    event_ids = [e.event_id for e in final.events]
    assert "pay-D1" in event_ids and "pay-D2" in event_ids
    assert gross_of(final, "PRINCIPAL_REPAYMENT") == Fraction(1_000_000)
    allocated = [e for e in final.ledger
                 if e.kind.name == "GROSS_ALLOCATED"
                 and e.basis_key == "PRINCIPAL_REPAYMENT"]
    assert sorted(e.amount for e in allocated) == [Fraction(400_000),
                                                   Fraction(600_000)]
    assert notes  # the step relation actually produced observations

    # step_event alone: one step, exactly the event's own semantics
    one = step_event(case.initial_state, events[0], env)
    assert [e.evidence_id for e in one.next_state.evidence] == \
        ["ev:ev-repay-principal"]
    assert one.next_env is env

    # the claims decisions stay on the bundle: the alternative was not
    # co-awarded (D029), the allowed echo was refused (D030), the
    # investment defense routed without admission (D031), the cross-branch
    # stitch was rejected (D032), the expired-but-undefended claim stayed
    # alive (D033), and the joint model conserved the total (D036)
    assert intake["claims"]["awards"] == ("repay-principal",)
    assert intake["stages"]["echo_is_all_allowed"] is False
    assert intake["routing"]["contras"] == ("investment_relation",)
    assert intake["fork"]["stitched"][2]["allowed"] is False
    assert intake["limitation"]["claim_alive"] is True
    assert intake["liability"]["internal_total"] == Fraction(1_000_000)


# ---------------------------------------------------------------------------
# 6 — synthetic receipts through completion.validate_binding
# ---------------------------------------------------------------------------

_REQUIREMENTS = {
    r["id"]: r
    for r in json.loads((SPEC / 'REQUIREMENTS.json').read_text(encoding='utf-8'))
}

_SEMANTICS = {
    "D029": "claim candidates are exactly the remedy combinations the "
            "given facts and the rule table allow (each candidate sits in "
            "the table with a true premise, and every premise-true row is "
            "a candidate); the principal performance and the incidental "
            "costs stay independent debt items; mutually exclusive "
            "alternative claims are never both fully awarded by default "
            "— the alternative enters the award carrier only when the "
            "primary claim is not satisfied.",
    "D030": "FiledClaims, AllowedClaims, SupportedClaims and "
            "AwardedClaims are four distinct carriers with the explicit "
            "chain awarded ⊆ supported ⊆ filed; merely echoing the filed "
            "list never earns the all-allowed certificate when the "
            "allowed table has rows beyond the filed claims.",
    "D031": "loan and investment are distinct scenario rows sharing the "
            "same delivered sum, each exporting its own premise and "
            "conclusion; the admission-of-loan and contrary-fact "
            "carriers are mutually exclusive, so the defendant's "
            "investment defense is never both an admission of the loan "
            "and the opposite fact.",
    "D032": "branches forked from one claim share its identity and the "
            "input version while staying distinct rows; the "
            "applicable-rule table is declared closed per regime "
            "(valid→principal, invalid→yield), so the cross-branch "
            "stitch pairs are rejected.",
    "D033": "expiry, the defense being raised, the subsequent "
            "acknowledgment and the period restart are computed as "
            "separate switches; dismissal requires both the period met "
            "and the defense raised — expiry alone never deletes the "
            "claim — and the interruption restart is its own ledger.",
    "D034": "the issue graph links claim, rebuttal, responsible party, "
            "support set and attack target separately per node; a claim "
            "is proved only through its own support set — a rebuttal "
            "failing (or holding) never proves the other side's claim by "
            "itself (the jump is refused).",
    "D035": "every defense proposition links the claim and the evidence "
            "it responds to; a new admission enters the record only with "
            "its own authorization source — an unsourced admission from "
            "a template is flagged for review, never silently written.",
    "D036": "liable party, method, share and amount are computed jointly "
            "by one liability model (internal rows are share × total and "
            "conserve the total); the external payment ledger is a "
            "separate per-obligor carrier and is never read as a "
            "per-capita proportional award.",
}

_ENTRY = {
    "D029": "enumerate_claims",
    "D030": "claim_stages",
    "D031": "alternative_scenarios/route_defenses",
    "D032": "branch_fork/stitched_rule",
    "D033": "limitation_state",
    "D034": "build_issue_graph/claim_proved",
    "D035": "link_defenses",
    "D036": "joint_liability_model",
}


def _binding_row(dem, required):
    """Template for the controller's BINDINGS.json back-fill
    (DEMAND:D029–D036 rows).  Passes completion.validate_binding as-is."""
    return {
        "id": f"DEMAND:{dem}",
        "theorem": required["theorem"],
        "contract": required["contract"],
        "proof_mode": "KERNEL_CONTRACT_PROOF",
        "formal_scope": "Group-04 claims/issues demand instance in the "
                        "shared semantic framework: this item's own "
                        "contract semantics plus the registered "
                        "argument-construction component (bounded "
                        "generation is sound — every generated argument "
                        "is well-formed with height at most the budget), "
                        "with its adverse case executed as a negative "
                        "test.",
        "independent_semantics": _SEMANTICS[dem],
        "algorithm": f"tools/full_math/implementation/claims_ref.py "
                     f"{_ENTRY[dem]} computes the intermediate result from "
                     f"structured input; claims_check.check_{dem} "
                     f"re-derives the contract independently.",
        "observation_contract": "Inputs are the declared structures "
                                "(rule-table rows with premises and "
                                "remedies plus primary/alternative award "
                                "switches and debt amounts, filed rows "
                                "with support/award flags and an allowed "
                                "table, relation rows over one delivered "
                                "sum with defense routing flags, branch "
                                "identity/version pairs with the closed "
                                "regime-rule table, limitation switches "
                                "with the acknowledgment day, issue rows "
                                "with five link fields and a support "
                                "switch, defense rows with targets and "
                                "admission/source flags, party/share "
                                "rows with a total and per-obligor "
                                "payments); outputs are exactly the "
                                "contract quantities (the candidate and "
                                "award carriers with the separate debt "
                                "items, the four stage carriers with the "
                                "echo verdict, the scenario rows and the "
                                "exclusive routing carriers, the "
                                "shared-identity branches with the "
                                "stitch verdicts, the separate "
                                "limitation switches with their own "
                                "restart ledger, the five-link graph "
                                "with the proof status, the linked "
                                "defenses with the admissions/review "
                                "split, and the joint liability rows "
                                "with the separate external ledger).",
        "external_assumptions": "Claim-strategy selection, text-to-claim "
                                "understanding, substantive relation "
                                "classification, fact-finding and "
                                "interpretation choices, knowledge-time "
                                "and demand-conduct proofs, issue-"
                                "discovery recall, defense quality and "
                                "argument sufficiency, proportionality "
                                "evaluation and damage facts remain "
                                "external validation obligations, not "
                                "part of this registration.",
        "proof_sources": [
            "proofs/lean/juris_lean/JurisLean/FullMath/Contracts.lean",
            "proofs/lean/juris_lean/JurisLean/FullMath/Acceptance.lean",
        ],
        "implementation_sources": [
            "tools/full_math/implementation/claims_ref.py",
            "tools/full_math/implementation/claims_check.py",
        ],
        "test_ids": [
            "tools/full_math/implementation_tests::test_claims_group04.py::"
            f"test_demand_positive[{dem}]",
            "tools/full_math/implementation_tests::test_claims_group04.py::"
            f"test_demand_counterexample[{dem}]",
            "tools/full_math/implementation_tests::test_claims_group04.py::"
            "test_downstream_pipeline_consumes_claims",
        ],
        "negative_test_ids": [
            "tools/full_math/implementation_tests::test_claims_group04.py::"
            f"test_checker_rejects_tampered[{dem}]",
        ],
        "semantic_links": [
            "JurisLean.FullMath.Logic.generate_sound",
        ],
    }


@pytest.mark.parametrize("dem", DEMANDS)
def test_b04_binding_receipt(dem):
    """Synthetic receipt: the binding row for DEMAND:D0XX passes
    completion.validate_binding against the real repository files."""
    required = _REQUIREMENTS[f"DEMAND:{dem}"]
    C.validate_binding(_binding_row(dem, required), required, repo=REPO)


@pytest.mark.parametrize("dem", DEMANDS)
def test_b04_binding_receipt_negative(dem):
    """A tampered receipt (swapped theorem) is rejected."""
    required = _REQUIREMENTS[f"DEMAND:{dem}"]
    row = dict(_binding_row(dem, required))
    row["theorem"] = "JurisLean.FullMath.Acceptance.nonexistent_demand"
    with pytest.raises(C.EvidenceError):
        C.validate_binding(row, required, repo=REPO)
