"""W2-A batch B06 acceptance tests: D047-D056, group 06 借贷、担保与
共同债务.

Six pieces per demand (docs/full-math/W2B_CLASSIFICATION.md §5.4):

1. Lean contract  — Contracts.demand_D047..D056 restated as this item's own
   semantics over the shared quantity-ledger carrier
   (Seams/UnifiedQuantLedger, the green B06 prerequisite); verified by the
   whole-repo replay build, and the registration-format tests live in
   test_registration_bindings.py.
2. Python entry   — tools/full_math/implementation/loan_ref.py per-item
   entries computing the intermediate result from real structured input
   (the ledger surface consumed from quantledger_ref, the Python mirror
   of JurisLean.Seams.UnifiedQuantLedger).
3. Independent checker — loan_check.py re-derives the contract inline
   with different code paths (index-walking allocations, direct division,
   branch tables, occurrence counting); no witness callbacks, no
   expectations from the main implementation, zero code sharing.
4. Downstream consumption — unified.pipeline run_case / step_event /
   run_trace consume the loan results through the adapters in loan_ref
   (build_case_input / build_environment / loan_trace_events).
5. Positive and adverse cases — the ALL_134 counterexample field of each
   demand is executed with per-item expectations.
6. Synthetic receipt — completion.validate_binding rows for
   DEMAND:D047-D056 (the ``_binding_row`` template below is ready for
   the controller to back-fill BINDINGS.json).
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
# foreign tree: an earlier suite may already have imported the right
# tools/unified_math_v2 modules, and a blind re-import would create a
# second enum identity that fails `kind is LegalEventKind...` dispatch.
_existing_unified = sys.modules.get('unified')
if _existing_unified is None or \
        'unified_math_v2' not in str(getattr(_existing_unified, '__file__', '')):
    for _shared in ("reference", "unified", "unified_v21"):
        for _name in [m for m in sys.modules
                      if m == _shared or m.startswith(_shared + ".")]:
            del sys.modules[_name]

from tools.full_math.implementation import loan_check as K  # noqa: E402
from tools.full_math.implementation import loan_ref as R  # noqa: E402
import completion as C  # noqa: E402

# Pipeline-facing names are imported INSIDE the downstream test, not at
# module level (same rationale as test_drafting_group12).

DEMANDS = ("D047", "D048", "D049", "D050", "D051", "D052", "D053",
           "D054", "D055", "D056")

F = Fraction

_DEMO = (
    R.LedgerItem(1, R.KIND_ATTORNEY, R.BASIS_CONTRACT, 0,
                 R.STATUS_SUPPORTED, F(10)),
    R.LedgerItem(2, R.KIND_INTEREST, R.BASIS_CONTRACT, 0,
                 R.STATUS_SUPPORTED, F(100)),
    R.LedgerItem(3, R.KIND_PRINCIPAL, R.BASIS_CONTRACT, 0,
                 R.STATUS_SUPPORTED, F(200)),
)

_FEES = (
    R.LedgerItem(6, R.KIND_ATTORNEY, R.BASIS_CONTRACT, 2,
                 R.STATUS_SUPPORTED, F(3000)),
    R.LedgerItem(7, R.KIND_COURT, R.BASIS_CONTRACT, 0,
                 R.STATUS_SUPPORTED, F(500)),
    R.LedgerItem(8, R.KIND_PRESERVATION, R.BASIS_CONTRACT, 0,
                 R.STATUS_SUPPORTED, F(200)),
)

_FEE_TUPLES = (
    (6, "attorneyFee", "contractStip", 2, "supported", F(3000)),
    (7, "courtFee", "contractStip", 0, "supported", F(500)),
    (8, "preservationFee", "contractStip", 0, "supported", F(200)),
)

_SIG_ROWS = (
    R.LedgerItem(11, R.KIND_PRINCIPAL, R.BASIS_CONTRACT, 0,
                 R.STATUS_SUPPORTED, F(200)),
    R.LedgerItem(12, R.KIND_INTEREST, R.BASIS_CONTRACT, 2,
                 R.STATUS_SUPPORTED, F(50)),
)


# ---------------------------------------------------------------------------
# 2/3/5 — entry + independent checker, positive and adverse (per item)
# ---------------------------------------------------------------------------


def _run_D047():
    """出借记录不能自动证明后来未清偿（ALL_134 反例字段）."""
    out = R.loan_discharge(True, 1, F(200), [F(150)])
    rep = K.check_D047(True, 1, F(200), [F(150)], out)
    return rep.ok, rep.reasons, out


def _run_D048():
    """同一还款同时全额扣本金、又全额扣利息应拒绝（ALL_134 反例字段）."""
    out = {
        "offset": R.offset_ledger(_DEMO, [F(150), F(60)]),
        "demo": R.demo_offset_150(),
        "double_full": R.double_full_rejected(F(150)),
    }
    reps = (
        K.check_D048([it.kind for it in _DEMO],
                     [it.amount for it in _DEMO],
                     [it.ident for it in _DEMO], [F(150), F(60)],
                     out["offset"]["rows"], out["offset"]["final_balance"],
                     [it.ident for it in _DEMO]),
        K.check_D048_stream_gates(out["offset"]),
        K.check_D048_double_full(out["double_full"]),
        K.check_D048_demo(out["demo"]),
    )
    reasons = [r for rep in reps for r in rep.reasons]
    return all(rep.ok for rep in reps), reasons, out


def _run_D049():
    """相似百分比不能默认三项全叠加（ALL_134 反例字段）."""
    out = {
        "report": R.charges_report(F(100), 1, F(1, 10), 1, F(1, 10), 1,
                                   F(1, 10), 1, F(24)),
        "stacking": R.stacking_not_default(),
    }
    reps = (
        K.check_D049(F(100), 1, F(1, 10), 1, F(1, 10), 1, F(1, 10), 1,
                     F(24), out["report"]),
        K.check_D049_stacking(out["stacking"]),
    )
    reasons = [r for rep in reps for r in rep.reasons]
    return all(rep.ok for rep in reps), reasons, out


def _run_D050():
    """签担保文件不自动证明登记完成或财产已交付（ALL_134 反例字段）."""
    out = R.security_readout(["signed", "registered"])
    rep = K.check_D050(["signed", "registered"], [F(100), F(100)],
                       F(150), out)
    return rep.ok, rep.reasons, out


def _run_D051():
    """仅无决议字段不得由一条统一规则宣布所有担保无效（ALL_134 反例字段）."""
    out = R.corp_guarantee(["signed"])
    rep = K.check_D051(["signed"], out)
    return rep.ok, rep.reasons, out


def _run_D052():
    """签名文本为自然人名不自动由其个人承担全部合同义务（ALL_134 反例字段）."""
    out = R.signature_attribution(3, "onBehalfOf", 7, _SIG_ROWS, F(50))
    rep = K.check_D052(3, "onBehalfOf", 7,
                       [(it.ident, it.beneficiary) for it in _SIG_ROWS],
                       out, F(50))
    return rep.ok, rep.reasons, out


def _run_D053():
    """婚内借款不自动推出夫妻共同债务（ALL_134 反例字段）."""
    out = R.spousal_attribution(True, False, False, False)
    rep = K.check_D053(True, False, False, False, out)
    return rep.ok, rep.reasons, out


def _run_D054():
    """共用电话不直接生成无限连带责任边（ALL_134 反例字段）."""
    out = R.veil_readout(["sharedPhone"])
    rep = K.check_D054(["sharedPhone"], out)
    return rep.ok, rep.reasons, out


def _run_D055():
    """收入低不自动证明不可能现金出借（ALL_134 反例字段）."""
    cands = [(True, 3), (False, 3), (True, 4)]
    out = R.fund_source_readout(cands)
    rep = K.check_D055(cands, out)
    return rep.ok, rep.reasons, out


def _run_D056():
    """自身工时报价不能自动作为对方应赔律师费（ALL_134 反例字段）."""
    out = R.fee_ledger_readout(_FEES)
    rep = K.check_D056(_FEE_TUPLES, out)
    return rep.ok, rep.reasons, out


_POSITIVE = {"D047": _run_D047, "D048": _run_D048, "D049": _run_D049,
             "D050": _run_D050, "D051": _run_D051, "D052": _run_D052,
             "D053": _run_D053, "D054": _run_D054, "D055": _run_D055,
             "D056": _run_D056}


@pytest.mark.parametrize("dem", DEMANDS)
def test_demand_positive(dem):
    """Entry computes the intermediate result; the independent checker
    re-derives the contract from the same input with different code
    paths and passes."""
    ok, reasons, _out = _POSITIVE[dem]()
    assert ok, f"{dem} contract violated: {reasons}"


@pytest.mark.parametrize("dem", DEMANDS)
def test_demand_counterexample(dem):
    """The ALL_134 counterexample field of each demand is distinguishable
    in the entry output with per-item expectations."""
    _ok, _reasons, out = _POSITIVE[dem]()
    if dem == "D047":
        loan = out
        # 交付与清偿分别读出；出借记录不蕴含未清偿；补足流即清偿
        assert loan["booked"] == F(200)
        assert loan["balance_after"] == F(50)
        assert loan["discharged"] is False
        assert loan["discharged_iff_covered"] is True
        assert loan["undelivered_balance_zero"] is True
        assert loan["record_alone_implies_unpaid"] is False
        assert loan["full_stream_discharges"] is True
    elif dem == "D048":
        offset, demo, double = out["offset"], out["demo"], out["double_full"]
        # 准入顺序抵充 (10, 100, 40)，余额 160；全额付清 350 清零
        assert demo["part_allocs"] == [F(10), F(100), F(40)]
        assert demo["part_balance"] == F(160)
        assert demo["full_allocs"] == [F(10), F(100), F(200)]
        assert demo["full_balance"] == F(0)
        # 逐笔界、身份保持、同 ID 重复拒绝
        assert offset["row_nonneg"] is True
        assert offset["row_within_payment"] is True
        assert offset["idents_preserved"] is True
        assert offset["duplicate_id_rejected"] is True
        assert offset["distinct_ids_legal"] is True
        # 双全额行被拒：真实抵充 [100, 50] ≠ [100, 200]
        assert double["real_allocs"] == [F(100), F(50)]
        assert double["double_full_exceeds_payment"] is True
        assert double["never_equals_real"] is True
    elif dem == "D049":
        report, stacking = out["report"], out["stacking"]
        # 三组件独立、分段可加；全叠加 30 超限 24 被拒，20 在限内
        assert report["term_independent_of_overdue"] is True
        assert report["seg_split_sums"] is True
        assert report["components_sum"] is True
        assert report["within_cap"] is False
        assert stacking["all_total"] == F(30)
        assert stacking["all_within_24"] is False
        assert stacking["no_penalty_total"] == F(20)
        assert stacking["no_penalty_within_24"] is True
    elif dem == "D050":
        sec = out
        # 三要件事件互异；仅有签署不设立抵押/质押；登记设立抵押
        assert sec["required_events"] == {"suretyship": "signed",
                                          "mortgage": "registered",
                                          "pledge": "delivered"}
        assert sec["required_events_distinct"] is True
        assert sec["signing_only_establishes_mortgage"] is False
        assert sec["signing_only_establishes_pledge"] is False
        assert sec["registered_mortgage_established"] is True
        assert sec["delivered_pledge_established"] is True
        # 顺位瀑布：[100, 50]＋剩余 0 守恒；后顺位得正⇒前顺位全清
        assert sec["priority_rows"] == [F(100), F(50)]
        assert sec["distribution_conserved"] is True
        assert sec["later_positive_implies_earlier_full"] is True
    elif dem == "D051":
        corp = out
        # 公司保证＝决议∧签署；同"仅签署"事件集：公司未设立、自然人设立
        assert corp["corp_established"] is False
        assert corp["needs_both"] is True
        assert corp["resolution_alone_insufficient"] is True
        assert corp["same_events_corp_not_established"] is True
        assert corp["same_events_natural_surety_established"] is True
        assert corp["no_blanket_invalidation"] is True
    elif dem == "D052":
        sig = out
        # 代表关系指向公司 7 ⇒ 责任人 7 ≠ 签字自然人 3；受益人逐笔保持
        assert sig["responsible"] == 7
        assert sig["signer"] == 3
        assert sig["signer_bears_all"] is False
        assert sig["natural_name_is_signer"] is True
        assert sig["beneficiaries_before"] == [0, 2]
        assert sig["beneficiaries_after"] == [0, 2]
        assert sig["beneficiaries_preserved"] is True
        own = R.signature_attribution(3, "ownName")
        assert own["responsible"] == 3 and own["signer_bears_all"] is True
    elif dem == "D053":
        spo = out
        # 婚姻期间翻转不变；婚内无签字/意思/用途非共同；签字或意思+用途成立
        assert spo["joint"] is False
        assert spo["marriage_flip_invariant"] is True
        assert spo["married_alone_not_joint"] is True
        assert spo["signature_suffices"] is True
        assert spo["intent_use_suffice"] is True
    elif dem == "D054":
        veil = out
        # 共用电话不达人格混同、不生成连带；资金混同/单向控制两项皆达
        assert veil["mix"] is False
        assert veil["joint_due"] is False
        assert veil["consequence_is_evaluation"] is True
        assert veil["phone_only_no_mix"] is True
        assert veil["phone_address_no_liability"] is True
        assert veil["commingled_reaches_both"] is True
        assert veil["control_reaches_both"] is True
    elif dem == "D055":
        funds = out
        # 无源不进事实；有源准入；同 ID 双角色判定不同；无规则不造负事实
        assert funds["unsourced_unproven"] is True
        assert funds["sourced_admitted"] is True
        assert funds["same_id_sourced_unsourced_differ"] is True
        assert funds["cash_rules"] == []
        assert funds["no_income_low_to_impossible_rule"] is True
        assert funds["insufficiency_is_unproven_not_negative"] is True
    elif dem == "D056":
        fees = out
        # 三费用分型互异；自报工时不自动 supported；约定基础可 supported
        assert fees["fee_kinds_distinct"] is True
        assert fees["rows_consistent"] is True
        assert fees["self_quoted_supported"] is False
        assert fees["stipulated_supported"] is True
        assert fees["beneficiary_total"] == F(3000)
        assert fees["partition_conserved"] is True


@pytest.mark.parametrize("dem", DEMANDS)
def test_checker_rejects_tampered(dem):
    """The independent checker must fail a tampered intermediate result
    (the checker, not the entry, is the judge of the contract)."""
    ok, _reasons, out = _POSITIVE[dem]()
    assert ok  # sanity: the honest result passes its own checker
    if dem == "D047":
        tampered = dict(out)
        tampered["balance_after"] = F(0)  # unread balance discharged
        rep = K.check_D047(True, 1, F(200), [F(150)], tampered)
    elif dem == "D048":
        tampered = dict(out["double_full"])
        tampered["real_allocs"] = [F(100), F(200)]  # double-full accepted
        rep = K.check_D048_double_full(tampered)
    elif dem == "D049":
        tampered = dict(out["report"])
        tampered["within_cap"] = True  # 30-over-24 stacking accepted
        rep = K.check_D049(F(100), 1, F(1, 10), 1, F(1, 10), 1, F(1, 10),
                           1, F(24), tampered)
    elif dem == "D050":
        tampered = dict(out)
        tampered["signing_only_establishes_mortgage"] = True  # sign=register
        rep = K.check_D050(["signed", "registered"], [F(100), F(100)],
                           F(150), tampered)
    elif dem == "D051":
        tampered = dict(out)
        tampered["corp_established"] = True  # resolution-less corp surety
        rep = K.check_D051(["signed"], tampered)
    elif dem == "D052":
        tampered = dict(out)
        tampered["responsible"] = 3  # natural-person bears it all
        rep = K.check_D052(3, "onBehalfOf", 7,
                           [(it.ident, it.beneficiary) for it in _SIG_ROWS],
                           tampered, F(50))
    elif dem == "D053":
        tampered = dict(out)
        tampered["married_alone_not_joint"] = False  # marriage alone is joint
        rep = K.check_D053(True, False, False, False, tampered)
    elif dem == "D054":
        tampered = dict(out)
        tampered["phone_address_no_liability"] = False  # phone edge = joint
        rep = K.check_D054(["sharedPhone"], tampered)
    elif dem == "D055":
        tampered = dict(out)
        tampered["unsourced_unproven"] = False  # unsourced admitted
        rep = K.check_D055([(True, 3), (False, 3), (True, 4)], tampered)
    else:  # D056
        tampered = dict(out)
        tampered["self_quoted_supported"] = True  # self-quote supported
        rep = K.check_D056(_FEE_TUPLES, tampered)
    assert not rep.ok, f"{dem} checker accepted a tampered result: {rep.reasons}"


# ---------------------------------------------------------------------------
# 4 — downstream consumption through the unified pipeline
# ---------------------------------------------------------------------------

def test_downstream_pipeline_consumes_loan():
    """run_case consumes the CaseInput assembled from the loan/guarantee
    results (the delivered loan and the registered mortgage supply the
    issue, the record-alone-non-discharged proposition stays awaiting —
    never written, and the only quantities are the loan balance after
    the partial repayment and the stipulated attorney fee — two separate
    debt items that are never merged); run_trace consumes the
    admission-order offset payments (150 then 60 on the payable basis)
    plus the stipulated 3000-fen attorney fee on its own basis."""
    # call-time imports: always the same unified copies the pipeline's own
    # lazy in-function imports resolve to (see module docstring note).
    _v2 = str(REPO / 'tools/unified_math_v2')
    while _v2 in sys.path:
        sys.path.remove(_v2)
    sys.path.insert(0, _v2)
    from theory.spec.canonical_v2.case import RunStatus
    from theory.spec.canonical_v2.kernel import Judgment
    from unified.pipeline import run_case, run_trace, step_event
    from unified.process import gross_of

    intake = R.build_loan_intake()
    case = R.build_case_input(intake)
    env = R.build_environment(intake)

    # the assembled carriers are exactly the loan outputs
    assert case.issues == ("LOAN_GUARANTEE",)
    assert case.claims[0].claimant == "lender"
    assert case.claims[0].respondent == "client"
    # D051: the corporate-guarantee predicate gap rides on the case; the
    # record-alone-non-discharged proposition stays awaiting — never written
    assert case.defenses[0].defense_id == "def-corp-no-resolution"
    assert case.defenses[0].basis == "corporate_guarantee_unestablished"
    assert case.defenses[0].target_claims == ("c0",)
    standings = {(f.proposition.predicate, f.standing.name)
                 for f in case.fact_records}
    assert ("loan-delivered", "ADMITTED_POSITIVE") in standings
    assert ("guarantee-registered", "ADMITTED_POSITIVE") in standings
    assert ("record-alone-non-discharged", "AWAITING_ADMISSION") in standings
    # D047/D056: the only quantities are the loan balance (50) and the
    # stipulated attorney fee (3000) — separate debt items, never merged
    assert [q.value for q in case.quantities] == [Fraction(50),
                                                  Fraction(3000)]
    assert {q.basis_kind for q in case.quantities} == \
        {"loan-balance", "attorney-fee-stipulated"}

    run = run_case(case, env)
    assert run.status is RunStatus.COMPLETE
    assert run.failures == ()
    judgments = run.judgments_of("c0")
    assert judgments and Judgment.ESTABLISHED in judgments

    # trace: the two admission-order offset payments land on the payable
    # basis (150 + 60) and the stipulated attorney fee lands as its own
    # 3000-fen installment; the self-quoted basis receives nothing
    events = R.loan_trace_events(intake)
    assert [e.event.event_id for e in events[:2]] == \
        ["pay-offset-1", "pay-offset-2"]
    final, notes = run_trace(case.initial_state, events, env)
    event_ids = [e.event_id for e in final.events]
    assert "pay-offset-1" in event_ids
    assert "pay-attorney-stipulated" in event_ids
    assert gross_of(final, "PAYABLE_AMOUNT") == Fraction(210)
    assert gross_of(final, "ATTORNEY_FEE_STIPULATED") == Fraction(3000)
    allocated = [e for e in final.ledger
                 if e.kind.name == "GROSS_ALLOCATED"
                 and e.basis_key == "ATTORNEY_FEE_STIPULATED"]
    assert sorted(e.amount for e in allocated) == [Fraction(3000)]
    assert notes  # the step relation actually produced observations

    # step_event alone: one step, exactly the event's own semantics
    one = step_event(case.initial_state, events[0], env)
    assert one.next_env is env

    # the loan/guarantee decisions stay on the bundle: the separate
    # delivery/discharge readouts (D047), the offset ledger with its
    # gates (D048), the charge components under the cap (D049), the
    # typed security events (D050), the corporate predicates (D051),
    # the signature attribution (D052), the spousal attribution (D053),
    # the veil readout (D054), the fund-source readout (D055) and the
    # fee ledger (D056)
    assert intake["delivery"]["record_alone_implies_unpaid"] is False
    assert intake["offset"]["duplicate_id_rejected"] is True
    assert intake["double_full"]["never_equals_real"] is True
    assert intake["charges"]["within_cap"] is False
    assert intake["security"]["required_events_distinct"] is True
    assert intake["corp"]["no_blanket_invalidation"] is True
    assert intake["signature"]["signer_bears_all"] is False
    assert intake["spousal"]["married_alone_not_joint"] is True
    assert intake["veil"]["phone_only_no_mix"] is True
    assert intake["funds"]["no_income_low_to_impossible_rule"] is True
    assert intake["fees"]["self_quoted_supported"] is False


# ---------------------------------------------------------------------------
# 6 — synthetic receipts through completion.validate_binding
# ---------------------------------------------------------------------------

_REQUIREMENTS = {
    r["id"]: r
    for r in json.loads((SPEC / 'REQUIREMENTS.json').read_text(encoding='utf-8'))
}

_SEMANTICS = {
    "D047": "the delivery fact and the discharge fact enter the "
            "responsibility chain separately: only a delivered loan is "
            "booked (an undelivered IOU has a zero balance), discharge "
            "means the payment stream actually covered the booked "
            "amounts (balance zero iff paid covers due), and a lending "
            "record alone never implies later non-discharge — the same "
            "delivered ledger with a full repayment stream is "
            "discharged.",
    "D048": "the offset ledger updates in admission order: every "
            "allocation is nonnegative and within its payment, debt "
            "identities are preserved row by row (traceable balance), "
            "a duplicated payment id makes the stream illegal, and one "
            "repayment can never simultaneously cover the interest in "
            "full and the principal in full.",
    "D049": "term interest, overdue interest and the penalty are "
            "separate computation components (the term component is "
            "invariant under the overdue parameters; a period splits "
            "additively in integer days, never a 30-day month "
            "conversion), and their composition is subject to the "
            "applicable policy cap — similar percentages do not stack "
            "by default.",
    "D050": "suretyship, mortgage and pledge are distinct legal "
            "relations with distinct establishment events (contract, "
            "registration, delivery): a signed security document alone "
            "establishes neither the mortgage nor the pledge, and the "
            "collateral proceeds run down a priority waterfall with "
            "conservation and priority (a positive later rank implies "
            "full earlier coverage).",
    "D051": "resolution existence, procedure, representative authority "
            "and guarantee validity are separate predicates connected "
            "by rules: the corporate surety needs resolution AND "
            "signature, and on the very same signature-only event set "
            "the corporate guarantee is unestablished while the "
            "natural-person suretyship is established — no single "
            "blanket invalidation rule.",
    "D052": "signer, nominal capacity, the representation relation, "
            "the contract party and the responsible person are "
            "separately encoded: signing on behalf of a company makes "
            "the company (not the natural-person signer whose name is "
            "in the signature text) the responsible subject, and the "
            "ledger-side beneficiary field survives the offsetting "
            "row by row.",
    "D053": "marriage period, spouse signature, common intent, "
            "household/business use and debt attribution are "
            "independent issues: joint attribution requires the "
            "signature or the intent+use pair, flipping the "
            "marriage-period field never changes the attribution, and "
            "a marriage-period loan with no signature, intent or use "
            "is not a joint debt.",
    "D054": "the company-relation evidence forms a support graph and "
            "the personality-mixing evaluation is a separate rule "
            "layer: the joint-liability consequence attaches exactly "
            "through the evaluation (commingled funds or one-way "
            "control); a shared phone number alone generates no "
            "unlimited joint-liability edge.",
    "D055": "fund source and cash capability are sourced fact "
            "candidates: an unsourced candidate stays unproven (never "
            "admitted), a sourced one is admitted, and from "
            "income-low to cash-lending-impossible no rule is "
            "admitted — insufficiency of sources reads out unproven, "
            "never a fabricated negative fact.",
    "D056": "attorney fees, court fees and preservation fees are "
            "independent debt items with their own basis, beneficiary "
            "and claim status (three distinct fee kinds), a supported "
            "status requires a supporting basis — a self-quoted "
            "attorney-fee row is never auto-supported — and grouping "
            "the ledger conserves the total.",
}

_ENTRY = {
    "D047": "loan_discharge",
    "D048": "offset_ledger/demo_offset_150/double_full_rejected",
    "D049": "charges_report/stacking_not_default",
    "D050": "security_readout",
    "D051": "corp_guarantee",
    "D052": "signature_attribution",
    "D053": "spousal_attribution",
    "D054": "veil_readout",
    "D055": "fund_source_readout",
    "D056": "fee_ledger_readout",
}

_SEMANTIC_LINKS = {
    "D047": ["JurisLean.FullMath.Numeric.parts_nonneg",
             "JurisLean.Seams.UnifiedQuantLedger.discharged_iff_paid_covered"],
    "D048": ["JurisLean.FullMath.Numeric.parts_nonneg",
             "JurisLean.Seams.UnifiedQuantLedger.allocsOf_mem_nonneg",
             "JurisLean.Seams.UnifiedQuantLedger.allocsOf_sum_le"],
    "D049": ["JurisLean.FullMath.Numeric.parts_nonneg",
             "JurisLean.Seams.UnifiedQuantLedger.termInterest_indep",
             "JurisLean.Seams.UnifiedQuantLedger.seg_split"],
    "D050": ["JurisLean.FullMath.Numeric.parts_nonneg",
             "JurisLean.Seams.UnifiedQuantLedger.signing_not_mortgage_established",
             "JurisLean.Seams.UnifiedQuantLedger.distribute_priority"],
    "D051": ["JurisLean.FullMath.Numeric.parts_nonneg",
             "JurisLean.Seams.UnifiedQuantLedger.no_blanket_invalidation"],
    "D052": ["JurisLean.FullMath.Numeric.parts_nonneg",
             "JurisLean.Seams.UnifiedQuantLedger.afterPay_idents"],
    "D053": ["JurisLean.FullMath.Numeric.parts_nonneg",
             "JurisLean.Seams.UnifiedQuantLedger.sum_filter_partition"],
    "D054": ["JurisLean.FullMath.Numeric.parts_nonneg",
             "JurisLean.FullMath.Numeric.joint_shares_bound"],
    "D055": ["JurisLean.FullMath.Numeric.parts_nonneg",
             "JurisLean.Seams.UnifiedQuantLedger.unsourced_not_admitted",
             "JurisLean.Seams.UnifiedQuantLedger.income_not_impossible"],
    "D056": ["JurisLean.FullMath.Numeric.parts_nonneg",
             "JurisLean.Seams.UnifiedQuantLedger.self_quoted_not_supported",
             "JurisLean.Seams.UnifiedQuantLedger.sum_filter_partition"],
}


def _binding_row(dem, required):
    """Template for the controller's BINDINGS.json back-fill
    (DEMAND:D047–D056 rows).  Passes completion.validate_binding as-is."""
    return {
        "id": f"DEMAND:{dem}",
        "theorem": required["theorem"],
        "contract": required["contract"],
        "proof_mode": "KERNEL_CONTRACT_PROOF",
        "formal_scope": "Group-06 loan/guarantee demand instance in the "
                        "shared semantic framework: this item's own "
                        "contract semantics over the quantity-ledger "
                        "carrier (seven-field debt identity, "
                        "admission-order allocation, integer-day "
                        "interest components, typed security "
                        "establishment events) plus the registered "
                        "quantity component (both parts of the "
                        "covered/uncovered split stay nonnegative), "
                        "with its adverse case executed as a negative "
                        "test.",
        "independent_semantics": _SEMANTICS[dem],
        "algorithm": "tools/full_math/implementation/loan_ref.py "
                     f"{_ENTRY[dem]} computes the intermediate result "
                     f"from structured input (the ledger surface "
                     f"consumed from quantledger_ref, the mirror of "
                     f"JurisLean.Seams.UnifiedQuantLedger); "
                     f"loan_check.check_{dem} re-derives the contract "
                     f"independently with different code paths "
                     f"(index-walking allocations, direct division, "
                     f"branch tables, occurrence counting) — zero "
                     f"code sharing with the reference.",
        "observation_contract": "Inputs are the declared structures "
                                "(delivered loans with principal and "
                                "repayment streams of exact Fractions, "
                                "admission-ordered ledger rows with "
                                "ident/kind/basis/beneficiary/status/"
                                "amount fields, charge configurations "
                                "with rates, integer day counts and "
                                "denominators plus a policy cap, "
                                "security event lists and priority "
                                "claim lists with liquidation proceeds, "
                                "corporate-guarantee event sets, "
                                "signature attributions with signer, "
                                "capacity and principal ids, spousal-"
                                "debt issue flags, company-relation "
                                "evidence edges, sourced/unsourced "
                                "fact candidates, and fee ledgers with "
                                "three fee kinds and their bases); "
                                "outputs are exactly the contract "
                                "quantities (the booked/discharged "
                                "readouts with the equivalence and the "
                                "full-stream witness, the offset rows "
                                "with per-payment bounds, identity "
                                "preservation and duplicate-id gates, "
                                "the three charge components with "
                                "independence, split additivity and "
                                "the cap verdict, the typed "
                                "establishment verdicts with the "
                                "priority waterfall, the corporate "
                                "predicates with the same-event-set "
                                "contrast, the responsible-subject "
                                "attribution with beneficiary "
                                "preservation, the spousal attribution "
                                "with marriage-flip invariance, the "
                                "veil evaluation with the phone-only "
                                "rejection, the admission table with "
                                "the empty rule base, and the fee "
                                "consistency with the partition "
                                "conservation).",
        "external_assumptions": "Actual delivery and repayment records, "
                                "bank-statement authenticity and fund "
                                "use, stipulated-purpose evidence for "
                                "offsets, charge-term validity and the "
                                "actual default period, registration "
                                "and delivery facts for security "
                                "interests with document verification, "
                                "good-faith/knowledge judgments on "
                                "corporate guarantees, signing intent "
                                "and counterparty awareness, spousal "
                                "common-intent and household-use "
                                "proofs, open legal evaluation of "
                                "personality mixing and real corporate-"
                                "relation investigation, lender "
                                "capability and practice facts, and "
                                "reasonableness plus actual payment "
                                "proofs for fees remain external "
                                "validation obligations, not part of "
                                "this registration.",
        "proof_sources": [
            "proofs/lean/juris_lean/JurisLean/FullMath/Contracts.lean",
            "proofs/lean/juris_lean/JurisLean/FullMath/Acceptance.lean",
        ],
        "implementation_sources": [
            "tools/full_math/implementation/loan_ref.py",
            "tools/full_math/implementation/loan_check.py",
        ],
        "test_ids": [
            "tools/full_math/implementation_tests::"
            "test_loan_group06.py::"
            f"test_demand_positive[{dem}]",
            "tools/full_math/implementation_tests::"
            "test_loan_group06.py::"
            f"test_demand_counterexample[{dem}]",
            "tools/full_math/implementation_tests::"
            "test_loan_group06.py::"
            "test_downstream_pipeline_consumes_loan",
        ],
        "negative_test_ids": [
            "tools/full_math/implementation_tests::"
            "test_loan_group06.py::"
            f"test_checker_rejects_tampered[{dem}]",
        ],
        "semantic_links": _SEMANTIC_LINKS[dem],
    }


@pytest.mark.parametrize("dem", DEMANDS)
def test_b06_binding_receipt(dem):
    """Synthetic receipt: the binding row for DEMAND:D0XX passes
    completion.validate_binding against the real repository files."""
    required = _REQUIREMENTS[f"DEMAND:{dem}"]
    C.validate_binding(_binding_row(dem, required), required, repo=REPO)


@pytest.mark.parametrize("dem", DEMANDS)
def test_b06_binding_receipt_negative(dem):
    """A tampered receipt (swapped theorem) is rejected."""
    required = _REQUIREMENTS[f"DEMAND:{dem}"]
    row = dict(_binding_row(dem, required))
    row["theorem"] = "JurisLean.FullMath.Acceptance.nonexistent_demand"
    with pytest.raises(C.EvidenceError):
        C.validate_binding(row, required, repo=REPO)
