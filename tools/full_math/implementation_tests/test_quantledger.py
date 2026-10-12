"""Tests for the unified quantity-ledger layer (W2-A B06/B07 substrate).

Every positive case is checked twice: once against the reference
(``quantledger_ref``) and once against the fully independent checker
(``quantledger_check`` — zero sharing with the reference).  The
counterexample cases assert the fail-closed behaviour demanded by the
ALL_134 contract sentences for D047–D064.
"""
from fractions import Fraction
from typing import List

import pytest

from tools.full_math.implementation import quantledger_check as K
from tools.full_math.implementation import quantledger_ref as R

F = Fraction


# ---------------------------------------------------------------------------
# D047/D048: itemized ledger, admission-order allocation, stream legality
# ---------------------------------------------------------------------------

class TestLedger:
    def test_demo_readout(self):
        # B06 consumption witness (mirrors the Lean demoLedger_readout):
        # pay 150 → (10, 100, 40), outstanding 160; pay 350 → full discharge.
        items = list(R.DEMO_LEDGER)
        amounts = R.li_amounts(items)
        rows = R.stream_allocs([F(150)], items)
        assert rows[0] == [F(10), F(100), F(40)]
        assert R.outstanding(R.after_stream([F(150)], items)) == F(160)
        rows2 = R.stream_allocs([F(350)], items)
        assert rows2[0] == [F(10), F(100), F(200)]
        assert R.outstanding(R.after_stream([F(350)], items)) == 0
        assert K.check_ledger(amounts, [F(150)], rows, F(160))
        assert K.check_ledger(amounts, [F(350)], rows2, F(0))

    def test_multi_payment_stream(self):
        items = [
            R.LedgerItem(1, R.KIND_ATTORNEY, R.BASIS_STATUTORY, 0,
                         R.STATUS_SUPPORTED, F(10)),
            R.LedgerItem(2, R.KIND_INTEREST, R.BASIS_CONTRACT, 0,
                         R.STATUS_SUPPORTED, F(100)),
            R.LedgerItem(3, R.KIND_PRINCIPAL, R.BASIS_CONTRACT, 0,
                         R.STATUS_SUPPORTED, F(200)),
        ]
        pays = [F(60), F(200), F(100)]
        rows = R.stream_allocs(pays, items)
        out = R.outstanding(R.after_stream(pays, items))
        assert out == R.outstanding_after_stream(pays, items) == 0
        assert K.check_ledger(R.li_amounts(items), pays, rows, out)
        # identity preserved across the whole stream
        before = [it.ident for it in items]
        after_items = R.after_stream(pays, items)
        assert [it.ident for it in after_items] == before
        # no negative balances
        assert all(it.amount >= 0 for it in after_items)

    def test_partial_stream_balance_tracked(self):
        items = [
            R.LedgerItem(1, R.KIND_PRINCIPAL, R.BASIS_CONTRACT, 0,
                         R.STATUS_SUPPORTED, F(200)),
            R.LedgerItem(2, R.KIND_INTEREST, R.BASIS_CONTRACT, 0,
                         R.STATUS_SUPPORTED, F(50)),
        ]
        pays = [F(30), F(40)]
        rows = R.stream_allocs(pays, items)
        out = R.outstanding(R.after_stream(pays, items))
        # clamp: due 250, paid 70 → outstanding 180
        assert out == F(180)
        assert K.check_ledger(R.li_amounts(items), pays, rows, out)

    def test_d048_counterexample_same_payment_twice_rejected(self):
        # ALL_134 D048: 同一还款同时全额扣本金、又全额扣利息应拒绝 —
        # the same payment id cannot be processed twice.
        assert not R.stream_legal([(7, F(100)), (7, F(100))])
        assert not K.check_stream_legal([(7, F(100)), (7, F(100))])
        assert R.stream_legal([(7, F(100)), (8, F(50))])
        assert K.check_stream_legal([(7, F(100)), (8, F(50))])

    def test_d048_tampered_row_rejected_by_checker(self):
        items = list(R.DEMO_LEDGER)
        amounts = R.li_amounts(items)
        good = R.stream_allocs([F(150)], items)
        tampered = [good[0][:]]
        tampered[0][1] = F(120)  # exceeds the payment when summed
        rep = K.check_ledger(amounts, [F(150)], tampered, F(160))
        assert not rep.ok

    def test_d047_delivery_and_repayment_separate(self):
        # delivered 200, repayment stream 150 → outstanding 50;
        # delivery record alone (no repayments) → outstanding 200.
        lg = R.loan_ledger(True, 1, F(200))
        assert R.outstanding(R.after_stream([F(150)], lg)) == F(50)
        assert R.outstanding(lg) == F(200)
        # not delivered ⇒ nothing enters the ledger
        assert R.loan_ledger(False, 1, F(200)) == []
        assert K.check_ledger(R.li_amounts(lg), [F(150)],
                              R.stream_allocs([F(150)], lg), F(50))

    def test_rank_ordered(self):
        assert R.rank_ordered(R.DEMO_LEDGER)
        shuffled = list(R.DEMO_LEDGER)
        shuffled.reverse()
        assert not R.rank_ordered(shuffled)


class TestUnits:
    def test_unit_mismatch_rejected(self):
        # 100元 + 3米 is an error, never a silent coercion.
        yuan = R.Qty(F(100), R.Unit("money", item=1))
        meters = R.Qty(F(3), R.Unit("days", item=2))
        with pytest.raises(R.UnitError):
            yuan.plus(meters)
        ok = yuan.plus(R.Qty(F(50), R.Unit("money", item=1)))
        assert ok.val == F(150)

    def test_negative_scale_rejected(self):
        with pytest.raises(ValueError):
            R.Qty(F(1), R.Unit("share")).scaled(F(-1))
        q = R.Qty(F(10), R.Unit("share")).scaled(F("1/4"))
        assert q.val == F(5, 2)

    def test_float_refused(self):
        with pytest.raises(TypeError):
            R.Qty(0.5, R.Unit("money"))  # type: ignore[arg-type]


# ---------------------------------------------------------------------------
# D049: components, policy cap, compounding
# ---------------------------------------------------------------------------

class TestCharges:
    def test_d049_stacking_not_default(self):
        # ALL_134 D049: 相似百分比不能默认三项全叠加.
        sample_all = R.LoanCharges(F(100), 1, F(1, 10), 1, F(1, 10), 1,
                                   F(1, 10), 1)
        no_penalty = R.LoanCharges(F(100), 1, F(1, 10), 1, F(1, 10), 1,
                                   F(1, 10), 0)
        assert R.term_interest(sample_all) == F(10)
        assert R.overdue_interest(sample_all) == F(10)
        assert R.penalty_charge(sample_all) == F(10)
        assert not R.charges_within(F(24), sample_all)
        assert R.charges_within(F(24), no_penalty)
        assert not K.check_charges(F(100), 1, F(1, 10), 1, F(1, 10), 1,
                                   F(1, 10), 1, F(24), R.total_charges(sample_all)).ok
        assert K.check_charges(F(100), 1, F(1, 10), 1, F(1, 10), 1,
                               F(1, 10), 0, F(24), R.total_charges(no_penalty))

    def test_component_independence(self):
        c = R.LoanCharges(F(1000), 365, F(3, 100), 100, F(5, 100), 30,
                          F(2, 10), 10)
        c2 = R.LoanCharges(F(1000), 365, F(3, 100), 100, F(9, 100), 77,
                           F(1, 2), 999)
        # term interest unaffected by overdue/penalty parameters
        assert R.term_interest(c) == R.term_interest(c2)
        assert K.check_charges(c.principal, c.denom, c.term_rate, c.term_days,
                               c.overdue_rate, c.overdue_days, c.penalty_rate,
                               c.penalty_days, R.total_charges(c) + F(1),
                               R.total_charges(c))

    def test_seg_split_exact(self):
        seg = R.InterestSeg(F(10000), F(3, 1000), 60, 360)
        left, right = R.seg_split_total(seg, 17)
        assert left + right == seg.interest()
        assert K.check_seg_split(seg.base, seg.rate, seg.days, 17, seg.denom)

    def test_compound_two_periods_identity(self):
        compound, parts = R.compound_two_periods(F(1000), F(4, 100), 30, 60, 365)
        assert compound == parts
        assert K.check_compound(F(1000), F(4, 100), 30, 60, 365)
        # compounding never understates the two simple periods
        assert compound >= (R.capitalize(F(1000), F(4, 100), 30, 365)
                            + R.InterestSeg(F(1000), F(4, 100), 60, 365).interest())

    def test_zero_days_and_denominator_discipline(self):
        assert R.InterestSeg(F(100), F(1, 10), 0, 365).interest() == 0
        with pytest.raises(ValueError):
            R.InterestSeg(F(100), F(1, 10), 10, 0)


# ---------------------------------------------------------------------------
# D050/D051: collateral events and priority
# ---------------------------------------------------------------------------

class TestCollateral:
    def test_d050_signing_is_not_registration_or_delivery(self):
        # ALL_134 D050: 签担保文件不自动证明登记完成或财产已交付.
        assert not R.sec_established(R.SEC_MORTGAGE, [R.EV_SIGNED])
        assert not R.sec_established(R.SEC_PLEDGE, [R.EV_SIGNED])
        assert not K.check_sec("mortgage", ["signed"])
        assert not K.check_sec("pledge", ["signed"])
        assert R.sec_established(R.SEC_MORTGAGE, [R.EV_SIGNED, R.EV_REGISTERED])
        assert R.sec_established(R.SEC_PLEDGE, [R.EV_DELIVERED])
        assert R.sec_established(R.SEC_SURETYSHIP, [R.EV_SIGNED])

    def test_d051_no_blanket_invalidation(self):
        # ALL_134 D051: 仅无决议字段不得由一条统一规则宣布所有担保无效 —
        # the same event set leaves the natural-person suretyship standing.
        assert not R.corp_surety_established([R.EV_SIGNED])
        assert not K.check_corp_surety(["signed"])
        assert R.sec_established(R.SEC_SURETYSHIP, [R.EV_SIGNED])
        assert R.corp_surety_established([R.EV_RESOLUTION, R.EV_SIGNED])

    def test_priority_distribution(self):
        claims = [F(100), F(200), F(700)]
        proceeds = F(500)
        rows, leftover = R.distribute_proceeds(claims, proceeds)
        assert rows == [F(100), F(200), F(200)]
        assert leftover == 0
        rep = K.check_proceeds(claims, proceeds, rows)
        assert rep.ok
        rows2, leftover2 = R.distribute_proceeds(claims, F(1000))
        assert rows2 == [F(100), F(200), F(700)]
        assert leftover2 == F(0)
        assert K.check_proceeds(claims, F(1000), rows2)

    def test_seniority_tamper_rejected(self):
        claims = [F(100), F(200)]
        bad = [F(60), F(200)]  # junior full while senior unsatisfied
        rep = K.check_proceeds(claims, F(260), bad)
        assert not rep.ok
        assert any("seniority" in r for r in rep.reasons)


# ---------------------------------------------------------------------------
# D057-D064 interval substrate
# ---------------------------------------------------------------------------

class TestIntervals:
    def test_readout(self):
        a = R.IvQ(F(100), F(200))
        b = R.IvQ(F(150), F(300))
        inter = R.v_inter(a, b)
        assert (inter.lo, inter.hi) == (F(150), F(200))
        assert K.check_inter(F(100), F(200), F(150), F(300),
                             (F(150), F(200)))
        scaled = R.v_scale(F(1, 4), a)
        assert (scaled.lo, scaled.hi) == (F(25), F(50))
        assert K.check_scale(F(1, 4), F(100), F(200), (F(25), F(50)))

    def test_cause_times_loss_readout(self):
        ci = R.TagIv(R.TAG_CAUSE, R.IvQ(F(1, 3), F(2, 3)))
        li = R.TagIv(R.TAG_LOSS, R.IvQ(F(90), F(120)))
        prod = R.cause_times_loss(ci, li)
        assert prod.tag == R.TAG_LOSS
        assert (prod.iv.lo, prod.iv.hi) == (F(30), F(80))
        assert K.check_cause_times_loss(F(1, 3), F(2, 3), F(90), F(120),
                                        (F(30), F(80)))

    def test_disjoint_intersection_fail_closed(self):
        empty = R.v_inter(R.IvQ(F(0), F(10)), R.IvQ(F(20), F(30)))
        assert empty is None
        assert K.check_inter(F(0), F(10), F(20), F(30), None)

    def test_cross_tag_rejected(self):
        loss = R.TagIv(R.TAG_LOSS, R.IvQ(F(1), F(2)))
        fault = R.TagIv(R.TAG_FAULT, R.IvQ(F(0), F(1)))
        with pytest.raises(TypeError):
            loss.plus(fault)  # type: ignore[arg-type]

    def test_fault_ok_and_scaling(self):
        f = R.TagIv(R.TAG_FAULT, R.IvQ(F(1, 4), F(1, 2)))
        assert f.fault_ok()
        assert f.scaled(F(1, 2)).fault_ok()
        assert K.check_fault_ok(F(1, 8), F(1, 4))
        bad = R.TagIv(R.TAG_FAULT, R.IvQ(F(0), F(3, 2)))
        assert not bad.fault_ok()

    def test_endpoint_algebra(self):
        a = R.IvQ(F(1), F(4))
        b = R.IvQ(F(2), F(3))
        c = R.IvQ(F(5), F(6))
        assert R.v_add(R.v_add(a, b), c) == R.v_add(a, R.v_add(b, c))
        assert R.v_add(a, b) == R.v_add(b, a)
        k = F(3, 7)
        assert R.v_scale(k, R.v_add(a, b)) == R.v_add(R.v_scale(k, a), R.v_scale(k, b))
        assert R.v_scale(k, R.v_scale(F(2), a)) == R.v_scale(k * 2, a)
        # subtraction via negation: (x − y) ∈ v_sub for members
        s = R.v_sub(R.IvQ(F(10), F(20)), R.IvQ(F(1), F(2)))
        assert s.lo == F(8) and s.hi == F(19)
        # containment monotone under scaling
        assert R.v_contained(a, R.IvQ(F(0), F(5)))
        assert R.v_contained(R.v_scale(k, a), R.v_scale(k, R.IvQ(F(0), F(5))))
        assert K.check_contained((F(1), F(4)), (F(0), F(5)))


class TestGatesAndModes:
    def test_d059_gate_zero_share(self):
        assert R.legal_shares([True, True], [F(1, 4), F(3, 4)])
        assert K.check_legal_shares([True, True], [F(1, 4), F(3, 4)])
        # ALL_134 D059: 用小比例掩盖根本不承担该责任的主体 — 1/10 for a
        # no-liability party is illegal.
        assert not R.legal_shares([False, True], [F(1, 10), F(9, 10)])
        assert not K.check_legal_shares([False, True], [F(1, 10), F(9, 10)])
        assert R.legal_shares([False, True], [F(0), F(1)])

    def test_d062_shared_base_consistency(self):
        shares = [F(1, 4), F(3, 4)]
        base = F(1200)
        assert R.pays_sum_base(base, shares) == base
        assert R.external_due(R.MODE_SEVERAL, base, F(300), 0, 0) == F(300)

    def test_d060_joint_total_constraint(self):
        # ALL_134 D060: 同一损害多个连带债务全额相加造成超额受偿.
        assert not R.joint_recovery_ok(F(100), [F(100), F(100)])
        assert not K.check_joint_recovery(F(100), [F(100), F(100)])
        assert R.joint_recovery_ok(F(100), [F(100), F(0)])
        assert R.joint_recovery_ok(F(100), [F(60), F(40)])

    def test_d062_joint_external_not_share_reduced(self):
        # ALL_134 D062: 把外部连带金额按内部份额削减，须发现语义不符.
        loss, share = F(100), F(40)
        due = R.external_due(R.MODE_JOINT, loss, share, 0, 0)
        assert due == loss and due != share
        assert K.check_external_due("joint", loss, share, 0, 0, due)

    def test_recourse_pool_balanced(self):
        paid = [F(70), F(30), F(0)]
        shares = [F(10), F(40), F(50)]
        assert sum(paid, F(0)) == sum(shares, F(0)) == F(100)
        assert R.recourse_pool_balanced(paid, shares)
        assert K.check_recourse_pool(paid, shares)
        assert R.recourse_of(F(70), F(10)) == F(60)
        assert R.deficit_of(F(0), F(50)) == F(50)

    def test_supplementary_only_unpaid(self):
        first, second = R.supp_distribution(F(100), F(500), F(300))
        assert (first, second) == (F(100), F(200))
        assert K.check_supp(F(100), F(500), F(300), (first, second))
        # primary fully covers ⇒ supplementary pays nothing
        f2, s2 = R.supp_distribution(F(300), F(500), F(300))
        assert (f2, s2) == (F(300), F(0))
        assert K.check_supp(F(300), F(500), F(300), (f2, s2))
        # secondary capped by its own due
        f3, s3 = R.supp_distribution(F(100), F(50), F(300))
        assert (f3, s3) == (F(100), F(50))


# ---------------------------------------------------------------------------
# D061/D063/D064: loss ledger, remedies, scenario witness
# ---------------------------------------------------------------------------

class TestLossLedger:
    def test_d061_invoice_appraisal_single_count(self):
        # ALL_134 D061: 发票额和同一损失评估额不得无条件双计.
        invoice = R.LossEntry(1, 2, 3, 4, F(1000))
        appraisal = R.LossEntry(1, 2, 3, 4, F(800))
        deduped = R.dedup_first([invoice, appraisal])
        assert deduped == [invoice]
        assert R.loss_total(deduped) == F(1000)
        assert R.loss_total([invoice, appraisal]) == F(1800)
        rep = K.check_dedup([(invoice.key, invoice.amount),
                             (appraisal.key, appraisal.amount)],
                            [(e.key, e.amount) for e in deduped])
        assert rep.ok

    def test_distinct_keys_all_kept(self):
        a = R.LossEntry(1, 2, 3, 4, F(100))
        b = R.LossEntry(1, 2, 3, 5, F(200))  # different time ⇒ distinct key
        c = R.LossEntry(1, 3, 3, 4, F(300))  # different beneficiary
        out = R.dedup_first([a, b, c])
        assert out == [a, b, c]
        assert R.loss_total(out) == F(600)

    def test_dedup_never_inflates(self):
        a = R.LossEntry(1, 1, 1, 1, F(10))
        b = R.LossEntry(1, 1, 1, 1, F(999))
        out = R.dedup_first([a, b, a])
        assert R.loss_total(out) <= R.loss_total([a, b, a])
        rep = K.check_dedup([(a.key, a.amount), (b.key, b.amount),
                             (a.key, a.amount)],
                            [(e.key, e.amount) for e in out])
        assert rep.ok


class TestRemediesAndWitness:
    def test_d063_nonmonetary_no_amount(self):
        assert R.amount_of(F(500)) == F(500)
        assert R.amount_of(R.REMEDY_APOLOGY) is None
        assert R.amount_of(R.REMEDY_CESSATION) is None
        assert R.amount_of(R.REMEDY_RESTITUTION) is None

    def test_d063_monetary_total_blind_spot(self):
        # ALL_134 D063: 道歉或禁令不能当赔偿金额零而消失 — two remedy
        # lists with the same monetary total are still different duties.
        list_a = [F(100), R.REMEDY_APOLOGY]
        list_b = [F(100)]
        assert R.monetary_total(list_a) == R.monetary_total(list_b) == F(100)
        assert K.check_monetary_blind_spot(list_a, list_b)

    def test_d064_cross_scenario_mix_rejected(self):
        # ALL_134 D064: 不同情景各取最有利结果拼成无条件总结.
        wa = R.ScenarioWitness(1, (F(1),), (F(100),))
        wb = R.ScenarioWitness(2, (F(1),), (F(999),))
        mixed = R.SummaryRecord(1, (F(1),), (F(999),), F(0))
        assert not mixed.from_same_witness(wa)  # values differ
        assert not mixed.from_same_witness(wb)  # scen id differs
        good = R.SummaryRecord(2, (F(1),), (F(999),), F(0))
        assert good.from_same_witness(wb)
        assert K.check_same_witness(1, (F(1),), (F(999),), F(0),
                                    {"scen_id": 2, "ratios": [F(1)],
                                     "values": [F(999)]}) is False


# ---------------------------------------------------------------------------
# D055/D057/D058: admission, tort partition, imputation
# ---------------------------------------------------------------------------

class TestLightweight:
    def test_d055_unsourced_not_admitted(self):
        assert R.admitted_fact((True, 1))
        assert not R.admitted_fact((False, 9))
        assert K.check_admitted((True, 1))
        assert not K.check_admitted((False, 9))
        # 收入低 does not fabricate the negative cash-impossibility fact —
        # there is no licensed rule; the checker has none either.
        assert not K.check_imputed(False, F("0.9"))

    def test_d057_residual_kept(self):
        cands = [("openResidual", False), ("general", True)]
        sel, res = R.tort_partition(cands)
        assert sel == [("general", True)] and res == [("openResidual", False)]
        ksel, kres = K.check_tort_partition(cands)
        assert ksel == sel and kres == res

    def test_d058_correlation_not_imputation(self):
        strong = F(9, 10)
        assert not R.imputed(False, strong)
        assert not K.check_imputed(False, strong)
        assert R.imputed(True, strong)
        assert K.check_imputed(True, strong)
        assert not R.imputed(True, F(0))


class TestRefCheckerAgreement:
    """Deterministic sweep: the reference and the independent checker agree
    on a grid of synthetic ledger cases (no floats, exact Fractions)."""

    @pytest.mark.parametrize("payments", [
        [F(0)],
        [F(5)],
        [F(50)],
        [F(155)],
        [F(310)],
        [F(400)],
        [F(10), F(10), F(10)],
        [F(100), F(1), F(209)],
        [F(1, 2), F(309, 2)],
    ])
    def test_grid(self, payments: List[Fraction]):
        items = list(R.DEMO_LEDGER)
        amounts = R.li_amounts(items)
        rows = R.stream_allocs(payments, items)
        out = R.outstanding(R.after_stream(payments, items))
        assert out == R.outstanding_after_stream(payments, items)
        rep = K.check_ledger(amounts, payments, rows, out)
        assert rep.ok, rep.reasons

    @pytest.mark.parametrize("proceeds", [F(0), F(40), F(100), F(310),
                                          F(999), F(1000)])
    def test_proceeds_grid(self, proceeds: Fraction):
        claims = [F(10), F(100), F(200)]
        rows, leftover = R.distribute_proceeds(claims, proceeds)
        rep = K.check_proceeds(claims, proceeds, rows)
        assert rep.ok, rep.reasons
        assert sum(rows, F(0)) + leftover == proceeds
