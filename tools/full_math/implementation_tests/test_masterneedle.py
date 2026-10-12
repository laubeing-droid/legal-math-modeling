"""Master needle (W0, needle 60, I:814) tests.

Positive cases: the coherent interim's C1-C7 clauses all hold, the event
chain is sound for the static closure with two-way agreement on the
consumed atom set, the three exchange groups hold (payment split/reorder,
dedup x scaling plus interval distributivity, burden/payment channels), all
four error-propagation faces hold with the end-to-end exposure bound, the
divFree AST carries the balance exactly, the Beta(2,3) posterior is a
genuine strictly increasing CDF comparable across rationals, and the
all-comply pure profile is a Nash equilibrium of the interim-derived menu.

Negative cases: an incoherent interim (flows not matching the allocation
readout), a wrong balance reading, a non-divFree AST, an invalid Beta
shape, a false equilibrium claim (all-defect), a violated perturbation
bound, a non-commuting "dedup" that reorders instead of preserving
first-seen, and a key-changing "scaling" are all rejected by the
independent checker.

The independent checker (``masterneedle_check``) re-derives every
observable with different algorithms (per-atom derivation-DAG search,
first-fit decrement scans, Horner-style single-pass reading, expanded
polynomial CDF, brute-force equilibrium enumeration); it never imports the
reference.

Receipt note (W0 form): the 60-needle table has no slot in
tools/full_math/spec/REQUIREMENTS.json, so there is no validate_binding row
for W17; the batch receipt is recorded in
.local/agent_W17_master_needle_report.md per the wave convention, and this
suite pins the Lean sources by name.
"""
from fractions import Fraction
from pathlib import Path

import pytest

from tools.full_math.implementation import masterneedle_check as K
from tools.full_math.implementation import masterneedle_ref as R

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[2]

LEAN_MODULE = (REPO / 'proofs/lean/juris_lean/JurisLean/Seams/'
               'UnifiedMasterNeedle.lean')

LEAN_THEOREMS = (
    'unified_legal_derivation_on_declared_fragment',
    'masterInterim_coherent',
    'master_static_event_correspondence',
    'ledger_payment_split_exchange',
    'master_loss_aggregation_share_exchange',
    'master_channel_exchange_readings',
    'prefIntegral_perturb',
    'legalReading_perturb',
    'abs_sub_max_zero',
    'outstanding_payment_perturb',
    'master_qty_ast_carries_balance',
    'beta_enclosure_expected_reading',
    'master_beta_face',
    'master_exposure_perturb_chain',
    'master_error_propagation_chain',
    'master_equil_face',
    'update_pureMR',
    'master_base_eu',
    'master_pay_dev',
    'master_dev_eu',
    'dedup_scale_commute',
    'dedupAux_scale_commute',
    'lossTotal_scale',
    'masterLoss_dedup_total',
    'masterBalance_eq',
    'masterReading_eq',
    'masterLawful_0',
    'masterLawful_1',
    'masterLawful_eq',
    'required_concl_mem',
    'conclInFinalNet',
    'conclInClosure',
    'qtyDenote_masterQtyAst',
    'cashTotal_append',
    'cashTotal_payEntriesOf',
    'masterFinalEstablished',
    'masterPos',
    'masterCivilHigh',
    'masterAllElements',
    'masterReasonLicensed',
    'masterCardDerives',
)

LEAN_DEFS = (
    'CoherentInterim', 'Coherent', 'RequiredAtoms', 'ledgerBacking',
    'costKindOf', 'masterFlows', 'masterInterim', 'masterFrame',
    'masterBalance', 'masterFlowCarrier', 'masterReading', 'payEntriesOf',
    'scaleLoss', 'masterLoss', 'payInterim', 'burdenInterim', 'amtPerturb',
    'masterQtyAst', 'exposureOf', 'masterLawful', 'masterMenu', 'masterQ',
    'QtyFaceProp', 'BetaFaceProp', 'ErrorChainProp', 'EquilFaceProp',
    'EventFaceProp',
)


# ---------------------------------------------------------------------------
# Pin the Lean sources by name
# ---------------------------------------------------------------------------

def test_lean_module_pins_the_rebuilt_needle():
    text = LEAN_MODULE.read_text(encoding='utf-8')
    for name in LEAN_THEOREMS:
        assert f'theorem {name}' in text, name
    for name in LEAN_DEFS:
        assert f'def {name}' in text or f'structure {name}' in text, name
    assert 'UnifiedNetTrajectory' in text and 'UnifiedPayoffChain' in text
    assert 'UnifiedEvalLayer' in text and 'UnifiedQuantLedger' in text
    assert 'UnifiedEquilExist' in text and 'UnifiedBetaDomain' in text
    assert 'UnifiedNeedlesS3b' in text


# ---------------------------------------------------------------------------
# F1: coherent interim
# ---------------------------------------------------------------------------

def test_master_interim_is_coherent():
    ci = R.build_master_interim()
    clauses = R.coherent_clauses(ci)
    assert all(clauses.values()), clauses
    assert R.coherent(ci)


def test_coherent_C4_flows_match_allocation_readout():
    ci = R.build_master_interim()
    rows = [x for rows in R.stream_allocs(ci.pay_plan, ci.ledger) for x in rows]
    assert [e.amount for e in ci.flows] == rows == [Fraction(10), Fraction(100),
                                                    Fraction(40)]
    assert R.cash_total(ci.flows) == Fraction(150)


def test_checker_rederives_coherence():
    ci = R.build_master_interim()
    balance = R.outstanding(R.after_stream(ci.pay_plan, ci.ledger))
    ok, reasons = K.check_coherence(
        R.RULES, R.FULL_DOCKET_MATERIALS, ci.traj,
        [it.ident for it in ci.ledger], R.LEDGER_BACKING,
        [e.amount for e in ci.flows], ci.pay_plan, balance,
        ci.loss_iv, ci.final_net, ci.frame_judgment_established)
    assert ok, reasons


def test_checker_rejects_incoherent_interim():
    ci = R.build_master_interim()
    balance = Fraction(999)  # balance outside the loss interval
    ok, reasons = K.check_coherence(
        R.RULES, R.FULL_DOCKET_MATERIALS, ci.traj,
        [it.ident for it in ci.ledger], R.LEDGER_BACKING,
        [e.amount for e in ci.flows], ci.pay_plan, balance,
        ci.loss_iv, ci.final_net, ci.frame_judgment_established)
    assert not ok
    ci2 = R.build_master_interim()
    bad_backing = dict(R.LEDGER_BACKING)
    bad_backing[1] = "nonexistentAtom"
    ok2, _ = K.check_coherence(
        R.RULES, R.FULL_DOCKET_MATERIALS, ci2.traj,
        [it.ident for it in ci2.ledger], bad_backing,
        [e.amount for e in ci2.flows], ci2.pay_plan, Fraction(160),
        ci2.loss_iv, ci2.final_net, True)
    assert not ok2


# ---------------------------------------------------------------------------
# F2: static/event chain correspondence
# ---------------------------------------------------------------------------

def test_event_chain_soundness_via_dag_search():
    ci = R.build_master_interim()
    ok, reasons = K.check_trajectory_soundness(
        R.RULES, R.FULL_DOCKET_MATERIALS, ci.traj)
    assert ok, reasons


def test_consumed_atoms_two_way_agreement():
    ci = R.build_master_interim()
    corr = R.static_event_correspondence(ci)
    assert corr['a_soundness'] and corr['b_consumed_two_way'] \
        and corr['c_rules_pinned'], corr


def test_trajectory_wellformed_productive_increasing():
    init = R.initial_state(R.FULL_DOCKET_MATERIALS)
    assert R.trajectory_ok(init, R.WITNESS_TRAJECTORY)
    assert R.trajectory_productive(init, R.WITNESS_TRAJECTORY)
    assert R.times_increasing(R.WITNESS_TRAJECTORY)
    assert len(R.WITNESS_TRAJECTORY) == 17


def test_checker_rejects_unsound_trajectory():
    # a fabricated rule consuming an atom nothing produces: its conclusion is
    # not derivable in the static chain, so the event chain is unsound
    fake_rules = list(R.RULES) + [
        {"id": "R99", "premises": ("atomDoesNotExist",),
         "conclusion": "conclusionDoesNotExist", "src": "L01"}]
    bogus = list(R.WITNESS_TRAJECTORY) + [(17, "R99")]
    ok, reasons = K.check_trajectory_soundness(
        fake_rules, R.FULL_DOCKET_MATERIALS, bogus)
    assert not ok


# ---------------------------------------------------------------------------
# F3: exchange groups
# ---------------------------------------------------------------------------

@pytest.mark.parametrize("p1,p2", [
    (Fraction(60), Fraction(90)),
    (Fraction(150), Fraction(0)),
    (Fraction(0), Fraction(350)),
    (Fraction(310), Fraction(100)),
    (Fraction(7, 3), Fraction(2, 7)),
])
def test_payment_split_exchange_holds(p1, p2):
    ci = R.build_master_interim()
    obs = R.payment_split_exchange(ci, p1, p2)
    amounts = [it.amount for it in ci.ledger]
    ok, reasons = K.check_payment_split_exchange(
        amounts, p1, p2,
        {"E1": obs["E1_reorder"], "E2": obs["E2_merge"],
         "E3_two": obs["E3_two_stage"], "E3_one": obs["E3_one_stage"],
         "E4_cash_two": obs["E4_cash_two"], "E4_cash_one": obs["E4_cash_one"]})
    assert ok, (reasons, p1, p2)
    assert obs["E1_reorder"] == obs["E1_reorder_swapped"]
    assert obs["E2_merge"] == obs["E2_merged"] == obs["E1_reorder"]


def test_dedup_scale_commutes():
    for c in (Fraction(1, 4), Fraction(0), Fraction(3), Fraction(2, 5)):
        lhs, rhs = R.dedup_scale_exchange(c, R.MASTER_LOSS)
        assert lhs == rhs
        entries = [{"key": e.key, "amount": e.amount} for e in R.MASTER_LOSS]
        ok, reasons = K.check_dedup_scale_commute(
            entries, c, [{"key": e.key, "amount": e.amount} for e in lhs],
            [{"key": e.key, "amount": e.amount} for e in rhs])
        assert ok, reasons
    lhs, _ = R.dedup_scale_exchange(Fraction(1, 4), R.MASTER_LOSS)
    assert R.loss_total(lhs) == Fraction(250)
    assert R.loss_total(R.dedup_first(R.MASTER_LOSS)) == Fraction(1000)


def test_interval_share_distributivity():
    c = Fraction(1, 4)
    i = (Fraction(100), Fraction(200))
    j = (Fraction(150), Fraction(300))
    lhs, rhs = R.interval_share_distributivity(c, i, j)
    assert lhs == rhs == (Fraction(25), Fraction(75))
    ok, reasons = K.check_interval_distributivity(c, i, j, lhs, rhs)
    assert ok, reasons


def test_channel_exchange_commutes():
    ci = R.build_master_interim()
    out = R.channel_exchange(ci, Fraction(50), True)
    assert out["commutes"] and out["judgment_stays"]
    assert out["burden_keeps_ledger"] and out["burden_keeps_flows"]
    assert out["pay_keeps_frame"]


def test_checker_rejects_noncommuting_fake_dedup():
    # a "dedup" that keeps the LAST occurrence instead of the first
    entries = [{"key": e.key, "amount": e.amount} for e in R.MASTER_LOSS]
    lhs = [{"key": (1, 2, 3, 4), "amount": Fraction(200)}]  # last-seen value
    ok, reasons = K.check_dedup_scale_commute(entries, Fraction(1, 4), lhs, lhs)
    assert not ok


def test_checker_rejects_key_changing_scaling():
    entries = [{"key": (1, 2, 3, 4), "amount": Fraction(1000)},
               {"key": (9, 9, 9, 9), "amount": Fraction(800)}]
    lhs = [{"key": (1, 2, 3, 4), "amount": Fraction(250)}]
    ok, _ = K.check_dedup_scale_commute(entries, Fraction(1, 4), lhs, lhs)
    assert not ok


# ---------------------------------------------------------------------------
# F4: error propagation
# ---------------------------------------------------------------------------

def test_payoff_perturb_bound():
    for d in (lambda e: Fraction(0), lambda e: Fraction(1, 10),
              lambda e: -Fraction(1, 5) if e.period == 1 else Fraction(0)):
        moved, bound = R.payoff_perturb_bound("claimant", R.MASTER_FLOWS, d)
        assert abs(moved) <= bound
        deltas = [d(e) for e in R.MASTER_FLOWS]
        ok, reasons = K.check_payoff_bound(
            R.CONSEQUENCE_VALUATION,
            [{"kind": e.kind, "amount": e.amount} for e in R.MASTER_FLOWS],
            deltas, moved, bound)
        assert ok, reasons


def test_ledger_perturb_bound_and_relu_lipschitz():
    moved, bound = R.ledger_perturb_bound(
        R.DEMO_LEDGER, [Fraction(150)], [Fraction(140)])
    assert abs(moved) == Fraction(10) == abs(bound)
    ok, reasons = K.check_ledger_lipschitz([
        (Fraction(310) - Fraction(150), Fraction(310) - Fraction(140)),
        (Fraction(-5), Fraction(5)), (Fraction(0), Fraction(-3)),
    ])
    assert ok, reasons
    # balance readings re-derived by the checker's decrement scan
    amounts = [it.amount for it in R.DEMO_LEDGER]
    ok2, reasons2 = K.check_balance_after(
        amounts, [Fraction(150)], R.master_balance())
    assert ok2, reasons2


def test_beta_enclosure_bound():
    deduped = R.loss_total(R.dedup_first(R.MASTER_LOSS))
    moved, bound = R.beta_enclosure_bound(
        Fraction(9, 10), Fraction(11, 10), Fraction(10, 10),
        Fraction(11, 10), Fraction(1, 5), Fraction(1), deduped)
    assert abs(moved) <= bound
    ok, reasons = K.check_beta_enclosure(
        Fraction(9, 10), Fraction(11, 10), Fraction(10, 10),
        Fraction(11, 10), Fraction(1, 5), Fraction(1), deduped)
    assert ok, reasons


def test_exposure_perturb_chain():
    ci = R.build_master_interim()
    out = R.exposure_perturb_chain(
        ci, lambda e: Fraction(1, 10), [Fraction(150)], [Fraction(140)],
        Fraction(10), Fraction(9, 10), Fraction(11, 10), Fraction(10, 10),
        Fraction(11, 10), Fraction(1, 5), Fraction(1))
    assert abs(out["exposure_moved"]) <= out["total_bound"]
    assert out["payoff_moved"] <= out["payoff_bound"]
    assert out["ledger_moved"] <= out["ledger_bound"]
    assert out["beta_moved"] <= out["beta_bound"]


def test_checker_rejects_violated_bound():
    ok, reasons = K.check_abs_le(Fraction(5), Fraction(1), "fake")
    assert not ok
    # enclosure with inverted endpoints must fail the hypothesis check
    ok2, _ = K.check_beta_enclosure(
        Fraction(11, 10), Fraction(9, 10), Fraction(10, 10),
        Fraction(11, 10), Fraction(1, 5), Fraction(1), Fraction(1000))
    assert not ok2


# ---------------------------------------------------------------------------
# F4 quantity face / F5 beta face
# ---------------------------------------------------------------------------

def test_qty_ast_carries_balance():
    face = R.qty_ast_face()
    assert face["carries"] and face["div_free"] and face["int_valued"]
    assert face["balance"] == Fraction(160) == face["denote"]
    ok, reasons = K.check_qty_ast(face["denote"], Fraction(160),
                                  bool(face["div_free"]))
    assert ok, reasons


def test_checker_rejects_wrong_balance_and_nondivfree():
    ok, _ = K.check_qty_ast(Fraction(155), Fraction(160), True)
    assert not ok
    ok2, _ = K.check_qty_ast(Fraction(160), Fraction(160), False)
    assert not ok2


def test_beta_face_strictly_increasing_and_comparable():
    face = R.beta_face()
    assert face["shape_ok"] and face["endpoints"]
    assert face["strictly_increasing_rational_grid"]
    assert face["value_at_half"] == Fraction(11, 16)
    # checker: expanded-polynomial re-derivation on a dense rational grid
    grid = [Fraction(k, 40) for k in range(41)]
    vals = [R.rat_bern_cdf(2, 3, q) for q in grid]
    ok, reasons = K.check_beta_values(grid, vals)
    assert ok, reasons


def test_invalid_beta_shape_rejected():
    # C7 shape domain: 1 <= alpha and 1 <= beta.  A shape outside the domain
    # (0, 0) makes the coherence predicate fail (the Lean side requires the
    # same bounds in Coherent clause C7).
    ci = R.build_master_interim()
    bad = R.CoherentInterim(
        docket=ci.docket, traj=ci.traj, final_net=ci.final_net,
        ledger=ci.ledger, pay_plan=ci.pay_plan, flows=ci.flows,
        loss_iv=ci.loss_iv, prob_shape=(0, 0),
        frame_judgment_established=ci.frame_judgment_established)
    assert not R.coherent_clauses(bad)["C7_beta_shape"]


# ---------------------------------------------------------------------------
# F5: equilibrium face
# ---------------------------------------------------------------------------

def test_menu_values_are_interim_readings():
    face = R.equil_face()
    assert face["lawful_values"] == (Fraction(160), Fraction(250))
    assert face["balance"] == Fraction(160)
    assert face["reading"] == Fraction(250)


def test_all_comply_is_nash_all_defect_is_not():
    assert R.menu_is_pure_nash((True, True))
    assert not R.menu_is_pure_nash((False, False))
    ok, reasons = K.check_equilibrium_claim(
        R.menu_pay, (0, 1), (True, True), True)
    assert ok, reasons
    ok2, reasons2 = K.check_equilibrium_claim(
        R.menu_pay, (0, 1), (False, False), False)
    assert ok2, reasons2
    # brute force: the ONLY pure equilibrium of this menu is all-comply
    eqs = K.brute_force_pure_nash(R.menu_pay, (0, 1))
    assert eqs == [(True, True)]


def test_checker_rejects_false_equilibrium_claim():
    ok, _ = K.check_equilibrium_claim(
        R.menu_pay, (0, 1), (True, False), True)
    assert not ok


# ---------------------------------------------------------------------------
# Total readout
# ---------------------------------------------------------------------------

def test_master_needle_readout_all_green():
    out = R.master_needle_readout()
    assert out['F1_coherent']
    assert all(out['F1_clauses'].values())
    assert all(out['F2_correspondence'].values())
    assert all(out['F3_payment_split'].values())
    assert out['F3_dedup_scale_commutes']
    assert out['F3_interval_distributivity']
    assert out['F3_channel_exchange']['commutes']
    assert out['F4_error_chain']['qty_ast']['carries']
    assert out['F5_beta_face']['strictly_increasing_rational_grid']
    assert out['F5_equil_face']['all_comply_is_nash']
    assert all(out['F5_static_event'].values())
