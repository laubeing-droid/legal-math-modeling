"""Payoff-chain and lawView use-point tests for needles 28 and 48 (W1-13).

Needle 28 legal_payoff_preserved (I:782): the four-layer encoding chain —
cash -> costs -> preference integral -> legal payoff reading — with total
preservation (positive), image preservation (positive), netting boundary
(negative), covariance (positive), single-kind reflection (positive) and
its zero-weight failure (negative), the status-vector grid agreement (all
8 cells), bookkeeping-bit blindness, the end-to-end chain propagation, and
the two chain-breaking counterexamples (status projection drops cash;
dropped-kind cost encoding).

Needle 48 legal_time_nonanticipation (I:802): the real 29-rule body network
evaluated through the truncated view — per-rule use points for R01/R23/R19
(every premise read equals the view read), per-rule future blindness,
witness firing (positive), out-of-window rejection on future-only ledgers
(negative), the hview-as-theorem fact, and the as-of dynamics witness (the
contract material arriving on day 150 changes nothing at cut 100 and fires
at cut 160).

Receipt note (W1-13 batch form): the 60-needle table has no slot in
tools/full_math/spec/REQUIREMENTS.json (217 FullMath ids only), so there is
no validate_binding row for W1:28/W1:48; the receipt for this batch is
recorded in .local/agent_W13_payoff_chain_report.md per the W1-wave
convention, and this suite pins the Lean sources by name.
"""
from fractions import Fraction
from pathlib import Path

import pytest

from tools.full_math.implementation import payoffchain_ref as R
from tools.full_math.implementation import payoffchain_check as K

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[2]

LEAN_MODULE = (REPO / 'proofs/lean/juris_lean/JurisLean/Seams/'
               'UnifiedPayoffChain.lean')

NEEDLE_THEOREMS = (
    'legal_payoff_preserved',
    'legal_time_nonanticipation',
)

F = Fraction

# ---------------------------------------------------------------------------
# Source pinning (W1-13 batch receipt anchor)
# ---------------------------------------------------------------------------


def test_lean_module_pins_both_needles():
    """The Lean contract file exists and declares both needle flagships by
    their original acceptance names (appendix I.13)."""
    text = LEAN_MODULE.read_text(encoding='utf-8')
    for name in NEEDLE_THEOREMS:
        assert f'theorem {name}' in text, name
    # needle 28 consumes the PayoffEquilibrium anchor; needle 48 consumes
    # the fourteen-family rule bodies, Gap05's firing lemma and Temporal's
    # trunc view.
    for imp in ('JurisLean.Seams.PayoffEquilibrium',
                'JurisLean.Seams.UnifiedFourteenFamilies',
                'JurisLean.Seams.UnifiedNeedlesGap05',
                'JurisLean.Seams.Temporal'):
        assert f'import {imp}' in text, imp


# ---------------------------------------------------------------------------
# Needle 28: layer 1 -> 2 (total and image preservation)
# ---------------------------------------------------------------------------


def _flow_family():
    """Synthetic flow family: signed amounts, mixed kinds, tags."""
    mk = R.CashEntry
    c = R.Consequence
    fams = [
        (),
        (mk(0, c.COST_BURDEN_LOSER, F(10), False),),
        (mk(0, c.COST_BURDEN_LOSER, F(10), False),
         mk(1, c.ENFORCEMENT_ACCESS, F(-3), True),
         mk(2, c.RES_JUDICATA, F(1), False)),
        (mk(0, c.NO_TITLE_NO_COST, F(7), True),),
        tuple(mk(i, c.COST_BURDEN_PARTIAL, F(i) - F(3), i % 2 == 0)
              for i in range(6)),
        (mk(0, c.COST_OWN_ON_DISMISS, F(1, 3), False),
         mk(1, c.COST_OWN_ON_DISMISS, F(2, 3), True)),
    ]
    return fams


def test_total_preservation_on_flow_family():
    """Cost aggregation preserves the unweighted cash total on every flow of
    the family (positive sweep), cross-checked by the independent checker."""
    for es in _flow_family():
        rep = K.check_total_preservation(es, R.cost_total(es), R.cash_total(es))
        assert rep.ok, rep.reasons
        assert R.cost_total(es) == R.cash_total(es)


def test_image_preservation_and_netting_boundary():
    """Positive: every nonzero cost component's kind is witnessed by an
    entry.  Negative (netting boundary): +5/-5 same-kind entries aggregate
    to zero — the cost layer sees NET not GROSS, so the reverse image
    direction legitimately fails."""
    for es in _flow_family():
        rep = K.check_image_preservation(es)
        assert rep.ok, rep.reasons

    mk = R.CashEntry
    c = R.Consequence
    netted = (mk(0, c.COST_BURDEN_LOSER, F(5), False),
              mk(1, c.COST_BURDEN_LOSER, F(-5), True))
    assert R.cash_total(netted) == 0
    assert all(R.cost_at(netted, k) == 0 for k in R.ALL_CONS)


def test_bookkeeping_bit_blindness():
    """Layer-1 bookkeeping rewrites (ledger-tag flips) leave costs, the
    integral and the reading untouched — the first link of the chain."""
    for es in _flow_family():
        flipped = R.flip_tags(es)
        for k in R.ALL_CONS:
            assert R.cost_at(flipped, k) == R.cost_at(es, k)
        for role in (R.Role.CLAIMANT, R.Role.RESPONDENT):
            assert R.pref_integral(role, flipped) == R.pref_integral(role, es)
    flow = R.PayFlow(_flow_family()[2], R.LegalStatus.UPHELD, False)
    flipped_flow = R.replace(flow, entries=R.flip_tags(flow.entries))
    assert R.legal_reading(R.Role.CLAIMANT, flipped_flow) == \
        R.legal_reading(R.Role.CLAIMANT, flow)


# ---------------------------------------------------------------------------
# Needle 28: layer 2 -> 3 (congruence and covariance)
# ---------------------------------------------------------------------------


def test_integral_covariance_and_congruence():
    """Adding one entry moves the integral by exactly valuation*amount for
    both roles (positive sweep); cost-equal flows have equal integrals."""
    mk = R.CashEntry
    c = R.Consequence
    for es in _flow_family():
        for e in (mk(9, c.RES_JUDICATA, F(4), False),
                  mk(9, c.COST_OWN_ON_DISMISS, F(-7, 2), True)):
            for role in (R.Role.CLAIMANT, R.Role.RESPONDENT):
                before = R.pref_integral(role, es)
                after = R.pref_integral(role, (e,) + es)
                assert after == before + R.CONSEQUENCE_VALUATION[(role, e.kind)] * e.amount
                rep = K.check_integral_covariance(role, e, es, before, after)
                assert rep.ok, rep.reasons


def test_status_vector_grid_all_eight_cells():
    """Layer 3 -> 4: on every status vector the preference integral equals
    the anchor legal payoff — all 8 cells derived from the frozen tables
    (claimant 7/3/-3/0, respondent -7/-3/0/0)."""
    expected_grid = {
        (R.Role.CLAIMANT, R.LegalStatus.UPHELD): F(7),
        (R.Role.CLAIMANT, R.LegalStatus.PARTIALLY_UPHELD): F(3),
        (R.Role.CLAIMANT, R.LegalStatus.DISMISSED): F(-3),
        (R.Role.CLAIMANT, R.LegalStatus.UNENFORCEABLE): F(0),
        (R.Role.RESPONDENT, R.LegalStatus.UPHELD): F(-7),
        (R.Role.RESPONDENT, R.LegalStatus.PARTIALLY_UPHELD): F(-3),
        (R.Role.RESPONDENT, R.LegalStatus.DISMISSED): F(0),
        (R.Role.RESPONDENT, R.LegalStatus.UNENFORCEABLE): F(0),
    }
    reported = {(role, st): R.payoff_of(role, st, False)
                for role in (R.Role.CLAIMANT, R.Role.RESPONDENT)
                for st in (R.LegalStatus.UPHELD, R.LegalStatus.PARTIALLY_UPHELD,
                           R.LegalStatus.DISMISSED, R.LegalStatus.UNENFORCEABLE)}
    readings = {(role, st): R.legal_reading(role, R.status_flow(st))
                for (role, st) in reported}
    assert reported == expected_grid
    assert readings == expected_grid
    rep = K.check_status_reading_grid(reported, readings)
    assert rep.ok, rep.reasons


def test_reading_docket_blindness():
    """Layer 4: the anchor reading depends on the status projection only
    (both docket bits give the same reading)."""
    for role in (R.Role.CLAIMANT, R.Role.RESPONDENT):
        for st in (R.LegalStatus.UPHELD, R.LegalStatus.DISMISSED):
            r1 = R.payoff_of(role, st, True)
            r2 = R.payoff_of(role, st, False)
            rep = K.check_docket_blindness(role, st, True, False, r1, r2)
            assert rep.ok, rep.reasons


# ---------------------------------------------------------------------------
# Needle 28: end-to-end reflection and its zero-weight failure
# ---------------------------------------------------------------------------


def test_single_kind_reflection_positive():
    """Same kind, nonzero weight, equal readings => equal amounts (positive
    instance, both directions checked by the checker)."""
    mk = R.CashEntry
    c = R.Consequence
    es = _flow_family()[2]
    e1 = mk(9, c.COST_BURDEN_LOSER, F(6), False)
    e2 = mk(9, c.COST_BURDEN_LOSER, F(6), True)
    for role in (R.Role.CLAIMANT, R.Role.RESPONDENT):
        r1 = R.legal_reading(R.Role.CLAIMANT, R.PayFlow((e1,) + es, R.LegalStatus.UPHELD, False)) \
            if role == R.Role.CLAIMANT else None
        reading_equal = (R.pref_integral(role, (e1,) + es)
                         == R.pref_integral(role, (e2,) + es))
        rep = K.check_reflection(role, es, e1, e2, reading_equal, True)
        assert rep.ok, rep.reasons
        if R.CONSEQUENCE_VALUATION[(role, e1.kind)] != 0:
            assert reading_equal


def test_reflection_fails_at_zero_weight():
    """Negative: claimant's no-title-no-cost weight is 0 — amounts 5 and 7
    give EQUAL readings, so reflection fails without the nonzero-weight
    premise (the premise is not decoration)."""
    mk = R.CashEntry
    c = R.Consequence
    e1 = mk(0, c.NO_TITLE_NO_COST, F(5), False)
    e2 = mk(0, c.NO_TITLE_NO_COST, F(7), False)
    assert R.CONSEQUENCE_VALUATION[(R.Role.CLAIMANT, c.NO_TITLE_NO_COST)] == 0
    r1 = R.pref_integral(R.Role.CLAIMANT, (e1,))
    r2 = R.pref_integral(R.Role.CLAIMANT, (e2,))
    assert r1 == r2 == 0
    assert e1.amount != e2.amount
    rep = K.check_reflection(R.Role.CLAIMANT, (), e1, e2, True, False)
    assert rep.ok, rep.reasons


# ---------------------------------------------------------------------------
# Needle 28: chain-breaking counterexamples and old-anchor independence
# ---------------------------------------------------------------------------


def test_status_projection_drops_cash():
    """Counterexample 1: the old status-only encoding is blind to the cash
    flow — same status projection, different readings (7 vs 14)."""
    fl1 = R.status_flow(R.LegalStatus.UPHELD)
    fl2 = R.doubled_status_flow(R.LegalStatus.UPHELD)
    assert R.status_projection(fl1) == R.status_projection(fl2)
    r1 = R.legal_reading(R.Role.CLAIMANT, fl1)
    r2 = R.legal_reading(R.Role.CLAIMANT, fl2)
    assert (r1, r2) == (F(7), F(14))
    rep = K.check_status_projection_drops_cash(fl1, fl2)
    assert rep.ok, rep.reasons


def test_dropped_kind_breaks_total():
    """Counterexample 2: a cost encoding that drops res-judicata cannot
    preserve the cash total — a res-judicata-only flow and the empty flow
    are indistinguishable to it."""
    mk = R.CashEntry
    es1 = (mk(0, R.Consequence.RES_JUDICATA, F(5), False),)
    es2 = ()
    assert all(R.cost_at_dropped(es1, k) == R.cost_at_dropped(es2, k)
               for k in R.ALL_CONS)
    assert R.cash_total(es1) != R.cash_total(es2)


def test_old_anchor_independence():
    """The old status congruence (anchor) still holds on the counterexample
    pair while the cash side moves — the constructive repair of 'the payoff
    and cash-flow preservations being two independent conjuncts'."""
    fl1 = R.status_flow(R.LegalStatus.UPHELD)
    fl2 = R.doubled_status_flow(R.LegalStatus.UPHELD)
    payoff1 = R.payoff_of(R.Role.CLAIMANT, fl1.declared_status, fl1.docket)
    payoff2 = R.payoff_of(R.Role.CLAIMANT, fl2.declared_status, fl2.docket)
    reading1 = R.legal_reading(R.Role.CLAIMANT, fl1)
    reading2 = R.legal_reading(R.Role.CLAIMANT, fl2)
    rep = K.check_old_anchor_independence(payoff1, payoff2, reading1, reading2)
    assert rep.ok, rep.reasons


def test_witness_readouts():
    """Witness cash flow: totals 17, claimant integral 44, respondent -44
    ([代拟稿] amounts over the anchor weights)."""
    assert R.cash_total(R.WITNESS_ENTRIES) == 17
    assert R.cost_total(R.WITNESS_ENTRIES) == 17
    assert R.pref_integral(R.Role.CLAIMANT, R.WITNESS_ENTRIES) == 44
    assert R.pref_integral(R.Role.RESPONDENT, R.WITNESS_ENTRIES) == -44
    rep = K.check_total_preservation(R.WITNESS_ENTRIES,
                                     R.cost_total(R.WITNESS_ENTRIES),
                                     R.cash_total(R.WITNESS_ENTRIES))
    assert rep.ok, rep.reasons


# ---------------------------------------------------------------------------
# Needle 48: per-rule use points through the view
# ---------------------------------------------------------------------------


def test_view_is_trunc_and_future_irrelevant():
    """lawView keeps exactly the <= as_of events; appending strictly-future
    events leaves it byte-identical."""
    ledger = R.WIT_LEDGER
    view = R.law_view(R.T_CUT, ledger)
    assert view == tuple(e for e in ledger if e[0] <= R.T_CUT)
    future = ((200, 'matContractSigned'), (150, 'matNQualified'))
    assert R.law_view(R.T_CUT, ledger + future) == view


def test_use_points_of_three_real_rules():
    """Per-rule use point (R01/R23/R19): every premise atom is a material
    atom and its docket read equals its view read — on several ledgers and
    cut points (positive sweep + independent checker)."""
    ledgers = [R.WIT_LEDGER, R.LATE_LEDGER, (), R.WIT_LEDGER + ((150, 'matNQualified'),)]
    cuts = [0, 100, 160]
    for ledger in ledgers:
        for as_of in cuts:
            for rule in (R.R01, R.R23, R.R19):
                rep = K.check_use_point(rule, ledger, as_of)
                assert rep.ok, (rule.rid, as_of, rep.reasons)
    # the docket material bridge agrees with the reference read
    docket = R.law_docket(R.T_CUT, R.WIT_LEDGER)
    for atom in R.MAT_ATOMS:
        assert R.material_holds(atom, docket) == R.occurs_by(R.T_CUT, R.WIT_LEDGER, atom)


def test_witness_firing_through_view():
    """Positive: on the witness ledger all three real rule bodies fire
    through the view (their conclusions enter the rule-network closure)."""
    for rule in (R.R01, R.R23, R.R19):
        assert R.rule_fires_at(rule, R.WIT_LEDGER, R.T_CUT) is True
    # downstream chains also light up through the same view
    assert R.eval_at('guarantorStanding', R.WIT_LEDGER + ((90, 'matGuaranteeByGOpen'),), R.T_CUT)
    assert R.eval_at('holdOnLoanFinal', R.WIT_LEDGER, R.T_CUT)


def test_future_blindness_of_three_real_rules():
    """Per-rule non-anticipation: appending strictly-future events —
    including a late DUPLICATE of an already-on-file material and a brand
    new material — leaves each rule body's evaluation unchanged."""
    futures = [
        ((200, 'matContractSigned'),),
        ((150, 'matNQualified'),),
        ((101, 'matHearingMissed'), (300, 'matRecordContradictions')),
    ]
    for future in futures:
        for rule in (R.R01, R.R23, R.R19):
            rep = K.check_future_blindness(rule, R.WIT_LEDGER, future, R.T_CUT)
            assert rep.ok, (rule.rid, future, rep.reasons)
            assert R.rule_fires_at(rule, R.WIT_LEDGER + future, R.T_CUT) == \
                R.rule_fires_at(rule, R.WIT_LEDGER, R.T_CUT)


def test_future_only_ledgers_rejected():
    """Negative (out-of-window consumption rejected): with everything dated
    after the cut, no material is on file and none of the three rules can
    fire — the blocking is recomputed inline by the checker."""
    for future in ((), ((200, 'matContractSigned'), (210, 'matHearingMissed'))):
        as_of = 100
        for x in future:
            assert as_of < x[0]
        for rule in (R.R01, R.R23, R.R19):
            assert R.rule_fires_at(rule, future, as_of) is False
        # a premise material is genuinely absent from the view
        rep = K.check_blocked_when_missing(R.R01, future, as_of, 'matContractSigned')
        assert rep.ok, rep.reasons


def test_eval_is_view_valued():
    """The old anchor's hview premise is a checked FACT here: evaluating on
    the raw ledger equals evaluating on the pre-truncated ledger."""
    for atom in ('loanEntitlement', 'adminDefectsEstablished', 'stayForSuccession'):
        for as_of in (100, 160):
            rep = K.check_eval_is_view_valued(atom, R.LATE_LEDGER, as_of)
            assert rep.ok, rep.reasons
            assert R.eval_at(atom, R.LATE_LEDGER, as_of) == \
                R.eval_at(atom, R.law_view(as_of, R.LATE_LEDGER), as_of)


def test_late_material_as_of_dynamics():
    """As-of dynamics witness: the contract material arrives on day 150 —
    R01 does NOT fire at cut 100 (blocked) and DOES fire at cut 160; what
    moves the reading is the adjudication time, not the information."""
    assert R.eval_at('loanEntitlement', R.LATE_LEDGER, 100) is False
    assert R.eval_at('loanEntitlement', R.LATE_LEDGER, 160) is True
    # and the same ledger with the late event deleted is identical at 100
    trimmed = tuple(e for e in R.LATE_LEDGER if e[0] != 150)
    assert R.eval_at('loanEntitlement', R.LATE_LEDGER, 100) == \
        R.eval_at('loanEntitlement', trimmed, 100)


def test_non_material_event_atoms_are_inert():
    """Ledger hygiene boundary: an event carrying a derived atom changes no
    material read and no rule evaluation (the docket reads materials only)."""
    spurious = R.WIT_LEDGER + ((50, 'loanEntitlement'),)
    assert R.law_docket(R.T_CUT, spurious) == R.law_docket(R.T_CUT, R.WIT_LEDGER)
    for rule in (R.R01, R.R23, R.R19):
        assert R.rule_fires_at(rule, spurious, R.T_CUT) == \
            R.rule_fires_at(rule, R.WIT_LEDGER, R.T_CUT)


# ---------------------------------------------------------------------------
# Cross-layer sweep: checker-vs-reference differential on random-ish flows
# ---------------------------------------------------------------------------


def test_differential_closure_and_integral_sweep():
    """Differential sweep: the independent checker's closure and integral
    recomputations agree with the reference on a generated family of
    ledgers/flows (zero function sharing — dataclasses and frozen tables
    only)."""
    mk = R.CashEntry
    c = R.Consequence
    flows = []
    day = 0
    for i in range(8):
        flows.append(mk(day, R.ALL_CONS[i % 6], F(i - 3) / F(2), i % 3 == 0))
        day += 7
    for role in (R.Role.CLAIMANT, R.Role.RESPONDENT):
        for n in range(0, len(flows) + 1, 3):
            es = tuple(flows[:n])
            assert R.pref_integral(role, es) == \
                K._integral(role, es)  # checker inline recompute
            assert R.cost_total(es) == K._cost_total(es)

    ledgers = [
        R.WIT_LEDGER,
        R.LATE_LEDGER,
        R.WIT_LEDGER + ((35, 'matSamplingMatch'), (45, 'matExceedance'),
                        (55, 'matNoExculpation'), (65, 'matInNewLawPeriod'),
                        (75, 'matNQualified'), (85, 'matEcoCostDocs')),
    ]
    for ledger in ledgers:
        for as_of in (0, 40, 80, 100, 160):
            for atom in ('loanEntitlement', 'ecoRemediationCosts',
                         'adminDefectsEstablished', 'stayForSuccession'):
                assert R.eval_at(atom, ledger, as_of) == \
                    K._eval(atom, ledger, as_of)


if __name__ == '__main__':
    raise SystemExit(pytest.main([__file__, '-q']))
