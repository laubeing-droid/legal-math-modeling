"""Joint fourteen-family network trajectory tests (W15, needle 42, I:796).

Positive cases: the full-material 17-step trajectory runs on the actual
rule network, the R07->R08->R10 depth-3 chain consumes its predecessors'
conclusions, closure consistency holds, both partial dockets still run real
(non-empty) trajectories while their blocked clusters are unreachable by
any trajectory, sources are in force, the termination bound holds, and the
exact-Fraction quantity readouts stay rational.

Negative cases: reordered steps (conclusion consumed before produced),
unknown rule ids, wrong-docket steps, non-increasing times, duplicate
firings (non-productive), borrowed premises, and full-only atoms leaking
into partial-docket runs are all rejected.

The independent checker (``nettraj_check``) re-derives every observable
with different algorithms (premise-scan accumulation, BFS derivation
search, table-derived universe counts); it never imports the reference.

Receipt note (W1-wave batch form): the 60-needle table has no slot in
tools/full_math/spec/REQUIREMENTS.json, so there is no validate_binding
row for W15; the batch receipt is recorded in
.local/agent_W15_net_traj_report.md per the wave convention, and this
suite pins the Lean sources by name.
"""
from fractions import Fraction
from pathlib import Path

import pytest

from tools.full_math.implementation import nettraj_check as K
from tools.full_math.implementation import nettraj_ref as R

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[2]

LEAN_MODULE = (REPO / 'proofs/lean/juris_lean/JurisLean/Seams/'
               'UnifiedNetTrajectory.lean')

LEAN_THEOREMS = (
    'nontrivial_net_trajectory_exists',
    'full_net_trajectory_end_to_end',
    'partial_net_trajectory_difference',
    'ecoChain_ok',
    'ecoChain_productive',
    'ecoChain_times',
    'eco_chain_depth3',
    'fullTraj_ok',
    'fullTraj_productive',
    'fullTraj_times',
    'fullTraj_length',
    'fullTraj_run',
    'fullTraj_sources',
    'net_atom_card',
    'traceOk_mono',
    'traceOk_runNetTrace',
    'traceOk_concl_mem',
    'traceOk_split',
    'traceOk_start_mono',
    'traceOk_closure',
    'traceOk_init_closure',
    'trace_reaches_mem_closure',
    'remainCard',
    'remain_insert_lt',
    'productive_card_bound',
    'prodStepRel',
    'prodStep_wf',
    'partialEcoTraj_ok',
    'partialBankTraj_ok',
    'partial_eco_no_traj_reaches',
    'partial_bank_no_traj_reaches',
    'ecoViolation_partial_diff',
    'bankruptcy_partial_diff',
    'not_in_closure_partialEco',
    'not_in_closure_partialBank',
)


# ---------------------------------------------------------------------------
# Source pinning (batch receipt anchor form)
# ---------------------------------------------------------------------------

def test_lean_module_exists_and_pins_theorems():
    text = LEAN_MODULE.read_text(encoding='utf-8')
    for name in LEAN_THEOREMS:
        assert name in text, name


def test_lean_module_has_no_placeholder_escapes():
    text = LEAN_MODULE.read_text(encoding='utf-8')
    for bad in ('sorryAx', 'native_decide', ': True :=', 'admit\n'):
        assert bad not in text
    # proof-position sorry / axiom declarations are absent (doc mentions only)
    for line in text.splitlines():
        s = line.strip()
        if s.startswith(('theorem ', 'def ', 'lemma ')):
            assert ' sorry' not in s and 'admit' not in s
        assert not s.startswith('axiom ')
    assert 'by decide' not in text


def test_lean_module_lf_only_no_bom():
    data = LEAN_MODULE.read_bytes()
    assert b'\r\n' not in data
    assert not data.startswith(b'\xef\xbb\xbf')


# ---------------------------------------------------------------------------
# Table shape (independent checker on the reference's structured data)
# ---------------------------------------------------------------------------

def test_rule_table_shape():
    ok, reasons = K.check_rule_table_shape(
        R.RULES, len(R.MATERIAL_ATOMS), R.DERIVED_ATOMS)
    assert ok, reasons


def test_universe_counts():
    assert len(R.MATERIAL_ATOMS) == 57
    assert len(R.DERIVED_ATOMS) == 29
    assert len(R.FAILURE_ATOMS) == 10
    assert len(R.ALL_ATOMS) == 96


# ---------------------------------------------------------------------------
# Positive: full docket, 17-step trajectory
# ---------------------------------------------------------------------------

def test_full_trajectory_runs_on_network():
    out = R.full_net_trajectory()
    assert out['ok'] and out['nonempty']
    assert out['length'] == 17
    assert out['times_increasing']
    assert out['productive']
    assert out['closure_consistent']
    assert out['bound']
    assert all(v for _, v in out['sources_in_force'])


def test_full_trajectory_independent_checks():
    out = R.full_net_trajectory()
    mats = R.init_state('full')
    ok, reasons = K.check_trace_ok(mats, R.FULL_TRAJ, out)
    assert ok, reasons
    ok, reasons = K.check_closure_consistent(
        mats, R.RULES, out,
        sample_atoms=('loanEntitlement', 'ecoRemediationCosts',
                      'wageBankruptcyPriority', 'holdOnLoanFinal'))
    assert ok, reasons
    ok, reasons = K.check_productive(mats, R.FULL_TRAJ, out)
    assert ok, reasons
    ok, reasons = K.check_bound(mats, R.RULES, R.FAILURE_ATOMS,
                                R.MATERIAL_ATOMS, R.FULL_TRAJ, out)
    assert ok, reasons
    ok, reasons = K.check_sources_in_force(out, R.SOURCE_WINDOWS, R.BASE_DAY)
    assert ok, reasons


def test_full_trajectory_covers_cross_family_wiring():
    out = R.full_net_trajectory()
    for atom in ('mortgageSecuredPriority',  # R04 consumes R01 across L02<-L01
                 'ecoRemediationCosts',      # R10 consumes R07 (L14->L05) + R08
                 'wageBankruptcyPriority',   # R17 consumes R11 + R13
                 'arbitrationStayed',        # R16 consumes R13 across L08->L14
                 'stayDecreeIssued',         # R20 consumes R19 across L13<-L06
                 'exemptionBurdenOnCarrier'):
        assert atom in out['final']


def test_every_step_log_record_shape():
    out = R.run_trace('full', R.FULL_TRAJ)
    for i, entry in enumerate(out['log']):
        assert entry['pos'] == i
        assert entry['idx'] == i
        assert entry['enabled']
        assert entry['consumed'], 'each step consumes premises'
        assert entry['produced']
        assert entry['src'] in R.SOURCE_WINDOWS


# ---------------------------------------------------------------------------
# Positive: depth-3 chain witness (R07 -> R08 -> R10)
# ---------------------------------------------------------------------------

def test_needle42_existence_witness():
    out = R.needle42_witness()
    assert out['ok'] and out['nonempty'] and out['length'] == 3
    assert 'ecoRemediationCosts' in out['final']
    assert out['closure_consistent'] and out['productive']
    assert out['times_increasing']


def test_depth3_chain_consumption_pattern():
    ok, reasons = K.check_depth3_chain(R.RULES_BY_RID, R.ECO_CHAIN)
    assert ok, reasons


def test_r10_consumes_both_predecessor_conclusions():
    r10 = R.RULES_BY_RID[10]
    assert R.RULES_BY_RID[7]['conclusion'] in r10['premises']
    assert R.RULES_BY_RID[8]['conclusion'] in r10['premises']
    assert all(p.startswith('mat') for p in R.RULES_BY_RID[7]['premises'])
    assert all(p.startswith('mat') for p in R.RULES_BY_RID[8]['premises'])


# ---------------------------------------------------------------------------
# Positive: partial dockets run real trajectories, blocked clusters unreachable
# ---------------------------------------------------------------------------

def test_partial_eco_runs_and_blocks():
    out = R.partial_eco_reading()
    assert out['ok'] and out['nonempty'] and out['length'] == 1
    assert 'publicInterestStanding' in out['final']
    assert all(out['blocked'].values())
    assert all(out['in_full_closure'].values())
    ok, reasons = K.check_blocked_cluster(
        R.init_state('partialEco'), R.RULES,
        ('ecoViolationEstablished', 'fishPrivateCompensation',
         'ecoRemediationCosts'), out)
    assert ok, reasons


def test_partial_bank_runs_and_blocks():
    out = R.partial_bank_reading()
    assert out['ok'] and out['nonempty'] and out['length'] == 4
    assert all(out['blocked'].values())
    assert all(out['in_full_closure'].values())
    for atom in ('wageDueEstablished', 'stayForSuccession', 'stayDecreeIssued',
                 'holdOnLoanFinal'):
        assert atom in out['final']
    ok, reasons = K.check_blocked_cluster(
        R.init_state('partialBank'), R.RULES,
        ('bankruptcyAccepted', 'bankruptcyExecutionStay', 'bankruptcyCivilStay',
         'arbitrationStayed', 'wageBankruptcyPriority'), out)
    assert ok, reasons


def test_eco_difference_full_vs_partial():
    full = R.closure('full')
    part = R.closure('partialEco')
    for atom in ('ecoViolationEstablished', 'fishPrivateCompensation',
                 'ecoRemediationCosts'):
        assert atom in full and atom not in part


def test_bank_difference_full_vs_partial():
    full = R.closure('full')
    part = R.closure('partialBank')
    for atom in ('bankruptcyAccepted', 'bankruptcyExecutionStay',
                 'bankruptcyCivilStay', 'arbitrationStayed',
                 'wageBankruptcyPriority'):
        assert atom in full and atom not in part


def test_missing_material_is_the_only_difference():
    assert R.init_state('full') - R.init_state('partialEco') == {
        'matExceedance'}
    assert R.init_state('full') - R.init_state('partialBank') == {
        'matAcceptanceDecided'}


# ---------------------------------------------------------------------------
# Negative cases
# ---------------------------------------------------------------------------

def test_reordered_chain_rejected():
    # R10 before R08: consumes ecoViolationEstablished before it exists.
    bad = (R.make_step(0, 7), R.make_step(1, 10), R.make_step(2, 8))
    out = R.traj_outcome('full', bad)
    assert not out['ok']
    assert any('unavailable premises' in r for r in out['reasons'])
    # the independent premise-scan also rejects the very same steps
    _acc, enabled = K._scan_final_state(R.init_state('full'), bad)
    assert not all(enabled)


def test_r17_without_bankruptcy_rejected():
    # R17 consumes bankruptcyAccepted; firing it before R13 must fail.
    bad = (R.make_step(0, 11), R.make_step(1, 17))
    out = R.traj_outcome('full', bad)
    assert not out['ok']


def test_unknown_rule_rejected():
    with pytest.raises(ValueError):
        R.make_step(0, 99)


def test_wrong_docket_steps_rejected():
    # The eco chain cannot run on the eco-partial docket (R08 blocked).
    out = R.traj_outcome('partialEco', R.ECO_CHAIN)
    assert not out['ok']
    assert not out['productive']


def test_bank_cluster_cannot_run_on_partial_bank():
    bad = (R.make_step(0, 11), R.make_step(1, 13), R.make_step(2, 17))
    out = R.traj_outcome('partialBank', bad)
    assert not out['ok']


def test_non_increasing_times_detected():
    bad = (R.make_step(5, 7), R.make_step(3, 8), R.make_step(4, 10))
    out = R.traj_outcome('full', bad)
    assert not out['times_increasing']
    ok, reasons = K.check_times_increasing(bad, out)
    assert ok, reasons


def test_duplicate_firing_not_productive():
    dup = (R.make_step(0, 7), R.make_step(1, 8), R.make_step(2, 10),
           R.make_step(3, 10))
    out = R.traj_outcome('full', dup)
    assert out['ok']  # re-firing is still well-formed ...
    assert not out['productive']  # ... but not productive
    ok, reasons = K.check_productive(R.init_state('full'), dup, out)
    assert ok, reasons


def test_trace_with_fabricated_premise_rejected():
    # A step whose rule consumes an atom no state ever provides.
    fabricated = dict(R.make_step(0, 22))  # R22 needs matDependentClaimFiled
    fabricated_premises = {'noSuchAtom', 'alsoMissing'}
    step = {'idx': 0, 'rid': 22, 'name': 'R22',
            'premises': fabricated_premises,
            'conclusion': 'holdOnDependentClaim', 'src': 'civProcLaw153_5'}
    materials = frozenset({'matDependentClaimFiled'})
    acc, enabled = K._scan_final_state(materials, [step])
    assert not all(enabled)


def test_blocked_atom_never_in_any_ok_partial_run():
    # Any trajectory on the eco-partial docket never contains the blocked atoms
    # (closure consistency: final state is a subset of the partial closure).
    for traj in (R.PARTIAL_ECO_TRAJ, (R.make_step(0, 7), R.make_step(1, 12)),
                 ()):
        out = R.run_trace('partialEco', traj)
        if out['ok']:
            for atom in ('ecoViolationEstablished', 'fishPrivateCompensation',
                         'ecoRemediationCosts'):
                assert atom not in out['final']


# ---------------------------------------------------------------------------
# Quantities (exact Fractions)
# ---------------------------------------------------------------------------

def test_quantities_exact():
    q = R.quantities_reading()
    assert q['shortfall'] == Fraction(80)
    assert q['shortfall'] > 0
    assert q['secured'] == Fraction(20)
    assert q['unsecured'] == Fraction(80)
    assert q['secured_plus_unsecured'] == q['loanPrincipal'] == Fraction(100)
    ok, reasons = K.check_quantities(q)
    assert ok, reasons


def test_float_trap_counterexample():
    # 0.3 - 0.1 != 0.2 in binary floating point; Fractions stay exact.
    assert Fraction(3, 10) - Fraction(1, 10) == Fraction(2, 10)
    assert 0.3 - 0.1 != 0.2


# ---------------------------------------------------------------------------
# Well-foundedness / termination readings
# ---------------------------------------------------------------------------

def test_remain_measure_decreases_along_witness():
    mats = R.init_state('full')
    state = set(mats)
    prev = R.remain_card(frozenset(state))
    for st in R.FULL_TRAJ:
        state.add(st['conclusion'])
        cur = R.remain_card(frozenset(state))
        assert cur < prev  # productive steps strictly decrease the measure
        prev = cur
    assert R.remain_card(frozenset(state)) == len(R.ALL_ATOMS) - len(state)


def test_productive_length_bound_witness():
    out = R.full_net_trajectory()
    assert out['length'] + len(out['init']) <= 96
    assert out['length'] + len(out['init']) == 17 + 57


# ---------------------------------------------------------------------------
# Batch receipt
# ---------------------------------------------------------------------------

def test_batch_receipt():
    full = R.full_net_trajectory()
    eco = R.partial_eco_reading()
    bank = R.partial_bank_reading()
    ok, receipt = K.check_needle42(
        full, eco, bank, R.RULES,
        R.init_state('full'), R.init_state('partialEco'),
        R.init_state('partialBank'), R.FAILURE_ATOMS)
    assert ok, receipt['reasons']
    assert all(receipt['checks'].values())
    print('W15 nettraj batch receipt:', receipt['checks'])
