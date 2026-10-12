"""W16 (needle 30) tests: Kakutani existence + CAD same-equilibrium mirrors.

Fixtures are exact Fraction games:

* matching pennies (unique fully mixed equilibrium 1/2-1/2);
* prisoner's-dilemma-shaped compliance game (unique pure equilibrium);
* coordination game (two pure + one mixed equilibrium -- completeness);
* the GapMid Fin 3 compliance game (3 players, pure all-comply equilibrium)
  consumed through a LegalActionMenu of lawful/sanction evaluations;
* CAD-side points: formula denotation equals the Nash verdict, at
  equilibria, at perturbed non-equilibria, and at non-simplex assignments.

Every reference output is re-verified by the independent checker
(`equilexist_check`), which shares no code with the reference module.
"""
from __future__ import annotations

import sys
from fractions import Fraction as Q
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "implementation"))

import equilexist_check as chk  # noqa: E402
import equilexist_ref as ref  # noqa: E402

P2 = [0, 1]
A2 = [0, 1]
P3 = [0, 1, 2]
B2 = [False, True]


def _pay_from_table(table) -> dict:
    """table[(profile, player)] -> Fraction, as a flat dict keyed like Lean."""
    return dict(table)


# ---------------------------------------------------------------------------
# Fixtures
# ---------------------------------------------------------------------------

# Matching pennies: row player wins on match, column on mismatch.
PENNIES_TABLE = {
    ((0, 0), 0): Q(1), ((0, 0), 1): Q(-1),
    ((0, 1), 0): Q(-1), ((0, 1), 1): Q(1),
    ((1, 0), 0): Q(-1), ((1, 0), 1): Q(1),
    ((1, 1), 0): Q(1), ((1, 1), 1): Q(-1),
}
PENNIES_U = ref.table_u({
    (0, 0): {0: Q(1), 1: Q(-1)},
    (0, 1): {0: Q(-1), 1: Q(1)},
    (1, 0): {0: Q(-1), 1: Q(1)},
    (1, 1): {0: Q(1), 1: Q(-1)},
})

# Compliance game (prisoner-dilemma shape): comply=1 beats defect=0 only if
# the other complies; defecting is never strictly better here -- the point of
# this fixture is a unique pure equilibrium (comply, comply).
PD_TABLE = {
    ((0, 0), 0): Q(3), ((0, 0), 1): Q(3),
    ((0, 1), 0): Q(0), ((0, 1), 1): Q(5),
    ((1, 0), 0): Q(5), ((1, 0), 1): Q(0),
    ((1, 1), 0): Q(1), ((1, 1), 1): Q(1),
}
PD_U = ref.table_u({
    (0, 0): {0: Q(3), 1: Q(3)},
    (0, 1): {0: Q(0), 1: Q(5)},
    (1, 0): {0: Q(5), 1: Q(0)},
    (1, 1): {0: Q(1), 1: Q(1)},
})

# Coordination game: equilibria (0,0), (1,1), and the mixed (1/3, 2/3) pair.
COORD_U = ref.table_u({
    (0, 0): {0: Q(2), 1: Q(2)},
    (0, 1): {0: Q(0), 1: Q(0)},
    (1, 0): {0: Q(0), 1: Q(0)},
    (1, 1): {0: Q(1), 1: Q(1)},
})
COORD_TABLE = {
    ((0, 0), 0): Q(2), ((0, 0), 1): Q(2),
    ((0, 1), 0): Q(0), ((0, 1), 1): Q(0),
    ((1, 0), 0): Q(0), ((1, 0), 1): Q(0),
    ((1, 1), 0): Q(1), ((1, 1), 1): Q(1),
}

# GapMid u3 compliance game on Fin 3 x Bool, through a legal menu:
# pay a i = lawful 1 if a i else lawful 0  (toQ: 1 / 0).
MENU3 = {
    ((a0, a1, a2), i): ("lawful", Q(1) if (a0, a1, a2)[i] else Q(0))
    for (a0, a1, a2) in [(x, y, z) for x in (False, True)
                         for y in (False, True) for z in (False, True)]
    for i in (0, 1, 2)
}
MENU3_TABLE = ref.menu_payoff(MENU3, P3, B2)


def menu3_u(a, i):
    return MENU3_TABLE[a][i]


def _sigma2(p: Q):
    return {0: [p, 1 - p], 1: [Q(1, 2), Q(1, 2)]}


def _grid_rows():
    return [[Q(k, 6), Q(6 - k, 6)] for k in range(7)]


# ---------------------------------------------------------------------------
# Carrier basics (mirrors of pointR / pureMR / InSimplexR / euR / euR_pureMR)
# ---------------------------------------------------------------------------


def test_point_row_and_simplex():
    assert ref.is_row_simplex(ref.point_row(A2, 0))
    assert ref.is_row_simplex(ref.point_row(A2, 1))
    assert not ref.is_row_simplex([Q(1), Q(1)])
    assert not ref.is_row_simplex([Q(-1, 2), Q(3, 2)])


def test_eu_pure_profile_reads_table():
    for a0 in A2:
        for a1 in A2:
            sig = ref.pure_profile(A2, {0: a0, 1: a1})
            assert ref.eu(PENNIES_U, sig, 0, P2, A2) == PENNIES_TABLE[((a0, a1), 0)]
            assert ref.eu(PENNIES_U, sig, 1, P2, A2) == PENNIES_TABLE[((a0, a1), 1)]


def test_eu_multilinear_value():
    sig = {0: [Q(1, 2), Q(1, 2)], 1: [Q(1, 3), Q(2, 3)]}
    # pennies row player: P(match) - P(mismatch)
    val = ref.eu(PENNIES_U, sig, 0, P2, A2)
    assert val == (Q(1, 2) * Q(1, 3) + Q(1, 2) * Q(2, 3)
                   - Q(1, 2) * Q(2, 3) - Q(1, 2) * Q(1, 3))
    assert val == 0


# ---------------------------------------------------------------------------
# Kakutani components
# ---------------------------------------------------------------------------


def test_best_response_vertex_exists():
    for sigma in [{0: r, 1: r2} for r in _grid_rows() for r2 in _grid_rows()]:
        for i in P2:
            b = ref.best_pure_response(PENNIES_U, sigma, i, P2, A2)
            for row in _grid_rows():
                trial = ref.updated(sigma, i, row)
                assert (ref.eu(PENNIES_U, trial, i, P2, A2)
                        <= ref.eu(PENNIES_U, ref.updated(sigma, i, ref.point_row(A2, b)),
                                  i, P2, A2))


def test_best_response_vertex_checked_independently():
    sigma = {0: [Q(1, 4), Q(3, 4)], 1: [Q(2, 3), Q(1, 3)]}
    chk.check_best_response_vertex(PENNIES_TABLE, sigma, P2, A2, _grid_rows())
    chk.check_best_response_vertex(COORD_TABLE, sigma, P2, A2, _grid_rows())


def test_br_profile_is_br_corr_member():
    sigma = {0: [Q(1, 4), Q(3, 4)], 1: [Q(2, 3), Q(1, 3)]}
    brp = ref.br_profile(PENNIES_U, sigma, P2, A2)
    assert ref.in_br_corr(PENNIES_U, sigma, brp, P2, A2)


def test_fixed_point_iff_nash():
    for game_u, game_pay in ((PENNIES_U, PENNIES_TABLE), (COORD_U, COORD_TABLE)):
        for p in (Q(0), Q(1, 3), Q(1, 2), Q(1)):
            sig = {0: [p, 1 - p], 1: [Q(1, 3), Q(2, 3)]}
            assert ref.fixed_point_is_nash(game_u, sig, P2, A2)
            # checker cross-verdict
            assert ref.is_nash(game_u, sig, P2, A2) == chk.nash_check(game_pay, sig, P2, A2)


def test_eu_dev_linear_identity():
    for row in _grid_rows():
        assert ref.eu_dev_linear_identity(
            COORD_U, {0: [Q(1, 3), Q(2, 3)], 1: [Q(1, 2), Q(1, 2)]}, 0, row, P2, A2)


def test_eu_row_affine_identity():
    r1, r2 = [Q(1, 3), Q(2, 3)], [Q(5, 6), Q(1, 6)]
    a, b = Q(2, 5), Q(3, 5)
    assert ref.eu_row_affine_identity(PD_U, {0: r1, 1: r2}, 0, r1, r2, a, b, P2, A2)
    chk.check_affinity_identity(PD_TABLE, {0: r1, 1: r2}, 0, r1, r2, a, b, P2, A2)


# ---------------------------------------------------------------------------
# Legal action menu
# ---------------------------------------------------------------------------


def test_legal_eval_to_q():
    assert ref.legal_eval_to_q(("lawful", Q(7, 3))) == Q(7, 3)
    assert ref.legal_eval_to_q(("sanction", Q(5))) == Q(-5)


def test_menu_payoff_matches_u3_and_pure_equilibrium():
    # menu table equals the GapMid u3 table
    for combo, d in MENU3_TABLE.items():
        for i in P3:
            expected = Q(1) if combo[i] else Q(0)
            assert d[i] == expected
    sigma_true = ref.pure_profile(B2, {i: True for i in P3})
    assert ref.eu(menu3_u, sigma_true, 1, P3, B2) == Q(1)
    assert ref.is_nash(menu3_u, sigma_true, P3, B2)
    sigma_false = ref.pure_profile(B2, {i: False for i in P3})
    assert not ref.is_nash(menu3_u, sigma_false, P3, B2)


def test_kakutani_existence_witness_menu():
    # existence on the menu game: all-true pure equilibrium is a witness
    sig = ref.pure_profile(B2, {i: True for i in P3})
    assert ref.is_nash(menu3_u, sig, P3, B2)


# ---------------------------------------------------------------------------
# Reference equilibrium finder + independent completeness
# ---------------------------------------------------------------------------


def test_pennies_unique_mixed_equilibrium():
    equil = ref.find_all_equilibria_2p(PENNIES_U, A2)
    assert equil == [([Q(1, 2), Q(1, 2)], [Q(1, 2), Q(1, 2)])]
    chk.check_equilibrium_outputs(PENNIES_TABLE, equil, P2, A2)
    chk.check_2x2_completeness(PENNIES_TABLE, equil)


def test_pd_unique_pure_equilibrium():
    equil = ref.find_all_equilibria_2p(PD_U, A2)
    assert equil == [([Q(0), Q(1)], [Q(0), Q(1)])]
    chk.check_equilibrium_outputs(PD_TABLE, equil, P2, A2)
    chk.check_2x2_completeness(PD_TABLE, equil)


def test_coordination_three_equilibria():
    equil = ref.find_all_equilibria_2p(COORD_U, A2)
    assert len(equil) == 3
    assert ([Q(1), Q(0)], [Q(1), Q(0)]) in equil
    assert ([Q(0), Q(1)], [Q(0), Q(1)]) in equil
    assert ([Q(1, 3), Q(2, 3)], [Q(1, 3), Q(2, 3)]) in equil
    chk.check_equilibrium_outputs(COORD_TABLE, equil, P2, A2)
    chk.check_2x2_completeness(COORD_TABLE, equil)


def test_non_equilibrium_rejections():
    # matching pennies: any pure profile is not an equilibrium
    for a0 in A2:
        for a1 in A2:
            sig = ref.pure_profile(A2, {0: a0, 1: a1})
            assert not ref.is_nash(PENNIES_U, sig, P2, A2)
            assert not chk.nash_check(PENNIES_TABLE, sig, P2, A2)
    # asymmetric mixes are not equilibria either
    for p in (Q(1, 3), Q(2, 3)):
        sig = {0: [p, 1 - p], 1: [Q(1, 2), Q(1, 2)]}
        assert not ref.is_nash(PENNIES_U, sig, P2, A2)


# ---------------------------------------------------------------------------
# Upstream bridge mirrors (toRow / pmfOfRow roundtrip)
# ---------------------------------------------------------------------------


def test_pmf_of_row_roundtrip():
    for row in _grid_rows():
        chk.check_roundtrip(row, ref.pmf_of_row, ref.to_row, A2)
    assert ref.pmf_of_row([Q(3, 2), Q(-1, 2)], A2) is None
    assert ref.pmf_of_row([Q(1, 2), Q(1, 2), Q(0)], A2) is None


def test_upstream_bridge_to_row_profile():
    # toRow on a profile of PMF rows keeps the equilibrium verdict (upstream
    # IsNash <-> IsNashR at the converted profile, here instantiated on the
    # pennies equilibrium)
    equil = ref.find_all_equilibria_2p(PENNIES_U, A2)[0]
    pmf_rows = {0: {a: equil[0][a] for a in A2}, 1: {a: equil[1][a] for a in A2}}
    sigma = {i: ref.to_row(pmf_rows[i], A2) for i in P2}
    assert ref.is_nash(PENNIES_U, sigma, P2, A2)


# ---------------------------------------------------------------------------
# CAD side: same whole equilibrium relation
# ---------------------------------------------------------------------------


def test_cad_var_table_roundtrip():
    sigma = {0: [Q(1, 3), Q(2, 3)], 1: [Q(3, 4), Q(1, 4)]}
    rho = ref.rho_of(P2, A2, sigma)
    assert ref.cad_var_n(P2, A2) == 4
    assert ref.row_of(P2, A2, rho) == sigma


def _rho(p0, p1):
    return ref.rho_of(P2, A2, {0: [p0, 1 - p0], 1: [p1, 1 - p1]})


def test_cad_formula_true_at_equilibria():
    for u, pts in ((PENNIES_U, [Q(1, 2)]),
                   (PD_U, [Q(0)]),
                   (COORD_U, [Q(0), Q(1, 3), Q(1)])):
        for p in pts:
            assert ref.cad_formula_denote(u, _rho(p, p), P2, A2)
            assert ref.cad_same_equilibrium_relation(u, _rho(p, p), P2, A2)


def test_cad_formula_false_off_equilibria():
    # pennies: (1/3, 1/2) is not an equilibrium -- player 0 gains by deviating
    rho = _rho(Q(1, 3), Q(1, 2))
    assert not ref.cad_formula_denote(PENNIES_U, rho, P2, A2)
    assert ref.cad_same_equilibrium_relation(PENNIES_U, rho, P2, A2)
    # coordination: (1/2, 1/3) mismix -- both deviate profitably
    rho = _rho(Q(1, 2), Q(1, 3))
    assert not ref.cad_formula_denote(COORD_U, rho, P2, A2)
    assert ref.cad_same_equilibrium_relation(COORD_U, rho, P2, A2)


def test_cad_formula_rejects_non_simplex():
    rho = ref.rho_of(P2, A2, {0: [Q(3, 2), Q(-1, 2)], 1: [Q(1, 2), Q(1, 2)]})
    assert not ref.cad_formula_denote(PENNIES_U, rho, P2, A2)
    rho = ref.rho_of(P2, A2, {0: [Q(1, 2), Q(1)], 1: [Q(1, 2), Q(1, 2)]})
    assert not ref.cad_formula_denote(PENNIES_U, rho, P2, A2)


def test_cad_same_relation_pointwise_checked():
    rhos = [_rho(a, b) for a in (Q(0), Q(1, 3), Q(1, 2), Q(3, 4), Q(1))
            for b in (Q(0), Q(1, 3), Q(1, 2), Q(3, 4), Q(1))]
    for u, pay in ((PENNIES_U, PENNIES_TABLE), (COORD_U, COORD_TABLE)):
        chk.check_same_relation_points(
            pay, u, rhos,
            lambda r: ref.row_of(P2, A2, r),
            lambda uu, r, ps, acts: ref.cad_formula_denote(uu, r, ps, acts),
            P2, A2)


def test_cad_solution_nonempty_via_existence():
    # every reference-found equilibrium yields a satisfying assignment
    for u in (PENNIES_U, PD_U, COORD_U):
        equil = ref.find_all_equilibria_2p(u, A2)
        assert len(equil) >= 1
        for sig0, sig1 in equil:
            rho = ref.rho_of(P2, A2, {0: sig0, 1: sig1})
            assert ref.cad_formula_denote(u, rho, P2, A2)


def test_cad_menu_game_three_players():
    # CAD relation on the 3-player menu game: all-true profile satisfies the
    # polynomial system; all-false does not (player 0 gains by complying)
    rho_t = ref.rho_of(P3, B2, ref.pure_profile(B2, {i: True for i in P3}))
    rho_f = ref.rho_of(P3, B2, ref.pure_profile(B2, {i: False for i in P3}))
    assert ref.cad_formula_denote(menu3_u, rho_t, P3, B2)
    assert not ref.cad_formula_denote(menu3_u, rho_f, P3, B2)
    assert ref.cad_same_equilibrium_relation(menu3_u, rho_t, P3, B2)
    assert ref.cad_same_equilibrium_relation(menu3_u, rho_f, P3, B2)


# ---------------------------------------------------------------------------
# Deviation characterization (sampled sanity, full iff is in Lean)
# ---------------------------------------------------------------------------


def test_deviation_characterization_sampled():
    sigma = {0: [Q(1, 3), Q(2, 3)], 1: [Q(1, 2), Q(1, 2)]}
    chk.check_deviation_characterization_sampled(
        PENNIES_TABLE, sigma, P2, A2, _grid_rows())
    sigma_eq = {0: [Q(1, 2), Q(1, 2)], 1: [Q(1, 2), Q(1, 2)]}
    chk.check_deviation_characterization_sampled(
        PENNIES_TABLE, sigma_eq, P2, A2, _grid_rows())
