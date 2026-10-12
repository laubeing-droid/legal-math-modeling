"""Mixed-equilibrium existence (Kakutani/upstream) reference entries (W16, needle 30).

Formal contract: ``JurisLean.Seams.UnifiedEquilExist.lean``
(authoritative spec line
``docs/spec/20261007-统一法律数学模型_附录I_Lean施工明细.md`` I.13 :784 --
"construct the finite game directly from the legal information/action menu and
use Kakutani; CAD outputs the same whole equilibrium relation").

The carrier mirrors the Lean module exactly:

* profiles -- per-player rational rows over a shared finite action list
  (``RowSimplexR``/``InSimplexR``/``pointR``/``pureMR`` mirrors);
* payoffs -- ``u(profile, player)`` exact ``Fraction`` tables, optionally read
  off a ``LegalActionMenu`` (``lawful``/``sancture`` legal-evaluation tags,
  ``toQ`` readings), mirroring ``LegalEval``/``LegalActionMenu.uReal``;
* eu -- ``eu(u, sigma, i)`` the finite multilinear expected utility (``euR``
  mirror over Q);
* the same-equilibrium relation -- ``is_nash`` (all mixed deviations,
  ``IsNashR`` mirror) checked through the pure-deviation characterization
  (``nashR_iff_no_pure_dev_gain`` mirror) by row decomposition
  (``euR_dev_linear`` mirror);
* Kakutani components -- best-response pure vertex maximality
  (``best_response_pure_vertex_exists`` mirror), row affinity
  (``euR_update_row_affine`` mirror), best-response correspondence membership
  and its fixed-point=Nash identity (``brCorr``/``fixed_point_brCorr_iff_nash``
  mirrors);
* upstream bridge -- ``to_row``/``pmf_of_row`` roundtrip mirrors of the PMF
  conversion lemmas;
* CAD side -- the section 8.2 polynomial equilibrium system rebuilt as an
  explicit atom list over a flattened variable table
  (``cadVarN``/``cadIdx``/``rowOf``/``euPoly``/``euDevPoly``/``cadAtom``/
  ``cadAtomList``/``cadEquilFormula``/``conjAll`` mirrors), evaluated exactly,
  with the solution-set identity ``cad_output_same_equilibrium_relation``
  mirrored pointwise;
* equilibrium finding -- exact two-player support enumeration with Fraction
  Gaussian elimination (the reference generator for equilibria; used to
  witness existence, mirroring the Lean existence theorems which hold for all
  player counts).

The independent contract checker lives in ``equilexist_check`` and shares no
code with this module.  All quantity arithmetic is exact ``Fraction``; nothing
here samples, rounds, or floats.
"""
from __future__ import annotations

from fractions import Fraction
from itertools import product as iter_product
from typing import Dict, FrozenSet, List, Mapping, Optional, Sequence, Tuple

Q = Fraction

# ---------------------------------------------------------------------------
# One-player action universe (shared, mirrors the Lean common-Act carrier)
# ---------------------------------------------------------------------------


def point_row(actions: Sequence[int], b: int) -> List[Q]:
    """Mirror of ``pointR``: the point mass on action ``b``."""
    return [Q(1) if a == b else Q(0) for a in actions]


def is_row_simplex(row: Sequence[Q]) -> bool:
    """Mirror of ``RowSimplexR``: nonnegative entries summing to one."""
    return all(x >= 0 for x in row) and sum(row, Q(0)) == 1


def is_in_simplex(actions: Sequence[int], sigma) -> bool:
    """Mirror of ``InSimplexR``: every player row is a simplex row."""
    return all(is_row_simplex(row) for row in sigma.values())


def pure_profile(actions: Sequence[int], p: Mapping[int, int]) -> Dict[int, List[Q]]:
    """Mirror of ``pureMR``: every player puts all mass on ``p[i]``."""
    return {i: point_row(actions, p[i]) for i in p}


def eu(u, sigma: Mapping[int, Sequence[Q]], i: int, players: Sequence[int],
       actions: Sequence[int]) -> Q:
    """Mirror of ``euR``: sum over joint actions of prod(sigma_j(a_j)) * u(a, i)."""
    total = Q(0)
    for a in iter_product(actions, repeat=len(players)):
        w = Q(1)
        for j, aj in zip(players, a):
            w *= sigma[j][aj]
        total += w * u(a, i)
    return total


def updated(sigma: Mapping[int, Sequence[Q]], i: int, row: Sequence[Q]) -> Dict[int, List[Q]]:
    """Mirror of ``Function.update``: replace player ``i``'s row."""
    out = dict(sigma)
    out[i] = list(row)
    return out


# ---------------------------------------------------------------------------
# Same-equilibrium relation (IsNashR mirror) + pure-deviation characterization
# ---------------------------------------------------------------------------


def no_pure_dev_gain(u, sigma, players, actions) -> bool:
    """Mirror of the RHS of ``nashR_iff_no_pure_dev_gain``."""
    return all(
        eu(u, updated(sigma, i, point_row(actions, b)), i, players, actions)
        <= eu(u, sigma, i, players, actions)
        for i in players for b in actions
    )


def is_nash(u, sigma, players, actions) -> bool:
    """Mirror of ``IsNashR`` via the pure-deviation characterization."""
    return is_in_simplex(actions, sigma) and no_pure_dev_gain(u, sigma, players, actions)


def best_pure_response(u, sigma, i, players, actions) -> int:
    """Mirror of ``best_response_pure_vertex_exists``: a maximizing pure vertex."""
    values = [
        (eu(u, updated(sigma, i, point_row(actions, b)), i, players, actions), b)
        for b in actions
    ]
    best_value = max(v for v, _ in values)
    for v, b in values:
        if v == best_value:
            return b
    raise AssertionError("unreachable")


def br_profile(u, sigma, players, actions) -> Dict[int, List[Q]]:
    """Kakutani nonemptiness witness: the per-player pure best-response profile."""
    return {
        i: point_row(actions, best_pure_response(u, sigma, i, players, actions))
        for i in players
    }


def in_br_corr(u, base, tau, players, actions) -> bool:
    """Mirror of ``brCorr`` membership: tau rows best-respond to base rows."""
    return is_in_simplex(actions, tau) and all(
        eu(u, updated(base, i, point_row(actions, b)), i, players, actions)
        <= eu(u, updated(base, i, tau[i]), i, players, actions)
        for i in players for b in actions
    )


def fixed_point_is_nash(u, sigma, players, actions) -> bool:
    """Mirror of ``fixed_point_brCorr_iff_nash``: sigma in brCorr sigma iff Nash."""
    a = in_br_corr(u, sigma, sigma, players, actions)
    b = is_nash(u, sigma, players, actions)
    return a == b


# ---------------------------------------------------------------------------
# Affinity / linearity identities (Kakutani convex-value engine)
# ---------------------------------------------------------------------------


def eu_dev_linear_identity(u, sigma, i, row, players, actions) -> bool:
    """Mirror of ``euR_dev_linear``: eu(update row) = weighted eu of pure rows."""
    if not is_row_simplex(row):
        return False
    lhs = eu(u, updated(sigma, i, row), i, players, actions)
    rhs = sum(
        (row[b] * eu(u, updated(sigma, i, point_row(actions, b)), i, players, actions)
         for b in actions),
        Q(0),
    )
    return lhs == rhs


def eu_row_affine_identity(u, sigma, i, r1, r2, a: Q, b: Q, players, actions) -> bool:
    """Mirror of ``euR_update_row_affine``: eu is affine in the replaced row."""
    combo = [a * x + b * y for x, y in zip(r1, r2)]
    lhs = eu(u, updated(sigma, i, combo), i, players, actions)
    rhs = (a * eu(u, updated(sigma, i, r1), i, players, actions)
           + b * eu(u, updated(sigma, i, r2), i, players, actions))
    return lhs == rhs


# ---------------------------------------------------------------------------
# Legal action menu (LegalEval / LegalActionMenu mirror)
# ---------------------------------------------------------------------------


def legal_eval_to_q(ev: Tuple[str, Q]) -> Q:
    """Mirror of ``LegalEval.toQ``: lawful v -> v, sanction c -> -c."""
    tag, value = ev
    if tag == "lawful":
        return value
    if tag == "sanction":
        return -value
    raise ValueError(f"unknown legal evaluation tag: {tag}")


def menu_payoff(menu: Mapping[Tuple[Tuple[int, ...], int], Tuple[str, Q]],
                players: Sequence[int], actions: Sequence[int]):
    """Mirror of ``LegalActionMenu.uReal``: the rational payoff table of a menu."""
    table: Dict[Tuple[int, ...], Dict[int, Q]] = {}
    for a in iter_product(actions, repeat=len(players)):
        table[a] = {i: legal_eval_to_q(menu[(a, i)]) for i in players}
    return table


def table_u(table):
    """Curried table access shaped like the Lean ``u : profile -> player``."""
    return lambda a, i: table[a][i]


# ---------------------------------------------------------------------------
# Upstream bridge mirrors (toRow / pmfOfRow)
# ---------------------------------------------------------------------------


def to_row(pmf_row: Mapping[int, Q], actions: Sequence[int]) -> List[Q]:
    """Mirror of ``toRow`` on a single row: PMF weights as reals (kept Q here)."""
    return [pmf_row[a] for a in actions]


def pmf_of_row(row: Sequence[Q], actions: Sequence[int]) -> Optional[Dict[int, Q]]:
    """Mirror of ``pmfOfRow``: real simplex row -> PMF weights (roundtrip source)."""
    if len(row) != len(actions):
        return None
    if not (all(x >= 0 for x in row) and sum(row, Q(0)) == 1):
        return None
    return {a: row[k] for k, a in enumerate(actions)}


# ---------------------------------------------------------------------------
# CAD side: variable table, polynomial system, formula evaluation
# ---------------------------------------------------------------------------


def cad_var_n(players: Sequence[int], actions: Sequence[int]) -> int:
    """Mirror of ``cadVarN``: card (players x actions)."""
    return len(players) * len(actions)


def cad_idx(players: Sequence[int], actions: Sequence[int]) -> Dict[Tuple[int, int], int]:
    """Mirror of ``cadIdx``: (i, a) -> table position (first-occurrence order)."""
    return {
        (i, a): k
        for k, (i, a) in enumerate((i, a) for i in players for a in actions)
    }


def row_of(players: Sequence[int], actions: Sequence[int],
           rho: Mapping[int, Q]) -> Dict[int, List[Q]]:
    """Mirror of ``rowOf``: assignment -> profile."""
    idx = cad_idx(players, actions)
    return {i: [rho[idx[(i, a)]] for a in actions] for i in players}


def rho_of(players: Sequence[int], actions: Sequence[int],
           sigma: Mapping[int, Sequence[Q]]) -> Dict[int, Q]:
    """Mirror of ``exists_rowOf_eq``: profile -> assignment."""
    idx = cad_idx(players, actions)
    return {idx[(i, a)]: sigma[i][a] for i in players for a in actions}


def eu_poly_value(u, rho, i, players, actions) -> Q:
    """Mirror of ``euPoly`` evaluation: sum_a prod_j x_{(j,a_j)} * u(a,i)."""
    idx = cad_idx(players, actions)
    total = Q(0)
    for a in iter_product(actions, repeat=len(players)):
        w = Q(1)
        for j, aj in zip(players, a):
            w *= rho[idx[(j, aj)]]
        total += w * u(a, i)
    return total


def eu_dev_poly_value(u, rho, i, b, players, actions) -> Q:
    """Mirror of ``euDevPoly`` evaluation: pure-deviation expected utility."""
    idx = cad_idx(players, actions)
    total = Q(0)
    for a in iter_product(actions, repeat=len(players)):
        w = Q(1)
        for j, aj in zip(players, a):
            w *= Q(1) if (j == i and aj == b) else (Q(0) if j == i else rho[idx[(j, aj)]])
        total += w * u(a, i)
    return total


def cad_atom_list(u, players, actions) -> List[Tuple[str, object]]:
    """Mirror of ``cadAtomList``: (op, payload) atoms of the section-8.2 system.

    ops: "nonneg" (payload (i,a)); "norm" (payload i); "dev" (payload (i,b)).
    """
    atoms: List[Tuple[str, object]] = []
    for i in players:
        for a in actions:
            atoms.append(("nonneg", (i, a)))
    for i in players:
        atoms.append(("norm", i))
    for i in players:
        for b in actions:
            atoms.append(("dev", (i, b)))
    return atoms


def cad_formula_denote(u, rho, players, actions) -> bool:
    """Mirror of ``cadEquilFormula.denote`` (conjAll over ``cadAtomList``)."""
    for op, payload in cad_atom_list(u, players, actions):
        if op == "nonneg":
            i, a = payload
            if not rho[cad_idx(players, actions)[(i, a)]] >= 0:
                return False
        elif op == "norm":
            i = payload
            idx = cad_idx(players, actions)
            if sum((rho[idx[(i, a)]] for a in actions), Q(0)) != 1:
                return False
        else:
            i, b = payload
            if not eu_dev_poly_value(u, rho, i, b, players, actions) <= \
                    eu_poly_value(u, rho, i, players, actions):
                return False
    return True


def cad_same_equilibrium_relation(u, rho, players, actions) -> bool:
    """Pointwise mirror of ``cad_output_same_equilibrium_relation``:
    formula denote(rho) iff rowOf(rho) is a simplex Nash profile."""
    lhs = cad_formula_denote(u, rho, players, actions)
    sigma = row_of(players, actions, rho)
    rhs = is_nash(u, sigma, players, actions)
    return lhs == rhs


# ---------------------------------------------------------------------------
# Reference equilibrium generator: exact two-player support enumeration
# ---------------------------------------------------------------------------


def _solve_linear(rows: List[List[Q]], rhs: List[Q]) -> Optional[List[Q]]:
    """Fraction Gaussian elimination on an n x n system; None if singular."""
    n = len(rhs)
    m = [list(r) + [v] for r, v in zip(rows, rhs)]
    for col in range(n):
        piv = next((r for r in range(col, n) if m[r][col] != 0), None)
        if piv is None:
            return None
        m[col], m[piv] = m[piv], m[col]
        pv = m[col][col]
        m[col] = [x / pv for x in m[col]]
        for r in range(n):
            if r != col and m[r][col] != 0:
                f = m[r][col]
                m[r] = [x - f * y for x, y in zip(m[r], m[col])]
    return [m[r][n] for r in range(n)]


def find_all_equilibria_2p(u, actions) -> List[Tuple[List[Q], List[Q]]]:
    """Exact two-player mixed-equilibrium enumeration by support pairs.

    For each nonempty support pair (S0, S1): equalization within supports
    (linear system over the opponent's row) + support membership + nonneg
    off-support deviation checks.  Deduplicated.  This is the reference
    generator whose output the independent checker re-verifies.
    """
    players = [0, 1]
    A = list(actions)
    results: List[Tuple[List[Q], List[Q]]] = []
    seen = set()
    for k0 in range(1, len(A) + 1):
        for s0 in _supports(A, k0):
            for k1 in range(1, len(A) + 1):
                for s1 in _supports(A, k1):
                    sol = _solve_support_system(u, s0, s1)
                    if sol is None:
                        continue
                    for x, y in sol:
                        sigma = {0: _embed(x, s0, A), 1: _embed(y, s1, A)}
                        if not is_in_simplex(A, sigma):
                            continue
                        if no_pure_dev_gain(u, sigma, players, A):
                            key = (tuple(sigma[0]), tuple(sigma[1]))
                            if key not in seen:
                                seen.add(key)
                                results.append((sigma[0], sigma[1]))
    return results


def _supports(A: Sequence[int], k: int):
    from itertools import combinations
    return list(combinations(A, k))


def _embed(x: Sequence[Q], support: Sequence[int], A: Sequence[int]) -> List[Q]:
    row = [Q(0)] * len(A)
    pos = {a: k for k, a in enumerate(A)}
    for a, v in zip(support, x):
        row[pos[a]] = v
    return row


def _solve_support_system(u, s0, s1):
    """Solve the equalization system for supports (s0, s1) exactly.

    Equations: |s0|-1 indifference conditions for player 0 over s0 (in y),
    |s1|-1 for player 1 over s1 (in x), plus the two normalizations —
    exactly |s0| + |s1| square.  Returns [(x, y), ...] candidate rows.
    """
    n0, n1 = len(s0), len(s1)
    rows: List[List[Q]] = []
    rhs: List[Q] = []
    for a, a2 in zip(s0, s0[1:]):
        rows.append([u((a, b), 0) - u((a2, b), 0) for b in s1] + [Q(0)] * n0)
        rhs.append(Q(0))
    for b, b2 in zip(s1, s1[1:]):
        rows.append([Q(0)] * n1 + [u((a, b), 1) - u((a, b2), 1) for a in s0])
        rhs.append(Q(0))
    rows.append([Q(1)] * n1 + [Q(0)] * n0)
    rhs.append(Q(1))
    rows.append([Q(0)] * n1 + [Q(1)] * n0)
    rhs.append(Q(1))
    sol = _solve_linear(rows, rhs)
    if sol is None:
        return None
    if not _consistent(rows, rhs, sol):
        return None
    y, x = list(sol[:n1]), list(sol[n1:])
    return [(x, y)]


def _consistent(rows, rhs, sol) -> bool:
    return all(
        sum((c * v for c, v in zip(r, sol)), Q(0)) == v for r, v in zip(rows, rhs)
    )
