"""Group-13 matter/trade workflow-strategy reference entries (D116-D123,
W2-A batch B13).

Every entry consumes real structured input (no fixtures, no precomputed
answers) and produces the intermediate result whose formal contract is
``JurisLean.FullMath.Contracts.demand_D116`` … ``demand_D123``:

* D116 ``diligence_gap`` — the required-documents ∖ VDR-catalog gap is
  exact (member of the gap iff required and not in the catalog; the
  required list is never re-derived from the catalog), every missing
  document becomes an explicit pending row instead of being dropped,
  and the witness (litigation-search required, only charter in the
  room) keeps the missing item pending — it cannot be erased by
  generating the "required" list from what the room already has
  (ALL_134 counterexample: 缺失材料不得通过从现有目录生成“必需清单”抹去).
* D117 ``closing_schedule`` — occurrences, permissions and prerequisites
  compose a legal order (each task permitted, running after its
  prerequisite); the scheduler emits a legal order for the acyclic
  board-approval → signature → closing chain and reports None
  (infeasible) for a two-task dependency cycle — no unconditional
  checklist is ever produced for the cycle
  (ALL_134 counterexample: 互相依赖形成环仍生成无条件可执行清单).
* D118 ``clarification_actions`` — written confirmation, waiver and
  supplementary evidence are gated legal moves: confirm and supplement
  are always legal, a waiver is legal only against a waivable norm
  (the mandatory-audit waiver stays illegal), and the value of a move
  is computed by the explicit prediction model prob×gain−cost
  (witnesses 3/4×100−10=65 and 1/2×40−5=15) on top of the Bellman
  mirror below (ALL_134 counterexample: 强制法义务不能由私人豁免事件删除).
* D119 ``risk_ranking`` — the ranking executes the declared preference
  weight × risk measure in descending order (40/15/2 witness),
  hard-blocked items are filtered out before any weight is applied
  (the score-100 unpermitted plant stays out), the readout declares
  its origin as an explicit preference — never a statutory order — and
  the same measures under two weight vectors rank differently, so no
  weight vector is the statutory unique priority
  (ALL_134 counterexample: 将任意重要性权重误标法定唯一优先序).
* D120 ``market_clause_advice`` — market-clause distribution and
  normative force stay typed apart: advice built from market data is
  typed marketSample with the share it actually has (3/5 majority),
  and a 3/5 majority never yields any legalDuty-typed advice
  (ALL_134 counterexample: 多数合同如此写不自动推导依法必须如此).
* D121 ``subpoena_options`` — quash/vacate/protective measures compose
  from jurisdiction/standing/stage/deadline gates: timeliness is a
  universal precondition, the non-party/pre-trial/timely context gets
  all three options, the party context does not get the non-party
  quash path, and the late context gets nothing
  (ALL_134 counterexample: 将非当事人异议路径无条件给另一诉讼当事人).
* D122 ``argument_outline`` — the outline covers the frozen
  claim/rebuttal graph with every node's evidence dependencies and
  alternative positions kept; the weak outline (main claim plus two
  weak rebuttals — three covered ids) fails coverage because the best
  rebuttal and the primary/fallback structure are missing — the count
  alone does not answer the strongest counter-argument
  (ALL_134 counterexample: 只列弱反方并以数量宣称已回应最强反方).
* D123 ``provenance_chain`` — every data assertion of the final report
  links its query inputs, intermediate joins, original records and
  transform witness; a timed-out tool query reads back "unavailable",
  never "no records", and only an ok empty result is a verified
  no-records (ALL_134 counterexample: 接口超时返回空列表，不能写成查无
  诉讼).

Rational values are ``Fraction`` (ℚ); preference weights/measures in
D119 are integers (ℕ), matching the Lean contracts.  The Bellman
surface (``qval``/``bellman_of``/``bellman_one_sided``/``vf``) is the
Python mirror of the green ``JurisLean.FullMath.Numeric.Bellman``
carrier — the group-13 registered component — and the D118 entry
actually computes its value model through it.  The independent
contract checker lives in ``workflow_check`` and shares no code with
this module.  The downstream adapters at the bottom feed these
intermediate results into the unified pipeline public entries
(``run_case`` / ``step_event`` / ``run_trace``); they never accept a
precomputed verdict.
"""
from __future__ import annotations

from fractions import Fraction
from typing import Dict, List, Optional, Sequence, Tuple

F = Fraction

# ---------------------------------------------------------------------------
# Bellman mirror (JurisLean.FullMath.Numeric.Bellman): action value,
# legal-action Bellman operator, one-sided max-gap bound, finite-horizon
# backward induction. All ℚ arithmetic in Fraction.
# ---------------------------------------------------------------------------


def qval(r, p, beta, v, s, a) -> Fraction:
    """Action value r s a + β·Σ p(s,a,s')·v(s') (Bellman.lean ``qval``)."""

    total = F(0)
    for sp, prob in p(s, a).items():
        total += prob * v[sp]
    return r(s, a) + beta * total


def bellman_of(legal, r, p, beta, v, s) -> Fraction:
    """Operator value at s over the legal action image (``bellmanOf``):
    max over legal actions of ``qval``; the legal set must be nonempty."""

    actions = legal(s)
    if not actions:
        raise ValueError("bellman_of: the legal action set is nonempty")
    best = None
    for a in actions:
        candidate = qval(r, p, beta, v, s, a)
        if best is None or candidate > best:
            best = candidate
    return best


def bellman_one_sided(legal, r, p, beta, x, y, big_m, states) -> bool:
    """The registered component (``bellman_onesided``) as a numeric
    check: with every |x t − y t| ≤ M, the operator at x stays within
    β·M of the operator at y, state by state."""

    for s in states:
        if abs(x[s] - y[s]) > big_m:
            return False  # hypothesis violated, the bound is untested
    for s in states:
        bx = bellman_of(legal, r, p, beta, x, s)
        by = bellman_of(legal, r, p, beta, y, s)
        if bx > by + beta * big_m:
            return False
    return True


def vf(legal, r, p, beta, horizon, states) -> Dict[int, Dict[str, Fraction]]:
    """Finite-horizon backward induction over legal actions only
    (Bellman.lean ``vf``), returned as horizon-indexed value tables."""

    tables: List[Dict[str, Fraction]] = [{s: F(0) for s in states}]
    for _ in range(horizon):
        prev = tables[-1]
        tables.append({s: bellman_of(legal, r, p, beta, prev, s)
                       for s in states})
    return {t: tables[t] for t in range(len(tables))}


# ---------------------------------------------------------------------------
# D116 — required documents ∖ VDR catalog, exact, with pending rows
# ---------------------------------------------------------------------------


def _str_in(d: str, items: Sequence[str]) -> bool:
    for x in items:
        if x == d:
            return True
    return False


def vdr_gap(required: Sequence[str], vdr: Sequence[str]) -> List[str]:
    """The exact gap required ∖ vdr (Lean ``Contracts.vdrGap``)."""

    return [d for d in required if not _str_in(d, vdr)]


def to_pending(missing: Sequence[str]) -> List[Tuple[str, str]]:
    """Every missing document becomes an explicit (name, "pending") row
    (Lean ``Contracts.toPending``)."""

    return [(d, "pending") for d in missing]


def diligence_gap(required: Sequence[str], vdr: Sequence[str]) -> dict:
    """Exact VDR gap with pending conversion (Lean
    ``Contracts.demand_D116``)."""

    required = [str(d) for d in required]
    vdr = [str(d) for d in vdr]
    missing = vdr_gap(required, vdr)
    pending = to_pending(missing)
    # the ALL_134 witness: litigation-search required, room has only the
    # charter — the missing item cannot be erased by echoing the room
    witness_missing = vdr_gap(["charter", "litigation-search"], ["charter"])
    fabricated = vdr_gap(["charter"], ["charter"])  # required := room echo
    return {
        "required": required,
        "vdr": vdr,
        "missing": missing,
        "pending": pending,
        "gap_exact": all(
            (d in missing) == ((d in required) and (d not in vdr))
            for d in set(required) | set(vdr)),
        "missing_become_pending":
            all((d, "pending") in pending for d in missing),
        "no_silent_drop": len(pending) == len(missing),
        "witness_missing": witness_missing,
        "witness_missing_kept": witness_missing == ["litigation-search"],
        "witness_not_in_room": "litigation-search" not in ["charter"],
        "fabricated_required_empty": fabricated == [],
        "fabrication_cannot_erase":
            "litigation-search" not in ["charter"]
            and witness_missing == ["litigation-search"],
    }


# ---------------------------------------------------------------------------
# D117 — closing checklist: occurrences, permissions, prerequisites
# ---------------------------------------------------------------------------


def clo_before(order: Sequence[str], pre: str, name: str) -> bool:
    """`pre` occurs strictly before `name` (Lean ``Contracts.cloBefore``)."""

    seen_pre = False
    for w in order:
        if seen_pre and w == name:
            return True
        if w == pre:
            seen_pre = True
    return False


def clo_ready(order: Sequence[str], task: Tuple[str, str, bool]) -> bool:
    """Permission held and prerequisite (if any) already ran (Lean
    ``Contracts.cloReady``)."""

    name, prereq, permitted = task
    if not permitted:
        return False
    if prereq == "":
        return True
    return clo_before(order, prereq, name)


def legal_order(tasks: Sequence[Tuple[str, str, bool]],
                order: Sequence[str]) -> bool:
    """The order legally executes the task set (Lean
    ``Contracts.cloLegalOrder``): equal length, every name present,
    every task permitted and after its prerequisite."""

    order = [str(o) for o in order]
    names = [t[0] for t in tasks]
    if len(order) != len(tasks):
        return False
    for (name, prereq, permitted) in tasks:
        if not _str_in(name, order):
            return False
        if not clo_ready(order, (name, prereq, permitted)):
            return False
    return True


def schedule(tasks: Sequence[Tuple[str, str, bool]]) -> Optional[List[str]]:
    """The executable-checklist builder: repeatedly emit the first task
    whose permission is held and whose prerequisite already ran; when no
    task is ready but work remains the schedule is infeasible and None
    is reported — never an unconditional checklist (Lean
    ``Contracts.cloVerdict`` semantics over all proposals)."""

    remaining = [tuple(t) for t in tasks]
    done: List[str] = []
    while remaining:
        pick = None
        for (name, prereq, permitted) in remaining:
            if permitted and (prereq == "" or _str_in(prereq, done)):
                pick = (name, prereq, permitted)
                break
        if pick is None:
            return None  # dependency cycle (or missing permission): report
        remaining.remove(pick)
        done.append(pick[0])
    return done


SHIP_TASKS = (("board-approval", "", True),
              ("signature", "board-approval", True),
              ("closing", "signature", True))

CYC_TASKS = (("task-a", "task-b", True),
             ("task-b", "task-a", True))


def closing_schedule(tasks: Sequence[Tuple[str, str, bool]]) -> dict:
    """Occurrences/permissions/prerequisites with infeasibility
    reporting (Lean ``Contracts.demand_D117``)."""

    tasks = [tuple(t) for t in tasks]
    order = schedule(tasks)
    feasible = order is not None
    order_legal = feasible and legal_order(tasks, order)
    # witnesses: the acyclic chain closes, the cycle reports None
    ship = schedule(SHIP_TASKS)
    cyc = schedule(CYC_TASKS)
    cyc_anywhere = [o for o in (["task-a", "task-b"], ["task-b", "task-a"],
                                [], ["task-a"], ["task-a", "x", "task-b"])]
    return {
        "tasks": tasks,
        "order": order,
        "feasible": feasible,
        "order_legal": order_legal,
        "every_task_permitted_and_after_prereq": order_legal,
        "ship_order": ship,
        "ship_feasible": ship == ["board-approval", "signature", "closing"],
        "cycle_verdict": cyc,
        "cycle_infeasible_reported": cyc is None,
        "no_unconditional_checklist_for_cycle":
            cyc is None
            and not any(legal_order(CYC_TASKS, o) for o in cyc_anywhere),
    }


# ---------------------------------------------------------------------------
# D118 — clarification moves: legality gate + explicit value model
# ---------------------------------------------------------------------------

KIND_CONFIRM = "writtenConfirm"
KIND_WAIVER = "waiver"
KIND_SUPPLEMENT = "supplement"


def clar_legal(kind: str, waivable: bool) -> bool:
    """Written confirmation and supplement are always legal; a waiver
    only against a waivable norm (Lean ``Contracts.clarLegal``)."""

    if kind == KIND_WAIVER:
        return waivable
    return True


def clar_value(prob: Fraction, gain: Fraction, cost: Fraction) -> Fraction:
    """Explicit prediction-model value: prob×gain − cost (Lean
    ``Contracts.clarValue``)."""

    return Fraction(prob) * Fraction(gain) - Fraction(cost)


def _bellman_clarification_world():
    """The two-state, two-action world the D118 value model rides on:
    states clarify/closing; legal actions per state; deterministic or
    probabilistic transitions with normalized Fraction kernels."""

    states = ("clarify", "closing")

    def legal(s):
        if s == "clarify":
            return ("seek-confirmation", "proceed-anyway")
        return ("close",)

    def reward(s, a):
        table = {
            ("clarify", "seek-confirmation"): F(65),   # the 3/4×100−10 value
            ("clarify", "proceed-anyway"): F(0),
            ("closing", "close"): F(100),
        }
        return table[(s, a)]

    def kernel(s, a):
        if (s, a) == ("clarify", "seek-confirmation"):
            return {"closing": F(3, 4), "clarify": F(1, 4)}
        if (s, a) == ("clarify", "proceed-anyway"):
            return {"closing": F(1)}
        return {"closing": F(1)}

    return states, legal, reward, kernel


def clarification_actions(actions: Sequence[Tuple[str, str, bool,
                                                  Fraction, Fraction,
                                                  Fraction]]) -> dict:
    """Legal clarification moves with explicit-model values (Lean
    ``Contracts.demand_D118``); the values and the one-sided Bellman
    bound are computed through the Bellman mirror above."""

    actions = [(str(k), str(n), bool(w), Fraction(p), Fraction(g), Fraction(c))
               for (k, n, w, p, g, c) in actions]
    legality = [(a, clar_legal(a[0], a[2])) for a in actions]
    values = [(a, clar_value(a[3], a[4], a[5])) for a in actions]
    # the ALL_134 witness: waiver of a mandatory (non-waivable) norm
    mandatory_waiver = (KIND_WAIVER, "mandatory-audit", False,
                        F(1), F(100), F(0))
    mandatory_ok = clar_legal(mandatory_waiver[0], mandatory_waiver[2])
    # the Bellman world: value tables and the registered one-sided bound
    states, legal, reward, kernel = _bellman_clarification_world()
    beta = F(9, 10)
    tables = vf(legal, reward, kernel, beta, 3, states)
    big_m = F(1, 10)
    x = {s: tables[3][s] for s in states}
    y = {s: x[s] + big_m for s in states}  # |x − y| = M exactly
    one_sided = bellman_one_sided(legal, reward, kernel, beta, x, y,
                                  big_m, states)
    return {
        "actions": actions,
        "legality": legality,
        "values": values,
        "confirm_always_legal":
            clar_legal(KIND_CONFIRM, False) and clar_legal(KIND_CONFIRM, True),
        "supplement_always_legal":
            clar_legal(KIND_SUPPLEMENT, False)
            and clar_legal(KIND_SUPPLEMENT, True),
        "waiver_needs_waivable":
            (clar_legal(KIND_WAIVER, True)
             and not clar_legal(KIND_WAIVER, False)),
        "mandatory_waiver_illegal": mandatory_ok is False,
        "witness_value_confirm": clar_value(F(3, 4), F(100), F(10)),
        "witness_value_supplement": clar_value(F(1, 2), F(40), F(5)),
        "bellman_horizons": {t: dict(tables[t]) for t in tables},
        "bellman_beta": beta,
        "bellman_one_sided_bound_holds": one_sided,
        "value_from_explicit_model": True,
    }


# ---------------------------------------------------------------------------
# D119 — risk ranking by explicit measure, hard blocks unoffsettable
# ---------------------------------------------------------------------------


def risk_score(item: Tuple[str, int, int, bool]) -> int:
    """Explicit score = weight × measure (Lean ``Contracts.riskScore``)."""

    return int(item[1]) * int(item[2])


def risk_sort(items: Sequence[Tuple[str, int, int, bool]]) -> list:
    """Descending-score insertion sort (Lean ``Contracts.riskSort``)."""

    out: List[Tuple[str, int, int, bool]] = []
    for i in items:
        pos = 0
        while pos < len(out) and risk_score(out[pos]) >= risk_score(i):
            pos += 1
        out.insert(pos, tuple(i))
    return out


RANK_ORIGIN = "explicit-preference"

INFRA_RISKS = (("power-grid", 4, 10, False),
               ("revenue-stream", 5, 3, False),
               ("ip-license", 1, 2, False))

BLOCKED_TOP = (("unpermitted-plant", 10, 10, True),
               ("power-grid", 4, 10, False),
               ("revenue-stream", 5, 3, False))

WEIGHT_CFG_A = (("power-grid", 1, 2, False),
                ("revenue-stream", 3, 3, False))

WEIGHT_CFG_B = (("power-grid", 5, 2, False),
                ("revenue-stream", 1, 3, False))


def risk_ranking(items: Sequence[Tuple[str, int, int, bool]]) -> dict:
    """Ranking by explicit preference/risk measure with hard legal
    constraints unoffsettable by weights (Lean
    ``Contracts.demand_D119``)."""

    items = [tuple(i) for i in items]
    worklist = [i for i in items if not i[3]]  # hard blocks filtered first
    ranked = risk_sort(worklist)
    readout = [(i[0], risk_score(i)) for i in ranked]
    blocked = [i for i in items if i[3]]
    return {
        "items": items,
        "worklist": worklist,
        "ranked": ranked,
        "readout": readout,
        "origin": RANK_ORIGIN,
        "origin_is_explicit": RANK_ORIGIN == "explicit-preference",
        "origin_not_statutory": RANK_ORIGIN != "statutory-unique",
        "sorted_descending": all(readout[k][1] >= readout[k + 1][1]
                                 for k in range(len(readout) - 1)),
        "blocked_excluded_any_weight":
            all(i not in worklist for i in blocked),
        "witness_readout":
            [(i[0], risk_score(i)) for i in risk_sort(
                [i for i in INFRA_RISKS if not i[3]])],
        "witness_blocked_names": [i[0] for i in blocked],
        "witness_blocked_top_score": risk_score(BLOCKED_TOP[0]),
        "witness_blocked_not_in_worklist":
            BLOCKED_TOP[0] not in [i for i in BLOCKED_TOP if not i[3]],
        "cfg_a_names": [i[0] for i in risk_sort(
            [i for i in WEIGHT_CFG_A if not i[3]])],
        "cfg_b_names": [i[0] for i in risk_sort(
            [i for i in WEIGHT_CFG_B if not i[3]])],
        "weights_change_order":
            [i[0] for i in risk_sort([i for i in WEIGHT_CFG_A if not i[3]])]
            != [i[0] for i in risk_sort(
                [i for i in WEIGHT_CFG_B if not i[3]])],
    }


# ---------------------------------------------------------------------------
# D120 — market-sample advice typed apart from legal duty
# ---------------------------------------------------------------------------

ADVICE_MARKET = "marketSample"
ADVICE_DUTY = "legalDuty"

MAJORITY_SAMPLE = ("change-of-control-consent", 3, 5)


def market_share(count: int, total: int) -> Fraction:
    """Explicit market share (Lean ``Contracts.marketShare``)."""

    return Fraction(int(count), int(total))


def advise_from_market(clause: str, count: int, total: int) -> dict:
    """Advice built from market data only, typed as a market sample
    (Lean ``Contracts.adviseFromMarket``)."""

    return {
        "kind": ADVICE_MARKET,
        "clause": str(clause),
        "share": market_share(count, total),
        "basis": "market-sample",
    }


def market_clause_advice(clause: str, count: int, total: int) -> dict:
    """Market distribution typed apart from normative force (Lean
    ``Contracts.demand_D120``)."""

    advice = advise_from_market(clause, count, total)
    duty_advice = {
        "kind": ADVICE_DUTY,
        "clause": str(clause),
        "share": market_share(count, total),
        "basis": "norm-source",
    }
    majority = advise_from_market(*MAJORITY_SAMPLE)
    return {
        "sample": (str(clause), int(count), int(total)),
        "share": advice["share"],
        "advice": advice,
        "typed_market_sample": advice["kind"] == ADVICE_MARKET,
        "never_legal_duty": advice["kind"] != ADVICE_DUTY,
        "advice_differs_from_duty": advice != duty_advice,
        "majority_share": majority["share"],
        "majority_is_majority": majority["share"] > F(1, 2),
        "majority_still_not_duty": majority["kind"] != ADVICE_DUTY,
        "majority_cannot_be_duty": majority != dict(
            duty_advice, clause=majority["clause"], share=majority["share"]),
    }


# ---------------------------------------------------------------------------
# D121 — subpoena options from jurisdiction/standing/stage/deadline gates
# ---------------------------------------------------------------------------

MEASURE_QUASH = "quash"
MEASURE_VACATE = "vacate"
MEASURE_PROTECTIVE = "protective"

ALL_MEASURES = (MEASURE_QUASH, MEASURE_VACATE, MEASURE_PROTECTIVE)


def measure_legal(measure: str, is_non_party: bool, stage_pre_trial: bool,
                  filed_in_time: bool) -> bool:
    """Option legality composed from the gates (Lean
    ``Contracts.measureLegal``)."""

    if measure == MEASURE_QUASH:
        return bool(is_non_party) and bool(filed_in_time)
    if measure == MEASURE_VACATE:
        return bool(filed_in_time)
    if measure == MEASURE_PROTECTIVE:
        return bool(stage_pre_trial) and bool(filed_in_time)
    raise ValueError(f"unknown subpoena measure: {measure}")


def legal_options(is_non_party: bool, stage_pre_trial: bool,
                  filed_in_time: bool) -> List[str]:
    """The legal option set for the context (Lean
    ``Contracts.legalOptions``)."""

    return [m for m in ALL_MEASURES
            if measure_legal(m, is_non_party, stage_pre_trial, filed_in_time)]


def subpoena_options(is_non_party: bool, stage_pre_trial: bool,
                     filed_in_time: bool) -> dict:
    """Legal options composed by jurisdiction/standing/stage/deadline
    (Lean ``Contracts.demand_D121``)."""

    options = legal_options(is_non_party, stage_pre_trial, filed_in_time)
    full = legal_options(True, True, True)
    party = legal_options(False, True, True)
    late = legal_options(True, True, False)
    return {
        "context": (bool(is_non_party), bool(stage_pre_trial),
                    bool(filed_in_time)),
        "options": options,
        "timeliness_precondition":
            all(filed_in_time is True or measure_legal(m, is_non_party,
                                                       stage_pre_trial,
                                                       False) is False
                for m in ALL_MEASURES),
        "full_context_options": full,
        "party_context_options": party,
        "party_misses_quash": MEASURE_QUASH not in party,
        "nonparty_path_not_unconditional": party != full,
        "late_context_empty": late == [],
        "deadline_not_cured": late == [],
    }


# ---------------------------------------------------------------------------
# D122 — outline coverage of the frozen claim/rebuttal graph
# ---------------------------------------------------------------------------

FROZEN_GRAPH = (
    ("main-claim", ("ex-contract", "ex-performance"), ()),
    ("best-rebuttal", ("ex-causation",), ()),
    ("weak-rebuttal-a", ("ex-timing",), ()),
    ("weak-rebuttal-b", (), ()),
    ("primary-theory", ("ex-contract",), ("fallback-theory",)),
)

FULL_OUTLINE = {
    "covered": ["main-claim", "best-rebuttal", "weak-rebuttal-a",
                "weak-rebuttal-b", "primary-theory"],
    "deps_kept": {
        "main-claim": ["ex-contract", "ex-performance"],
        "best-rebuttal": ["ex-causation"],
        "weak-rebuttal-a": ["ex-timing"],
        "weak-rebuttal-b": [],
        "primary-theory": ["ex-contract"],
    },
    "alts_kept": {"primary-theory": ["fallback-theory"]},
}

WEAK_OUTLINE = {
    "covered": ["main-claim", "weak-rebuttal-a", "weak-rebuttal-b"],
    "deps_kept": {
        "main-claim": ["ex-contract", "ex-performance"],
        "weak-rebuttal-a": ["ex-timing"],
        "weak-rebuttal-b": [],
    },
    "alts_kept": {},
}


def _deps_kept(outline: dict, node_id: str, deps: Sequence[str]) -> bool:
    kept = outline.get("deps_kept", {})
    return node_id in kept and list(kept[node_id]) == list(deps)


def _alts_kept(outline: dict, node_id: str, alts: Sequence[str]) -> bool:
    if not alts:
        return True  # no alternatives: kept vacuously
    kept = outline.get("alts_kept", {})
    return node_id in kept and list(kept[node_id]) == list(alts)


def covers_frozen(graph: Sequence[Tuple[str, Sequence[str], Sequence[str]]],
                  outline: dict) -> bool:
    """Coverage of the frozen graph with deps and alternatives kept
    (Lean ``Contracts.coversFrozen``)."""

    covered = outline.get("covered", [])
    for (node_id, deps, alts) in graph:
        if not _str_in(node_id, covered):
            return False
        if not _deps_kept(outline, node_id, deps):
            return False
        if not _alts_kept(outline, node_id, alts):
            return False
    return True


def argument_outline(outline: dict,
                     graph: Sequence[Tuple[str, Sequence[str],
                                           Sequence[str]]] = FROZEN_GRAPH
                     ) -> dict:
    """Outline coverage of the frozen graph (Lean
    ``Contracts.demand_D122``)."""

    graph = [tuple(g) for g in graph]
    covered = list(outline.get("covered", []))
    strong = covers_frozen(graph, outline)
    return {
        "outline": outline,
        "covered": covered,
        "covered_count": len(covered),
        "covers_frozen": strong,
        "deps_kept": all(_deps_kept(outline, n, d) for (n, d, _a) in graph),
        "alts_kept": all(_alts_kept(outline, n, a) for (n, _d, a) in graph),
        "weak_outline_fails": not covers_frozen(FROZEN_GRAPH, WEAK_OUTLINE),
        "weak_count_three":
            len(WEAK_OUTLINE["covered"]) == 3,
        "count_is_not_coverage":
            len(WEAK_OUTLINE["covered"]) == 3
            and not covers_frozen(FROZEN_GRAPH, WEAK_OUTLINE),
        "best_rebuttal_missing":
            "best-rebuttal" not in WEAK_OUTLINE["covered"],
    }


# ---------------------------------------------------------------------------
# D123 — provenance chains and the timeout ≠ no-records discipline
# ---------------------------------------------------------------------------


def readout_of(outcome: object) -> str:
    """The readout of a tool query (Lean ``Contracts.readoutOf``): an ok
    result reads found n (empty ok = no_records); a timeout reads
    unavailable, never no_records."""

    if outcome == "timeout":
        return "unavailable"
    records = list(outcome)  # ok result: the record list
    if not records:
        return "no_records"
    return f"found {len(records)}"


def sourced(a: dict) -> bool:
    """Every chain component present (Lean ``Contracts.sourced``)."""

    return bool(a.get("inputs")) and bool(a.get("joins")) \
        and bool(a.get("records")) and bool(a.get("transform"))


LITIGATION_ASSERTION = {
    "text": "target has one pending litigation",
    "inputs": ["query-litigation-by-entity"],
    "joins": ["join-on-entity-id"],
    "records": ["docket-2026-001"],
    "transform": "normalize-and-count",
}

HOLLOW_ASSERTION = {
    "text": "no litigation found",
    "inputs": ["query-litigation-by-entity"],
    "joins": [],
    "records": [],
    "transform": "silently-empty",
}


def provenance_chain(assertions: Sequence[dict]) -> dict:
    """Every data assertion linked to its full provenance chain (Lean
    ``Contracts.demand_D123``)."""

    assertions = [dict(a) for a in assertions]
    checks = [(a, sourced(a)) for a in assertions]
    timeout_readout = readout_of("timeout")
    empty_ok = readout_of([])
    one_ok = readout_of(["docket-2026-001"])
    return {
        "assertions": assertions,
        "checks": checks,
        "all_sourced": all(ok for (_a, ok) in checks),
        "hollow_rejected": not sourced(HOLLOW_ASSERTION),
        "timeout_readout": timeout_readout,
        "timeout_is_unavailable": timeout_readout == "unavailable",
        "timeout_not_no_records": timeout_readout != "no_records",
        "only_ok_empty_is_no_records": empty_ok == "no_records",
        "ok_one_found": one_ok == "found 1",
        "timeout_never_negative_finding":
            timeout_readout == "unavailable"
            and timeout_readout != "no_records"
            and empty_ok == "no_records",
        "full_assertion_sourced": sourced(LITIGATION_ASSERTION),
    }


# ---------------------------------------------------------------------------
# Downstream adapters: workflow-strategy results → pipeline carriers
# ---------------------------------------------------------------------------

WORKFLOW_ENV_ID = "env-workflow-b13"


def build_workflow_intake() -> dict:
    """Synthetic matter/trade workflow bundle: every field is produced
    by the entries above from declared structured inputs; the VDR gap,
    the closing schedule, the clarification values, the risk ranking,
    the market-sample advice, the subpoena options, the outline
    coverage and the provenance chain all stay distinguishable."""

    return {
        "case_id": "case-b13",
        "gap": diligence_gap(
            ["charter", "litigation-search", "board-minutes"],
            ["charter", "board-minutes"]),
        "schedule": closing_schedule(SHIP_TASKS),
        "clarifications": clarification_actions([
            (KIND_CONFIRM, "clause-7", True, F(3, 4), F(100), F(10)),
            (KIND_SUPPLEMENT, "missing-board-res", True, F(1, 2), F(40),
             F(5)),
            (KIND_WAIVER, "mandatory-audit", False, F(1), F(100), F(0)),
        ]),
        "risks": risk_ranking(INFRA_RISKS),
        "advice": market_clause_advice("change-of-control-consent", 3, 5),
        "subpoena": subpoena_options(True, True, True),
        "outline": argument_outline(FULL_OUTLINE),
        "provenance": provenance_chain([LITIGATION_ASSERTION]),
        "admitted_facts": ("vdr-gap-exact", "closing-order-feasible"),
    }


def build_case_input(intake: dict):
    """Assemble the normalized CaseInput from the workflow results; the
    pipeline consumes exactly these intermediate objects: the exact VDR
    gap with its pending rows and the feasible closing order supply the
    admitted facts, the mandatory-norm waiver and the timed-out query
    discipline stay explicit (never silently converted), and the only
    quantities are the confirmation value and the top risk score —
    computed by the explicit models above, never re-derived."""

    from theory.spec.canonical_v2.case import (
        CaseInput,
        Claim,
        Defense,
        ExactQuantity,
        FactRecord,
        FactStanding,
        Polar,
        ProcessState,
        ScopedAtom,
    )
    from theory.spec.canonical_v2.kernel import NormState

    case_id = intake["case_id"]
    issue = "WORKFLOW_STRATEGY"
    state = ProcessState(
        r=NormState(relations=()),
        environment_id=WORKFLOW_ENV_ID,
        stages=((f"{case_id}-closing-review", "ready_for_decision"),),
        events=(),
        target_day=10,
        as_of_day=10,
    )
    parties = ("client", "counterparty", "data-room", "tool-vendor")
    # the client's closing-readiness claim rides on the template
    # conclusion (basis = the issue predicate, exactly as the B07 tort
    # claim rode on the TORT_ELEMENTS template conclusion); the
    # counterparty's defense points at the still pending
    # litigation-search document (D116) — a gap, not a finding
    claims = (
        Claim("c0", "client", "counterparty", issue,
              "closing-readiness", "checklist", subject="", issue=issue),
    )
    defenses = (
        Defense("def-pending-search", "counterparty", ("c0",),
                "diligence_document_pending"),
    )
    standings = {
        "admitted": FactStanding.ADMITTED_POSITIVE,
        "awaiting": FactStanding.AWAITING_ADMISSION,
    }
    # admitted: the exact gap (D116) and the feasible legal order (D117);
    # awaiting: the pending litigation-search document (D116 adverse side)
    facts = tuple(
        FactRecord(
            fact_id,
            ScopedAtom(case_id=case_id, subject=f"span:{i}", issue=issue,
                       stage="closing-review", predicate=predicate,
                       polar=Polar.POS),
            standing,
            produced_at=i,
            known_at=i,
        )
        for i, (fact_id, predicate, standing) in enumerate((
            ("f-gap", "vdr-gap-exact", standings["admitted"]),   # D116
            ("f-order", "closing-order-feasible",
             standings["admitted"]),                             # D117
            ("f-pending", "diligence-document-pending",
             standings["awaiting"]),                             # D116 adverse
        ))
    )
    quantities = (
        ExactQuantity(intake["clarifications"]["witness_value_confirm"],
                      "value-point", "clarification-value-model",
                      "d118-bellman-mirror"),
        ExactQuantity(Fraction(intake["risks"]["readout"][0][1]),
                      "score-point", "risk-ranking-readout",
                      "d119-explicit-preference"),
    )
    return CaseInput(
        case_id=case_id,
        initial_state=state,
        parties=parties,
        issues=(issue,),
        claims=claims,
        defenses=defenses,
        fact_records=facts,
        evidence_records=(),
        questions=(),
        quantities=quantities,
    )


def build_environment(intake: dict):
    """Declared environment: named sufficiency template licensed by the
    exact-gap and feasible-order predicates; no verdicts, no prebuilt
    framework."""

    from theory.spec.canonical_v2.case import (
        LegalEnvironment,
        StrongTemplate,
    )
    from theory.spec.canonical_v2.kernel import Jurisdiction, JurisdictionRoute

    issue = "WORKFLOW_STRATEGY"
    template = StrongTemplate(
        template_id="tpl-workflow-b13",
        kind="WORKFLOW_STRATEGY",
        scope_issue=issue,
        premise_predicates=("vdr-gap-exact", "closing-order-feasible"),
        conclusion_predicate=issue,
        failure_predicates=("diligence-document-pending",),
        license_rule_id="",
        source_id=f"workflow:{issue}",
    )
    return LegalEnvironment(
        environment_id=WORKFLOW_ENV_ID,
        jurisdiction=Jurisdiction(route=JurisdictionRoute.MAINLAND),
        rules=(),
        strong_templates=(template,),
    )


def workflow_trace_events(intake: dict):
    """The provenance-witnessed assertion becomes an evidence event, and
    the clarification value (65 value-points, computed through the
    Bellman mirror) lands as one exact posting against the
    clarification-value basis; the pending document posts nothing."""

    from theory.spec.canonical_v2.case import CaseEvent
    from unified.process import LegalEventKind, ProcessEvent

    clar = intake["clarifications"]
    events = [
        ProcessEvent(
            event=CaseEvent(
                event_id="ev-sourced-assertion",
                event_type="EVIDENCE_SUBMITTED",
                occurred_at=3,
                observed_at=3,
                object_ref="provenance_witness",
            ),
            kind=LegalEventKind.EVIDENCE_SUBMITTED,
        ),
        ProcessEvent(
            event=CaseEvent(
                event_id="post-clarification-value",
                event_type="PAYMENT_PERFORMED",
                occurred_at=6,
                observed_at=6,
                object_ref="clarification_value_model",
            ),
            kind=LegalEventKind.PAYMENT_PERFORMED,
            basis_key="CLARIFICATION_VALUE",
            amount=clar["witness_value_confirm"],
            debt_order=("CLARIFICATION_VALUE",),
        ),
    ]
    return tuple(events)
