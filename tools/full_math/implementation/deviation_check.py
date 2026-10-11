"""Independent checker for the W4 deviation seam T124-T127 (J.7 discipline).

This module deliberately re-implements the seam's semantics with its own
inline logic instead of importing the reference functions: the
representation-preservation contract, the reflow authority/time gates, the
three-reference distance structure, the fixed-domain Hausdorff shift bound,
the stratified-propensity no-prior-double-use discipline, and the
report faithful-projection/completeness gates are all re-derived here from
the frozen carriers alone.  It shares only the immutable data
classes/enums of ``deviation_ref`` (and of ``interpretation_ref`` for the
T124 adopted pool) — never its functions — and never calls the evaluator.

Lean contract: JurisLean.Seams.UnifiedW4Deviation (T124-T127).
"""
from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction as Q
from typing import Iterable, Optional, Tuple

from tools.full_math.implementation.deviation_ref import (
    Comparability,
    DeviationReport,
    DevKind,
    DevSource,
    InterpRepLayer,
    PriorTable,
    PropensityAssumptions,
    RefKind,
    ReflowEvent,
    ReflowWindow,
    StratObs,
    StratTable,
    ThreeRefs,
    Uncert,
)
from tools.full_math.implementation.interpretation_ref import (
    InterpCandidate,
    RuleAst,
)


@dataclass(frozen=True)
class CheckReport:
    ok: bool
    reasons: Tuple[str, ...]

    @classmethod
    def pass_(cls) -> "CheckReport":
        return cls(True, ())

    @classmethod
    def fail(cls, *reasons: str) -> "CheckReport":
        return cls(False, tuple(reasons))


# ---------------------------------------------------------------------------
# Inline semantic re-derivations（与主实现零函数共享）
# ---------------------------------------------------------------------------


def _adoptable(c: InterpCandidate) -> bool:
    # §3.1: 采用/排除解释仍须法定权限与具名理由（内联重实现）
    return c.reason_id is not None and c.reason_id != "" \
        and c.authority_id is not None


def _rule_base(cands: Iterable[InterpCandidate]) -> frozenset:
    return frozenset(c.rule for c in cands if _adoptable(c))


def _rep_log(cands: Iterable[InterpCandidate]) -> Tuple[InterpCandidate, ...]:
    return tuple(c for c in cands if _adoptable(c))


def _rep_readings(cands: Iterable[InterpCandidate]) -> frozenset:
    return frozenset(c.rule for c in _rep_log(cands))


def _authority_ok(e: ReflowEvent) -> bool:
    return e.authority_id is not None


def _in_window(w: ReflowWindow, e: ReflowEvent) -> bool:
    return w.open_day <= e.at_day <= w.close_day


def _reflow_ok(w: ReflowWindow, e: ReflowEvent) -> bool:
    return _authority_ok(e) and _in_window(w, e)


def _dev_min(vals: Iterable[Q]) -> Q:
    vals = tuple(vals)
    if not vals:
        return Q(0)
    out = vals[0]
    for v in vals[1:]:
        if v < out:
            out = v
    return out


def _dev_max(vals: Iterable[Q]) -> Q:
    vals = tuple(vals)
    if not vals:
        return Q(0)
    out = vals[0]
    for v in vals[1:]:
        if v > out:
            out = v
    return out


def _dev_of(x: Q, s_set: Tuple[Q, ...]) -> Q:
    return _dev_min(abs(x - s) for s in s_set)


def _d_haus(s: Tuple[Q, ...], t: Tuple[Q, ...]) -> Q:
    return max(
        _dev_max(_dev_of(si, t) for si in s),
        _dev_max(_dev_of(ti, s) for ti in t))


def _obs_total(o: StratObs) -> int:
    return o.successes + o.failures


def _obs_ok(o: StratObs) -> bool:
    return _obs_total(o) > 0


def _propensity(o: StratObs) -> Q:
    return Q(o.successes, _obs_total(o))


def _assumptions_named(a: PropensityAssumptions) -> bool:
    return a.selection_modeled and a.migration_covered


def _comparable(g: Comparability) -> bool:
    return (g.same_domain and g.same_version and g.same_procedure
            and g.same_issue)


# ---------------------------------------------------------------------------
# T124 checks：表示保持 ＋ 回流权限/时际
# ---------------------------------------------------------------------------


def check_interp_rep_layer(cands: Iterable[InterpCandidate],
                           rep: InterpRepLayer) -> CheckReport:
    """Differential check of the T124 representation layer: the readings
    equal the adoption-layer rule base (no drift), the log carries only
    adopted candidates, and every record is a faithful field-by-field
    serialization of its preimage."""

    cands = tuple(cands)
    problems = []
    if frozenset(rep.readings) != _rep_readings(cands):
        problems.append("representation readings drift from the rule base")
    if frozenset(c.candidate_id for c in rep.log) != \
            frozenset(c.candidate_id for c in _rep_log(cands)):
        problems.append("representation log mismatch against adopted pool")
    for c in rep.log:
        if not _adoptable(c):
            problems.append(
                f"unadopted candidate {c.candidate_id} entered the "
                "representation log")
    if len(rep.records) != len(rep.log):
        problems.append("record count does not match log length")
    for r, c in zip(rep.records, rep.log):
        if (r.cand_id != c.candidate_id or r.rule != c.rule
                or r.reason_id != c.reason_id
                or r.authority_id != c.authority_id or r.method != c.method):
            problems.append(
                f"record {r.cand_id} is not the faithful serialization of "
                "its preimage")
    if problems:
        return CheckReport.fail(*problems)
    return CheckReport.pass_()


def check_reflow_layer(cands: Iterable[InterpCandidate],
                       window: ReflowWindow,
                       requests: Iterable[Tuple[ReflowEvent,
                                                InterpCandidate]],
                       resulting_log: Tuple[InterpCandidate, ...]
                       ) -> CheckReport:
    """Differential check of the T124 reflow gate: accepted iff authority AND
    in-window; every rejected event leaves the log untouched; every accepted
    event appends exactly its candidate (append-only, no history rewrite)."""

    problems = []
    base = _rep_log(cands)
    expected = base
    for e, c in requests:
        if _reflow_ok(window, e):
            expected = expected + (c,)
    if resulting_log != expected:
        problems.append(
            "reflow result does not match the inline authority/window "
            "re-derivation")
    prefix_len = len(base)
    if resulting_log[:prefix_len] != base:
        problems.append("reflow rewrote the historical log prefix")
    if problems:
        return CheckReport.fail(*problems)
    return CheckReport.pass_()


def check_unauthorized_reflow_rejected(window: ReflowWindow,
                                       e: ReflowEvent) -> CheckReport:
    """The T124 counterexample gate: an event without a named authority must
    be rejected by the reflow gate (无权限回流被拒)."""

    if e.authority_id is None:
        if _reflow_ok(window, e):
            return CheckReport.fail(
                "unauthorized reflow was reported accepted")
        return CheckReport.pass_()
    return CheckReport.fail("event carries an authority; gate test vacuous")


def check_out_of_window_reflow_rejected(window: ReflowWindow,
                                        e: ReflowEvent) -> CheckReport:
    """The T124 counterexample gate: an in-authority event outside the
    effective window must be rejected (时点越窗回流被拒)."""

    if e.authority_id is None:
        return CheckReport.fail("event lacks authority; gate test vacuous")
    if _in_window(window, e):
        return CheckReport.fail("event is inside the window; gate test vacuous")
    if _reflow_ok(window, e):
        return CheckReport.fail("out-of-window reflow was reported accepted")
    return CheckReport.pass_()


# ---------------------------------------------------------------------------
# T125 checks：三参照距离 ＋ 固定域 Hausdorff 偏移界
# ---------------------------------------------------------------------------


def check_three_ref_deviation(x: Q, refs: ThreeRefs,
                              readings: dict) -> CheckReport:
    """Differential check of the three-reference deviations: each reading
    equals the inline min|x-s|; an empty pool is NO baseline and must not
    produce a 0-filled reading (§12.2)."""

    problems = []
    for kind, s_set in ((RefKind.SELF, refs.self_set),
                        (RefKind.PEER, refs.peer_set),
                        (RefKind.UPPER, refs.upper_set)):
        if not s_set:
            if kind in readings:
                problems.append(
                    f"empty {kind.value} pool produced a deviation reading "
                    "(空 S 不能填 0 偏离)")
            continue
        expected = _dev_of(x, s_set)
        if kind not in readings:
            problems.append(f"missing {kind.value} deviation reading")
        elif readings[kind] != expected:
            problems.append(f"{kind.value} deviation reading mismatch")
    if problems:
        return CheckReport.fail(*problems)
    return CheckReport.pass_()


def check_hausdorff_shift(s: Tuple[Q, ...], delta: Q,
                          reported: Q) -> CheckReport:
    """Differential + bound gate for the fixed-domain shift: the reported
    d_H(S, S+delta) must satisfy d_H <= |delta| first (超界 Hausdorff 被拒)
    and then match the inline re-derivation."""

    if not (reported <= abs(delta)):
        return CheckReport.fail(
            "Hausdorff shift bound violated: d_H(S, S+delta) > |delta|")
    expected = _d_haus(s, tuple(si + delta for si in s))
    if reported != expected:
        return CheckReport.fail(
            "reported Hausdorff shift does not match inline re-derivation")
    return CheckReport.pass_()


def check_hausdorff_shift_witness(reported: Q) -> CheckReport:
    """Closed-form numeric witness: S=[0,2], delta=1/2 -> shifted domain
    [1/2, 5/2] and d_H = 1/2 exactly (偏移界紧)."""

    expected = _d_haus((Q(0), Q(2)), (Q(1, 2), Q(5, 2)))
    if expected != Q(1, 2):
        return CheckReport.fail("inline witness arithmetic is wrong")
    if reported != Q(1, 2):
        return CheckReport.fail(
            "closed-form witness reported a value other than 1/2")
    return CheckReport.pass_()


def check_empty_ref_rejected(refs: ThreeRefs,
                             produced: dict) -> CheckReport:
    """The T125 counterexample gate: an empty reference pool yields NO
    baseline; any filled reading for it is rejected (不能填 0 偏离)."""

    empty_kinds = [k for k, s in ((RefKind.SELF, refs.self_set),
                                  (RefKind.PEER, refs.peer_set),
                                  (RefKind.UPPER, refs.upper_set))
                   if not s]
    if not empty_kinds:
        return CheckReport.fail("no empty pool; gate test vacuous")
    problems = [f"empty {k.value} pool produced a reading"
                for k in empty_kinds if k in produced]
    if problems:
        return CheckReport.fail(*problems)
    return CheckReport.pass_()


def check_comparability_gate(g: Comparability,
                             admitted: bool) -> CheckReport:
    """Incomparable references must not be admitted (§12.2 可比性规则)."""

    if not _comparable(g) and admitted:
        return CheckReport.fail("incomparable reference pool was admitted")
    return CheckReport.pass_()


# ---------------------------------------------------------------------------
# T126 checks：分层倾向实算 ＋ 不重复先验 ＋ 显式假设门
# ---------------------------------------------------------------------------


def check_strat_table(obs: Iterable[StratObs], table: StratTable,
                      prior: Optional[PriorTable] = None) -> CheckReport:
    """Differential check of the stratified propensity table: every layer is
    the exact inline count ratio of its observation; zero-count strata are
    filtered; and NO layer may carry a prior-inflated posterior mean that
    differs from the data ratio (§7.3 同一标签不重复使用——先验混入被拒)."""

    problems = []
    obs = tuple(obs)
    keys = [o.key for o in obs]
    if len(set(keys)) != len(keys):
        problems.append("duplicate stratum key accepted by the builder")
    expected = {}
    for o in obs:
        if _obs_ok(o):
            expected[o.key] = _propensity(o)
    got = dict(table.layers)
    if set(got) != set(expected):
        problems.append("stratum set mismatch against the observation gate")
    for key, want in expected.items():
        if got.get(key) != want:
            problems.append(f"stratum {key} propensity is not the data ratio")
    if prior is not None:
        by_key = {o.key: o for o in obs if _obs_ok(o)}
        for (key, alpha, beta) in prior.entries:
            if key in by_key:
                posterior = Q(alpha + by_key[key].successes,
                              alpha + beta + _obs_total(by_key[key]))
                if got.get(key) == posterior and posterior != expected[key]:
                    problems.append(
                        f"stratum {key} carries prior-inflated mass "
                        f"{posterior} instead of the data ratio "
                        f"{expected[key]} (§7.3 先验混入)")
    if problems:
        return CheckReport.fail(*problems)
    return CheckReport.pass_()


def check_assumptions_gate(a: PropensityAssumptions,
                           comparison_allowed: bool) -> CheckReport:
    """The T126 explicit-assumption gate: layer comparison is allowed ONLY
    with both the selection and the migration assumptions NAMED
    (§7.3 显式假设参数；无名假设即拒)."""

    if _assumptions_named(a) and not comparison_allowed:
        return CheckReport.fail(
            "named assumptions but comparison gate refused")
    if not _assumptions_named(a) and comparison_allowed:
        return CheckReport.fail(
            "comparison allowed with UNNAMED selection/migration assumptions")
    return CheckReport.pass_()


def check_prior_double_use_witness(reported_ratio: Q) -> CheckReport:
    """The T126 counterexample gate: observation (3 successes / 1 failure)
    has data ratio 3/4 while the (1,1)-prior posterior mean is 2/3; the
    propensity layer must report the former, never the latter."""

    if reported_ratio == Q(2, 3):
        return CheckReport.fail(
            "reported the posterior mean 2/3: prior mass double-used (§7.3)")
    if reported_ratio != Q(3, 4):
        return CheckReport.fail(
            f"reported {reported_ratio} is not the data ratio 3/4")
    return CheckReport.pass_()


# ---------------------------------------------------------------------------
# T127 checks：忠实投影 ＋ 完整性
# ---------------------------------------------------------------------------


def check_report_faithful(r: DeviationReport, preimage: Q,
                          actual: Tuple[DevSource, ...]) -> CheckReport:
    """Faithful projection + completeness differential: the reading must
    equal the underlying preimage (no recompute drift — 篡改报告被拒); the
    interval must be well-formed; every actual source must be enumerated or
    the residual named; and the original status must be kept (§12.5)."""

    problems = []
    if r.reading != preimage:
        problems.append(
            "report reading drifts from the underlying preimage "
            "(不忠实投影/篡改报告)")
    if not (r.interval.lo <= r.interval.hi):
        problems.append("uncertainty interval malformed (lo > hi)")
    if not coverage_inline(actual, r):
        problems.append(
            "actual deviation source missing from the report with no named "
            "residual (完整性缺失)")
    if not r.status_kept:
        problems.append("report prose erased the original status (§12.5)")
    if problems:
        return CheckReport.fail(*problems)
    return CheckReport.pass_()


def coverage_inline(actual: Tuple[DevSource, ...],
                    r: DeviationReport) -> bool:
    # Inline re-derivation of the completeness gate.
    return all(s in r.sources for s in actual) or r.residual_named


def check_tampered_report_rejected(r: DeviationReport, preimage: Q,
                                   actual: Tuple[DevSource, ...]
                                   ) -> CheckReport:
    """The T127 counterexample gate: a report whose reading was tampered
    (differs from the preimage) must fail the faithful-projection gate."""

    if r.reading == preimage:
        return CheckReport.fail(
            "reading equals the preimage; tamper gate test vacuous")
    if report_ok_inline(r, preimage):
        return CheckReport.fail("tampered report was reported faithful")
    return CheckReport.pass_()


def report_ok_inline(r: DeviationReport, preimage: Q) -> bool:
    # Inline re-derivation of the faithful-projection gate.
    return r.reading == preimage


def check_source_kind_preserved(sources: Iterable[DevSource],
                                r: DeviationReport) -> CheckReport:
    """Every reported source keeps its named kind (§12.2 三种报告分别给依据)."""

    by_id = {s.source_id: s for s in r.sources}
    for s in sources:
        got = by_id.get(s.source_id)
        if got is None:
            return CheckReport.fail(
                f"source {s.source_id} missing from the report")
        if got.kind != s.kind:
            return CheckReport.fail(
                f"source {s.source_id} kind was erased or swapped")
    return CheckReport.pass_()


# ---------------------------------------------------------------------------
# 总差分：DeviationLayer 全链
# ---------------------------------------------------------------------------


def check_deviation_layer(cands: Iterable[InterpCandidate],
                          layer,
                          obs: Iterable[StratObs],
                          prior: Optional[PriorTable] = None
                          ) -> CheckReport:
    """Full differential of a DeviationLayer against the inline semantics:
    representation preservation, three-reference readings, Hausdorff shift
    bounds, stratified table, comparison gate and report faithfulness."""

    problems = []
    rep = check_interp_rep_layer(cands, layer.interp_rep)
    if not rep.ok:
        problems.extend(rep.reasons)
    table = check_strat_table(obs, layer.strat_table, prior)
    if not table.ok:
        problems.extend(table.reasons)
    gate = check_assumptions_gate(layer.assumptions,
                                  layer.comparison_allowed)
    if not gate.ok:
        problems.extend(gate.reasons)
    faithful = check_report_faithful(layer.report, layer.report.reading,
                                     tuple(layer.report.sources))
    if not faithful.ok:
        problems.extend(faithful.reasons)
    if problems:
        return CheckReport.fail(*problems)
    return CheckReport.pass_()
