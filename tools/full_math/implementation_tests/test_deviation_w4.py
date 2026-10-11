"""W4 deviation seam tests: T124-T127 (K rows 2553-2556).

T124 解释一致性: adopted-interpretation representation preservation and
reflow with authority/time — unauthorized or out-of-window reflows are
REJECTED (the row's original counterexample face, kept independently).
T125 三参照偏离: three-reference distance and the fixed-domain Hausdorff
shift bound d_H(S, S+delta) <= |delta|; empty pools get NO 0-filled
reading; overbound Hausdorff reports are rejected.
T126 倾向分层: exact rational count ratios; prior tables stay out of the
propensity input (double-use is detectable: 3/4 vs 2/3); selection/
migration assumptions are explicit gate parameters.
T127 偏离报告: faithful projection (tampered readings rejected) and
completeness (unlisted sources rejected unless the residual is named).
Plus the independent-checker differential, downstream consumption through
the existing interp layer entry, and the W4:T124..T127 completion/validate
receipts for the six-piece closure.
"""
import ast
import importlib.util
from fractions import Fraction as Q
from pathlib import Path

import pytest

from tools.full_math.implementation import interpretation_ref as R
from tools.full_math.implementation import deviation_ref as D
from tools.full_math.implementation import deviation_check as KC

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[2]


def _load_completion():
    """Load tools/full_math/completion.py by explicit path — NO sys.path
    insert: tools/full_math carries a `reference` package that would shadow
    tools/unified_math_v2/reference in a shared pytest process."""
    path = REPO / 'tools/full_math/completion.py'
    spec = importlib.util.spec_from_file_location('completion_t124_t127_w4',
                                                  str(path))
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


C = _load_completion()

LEAN_MODULE = (REPO / 'proofs/lean/juris_lean/JurisLean/Seams/'
               'UnifiedW4Deviation.lean')

RULE_A = R.RuleAst(rule_id="R-1", premises=("contract_signed",),
                   conclusion="payment_due")
RULE_B = R.RuleAst(rule_id="R-2", premises=("usage_evidenced",),
                   conclusion="payment_due")
RULE_C = R.RuleAst(rule_id="R-3", premises=("unauth_premise",),
                   conclusion="payment_due")
INPUT_X = R.InterpInput(text_id="art7-text", context_ids=("mat-11",))


def _adopted(cid="c1", rule=RULE_A):
    return R.mk_candidate(R.InterpMethod.LITERAL, cid, INPUT_X, "art7",
                          "civil", R.InterpEffect.SELECT_READING, rule,
                          "reason-1", "court-9")


def _unadopted(cid="c99", rule=RULE_C):
    return R.mk_literal(cid, INPUT_X, "art7", "civil",
                        R.InterpEffect.SELECT_READING, rule, "reason-9")


def _refs(self_set, peer_set, upper_set):
    return D.ThreeRefs(self_set=tuple(self_set), peer_set=tuple(peer_set),
                       upper_set=tuple(upper_set))


COMPARABLE = D.Comparability(same_domain=True, same_version=True,
                             same_procedure=True, same_issue=True)
INCOMPARABLE = D.Comparability(same_domain=True, same_version=False,
                               same_procedure=True, same_issue=True)
WINDOW = D.ReflowWindow(open_day=10, close_day=20)


def _reflow_event(eid="e1", cid="c1", authority="court-9", at_day=15):
    return D.ReflowEvent(event_id=eid, cand_id=cid,
                         authority_id=authority, at_day=at_day)


def _named_assumptions():
    return D.PropensityAssumptions(selection_modeled=True,
                                   migration_covered=True)


def _unnamed_assumptions(selection=True):
    return D.PropensityAssumptions(selection_modeled=selection,
                                   migration_covered=False)


# ---------------------------------------------------------------------------
# T124: 已采用解释表示保持 ＋ 回流权限/时际
# ---------------------------------------------------------------------------


@pytest.mark.parametrize('method', list(R.InterpMethod))
def test_record_field_faithful(method):
    """P066/§10.1：序列化记录逐字段保真——规则/理由/权限读数＝采用层原像
    （对照 Lean record_rule_faithful/record_adoptable_matches）。"""
    c = R.mk_candidate(method, "c1", INPUT_X, "art7", "civil",
                       R.InterpEffect.SELECT_READING, RULE_A, "reason-1",
                       "court-9")
    rec = D.record_of(c)
    assert D.record_rule(rec) is c.rule
    assert rec.cand_id == c.candidate_id
    assert rec.reason_id == c.reason_id
    assert rec.authority_id == c.authority_id
    assert D.record_adoptable(rec) == R.adoptable(c)


def test_rep_layer_readings_match_rule_base():
    """§10.1 表示保持：表示层读数＝采用层规则库原像（不漂移）。"""
    a, b = _adopted("c1"), _adopted("c2", RULE_B)
    rep = D.build_interp_rep_layer([a, b])
    assert rep.readings == D.rep_readings([a, b])
    assert frozenset(rep.readings) == R.rule_base([a, b])
    assert len(rep.records) == len(rep.log) == 2


def test_unadopted_never_enters_rep_layer():
    """T124 原反例面（独立保留）：无采用权限候选的"读数"进不了表示层——
    不进日志、不进读数、不可序列化（fail-fast）。"""
    unauth = _unadopted()
    rep = D.build_interp_rep_layer([unauth])
    assert rep.log == () and rep.readings == () and rep.records == ()
    with pytest.raises(ValueError):
        D.record_of(unauth)


def test_rep_gate_rejects_tampered_readings():
    """不漂移门：把未采用候选的规则塞进声称读数被独立 checker 拒绝。"""
    a, unauth = _adopted("c1"), _unadopted("c2")
    rep = D.build_interp_rep_layer([a])
    forged = D.InterpRepLayer(
        log=rep.log, readings=rep.readings + (unauth.rule,),
        records=rep.records)
    report = KC.check_interp_rep_layer([a], forged)
    assert not report.ok and any('drift' in r for r in report.reasons)
    assert KC.check_interp_rep_layer([a], rep).ok


def test_rep_gate_rejects_forged_record():
    """记录保真差分：字段被改的序列化记录被拒（记录读数≠原像）。"""
    a = _adopted("c1")
    rep = D.build_interp_rep_layer([a])
    forged_record = D.RepRecord(cand_id="c1", method=a.method,
                                rule=RULE_B, reason_id=a.reason_id,
                                authority_id=a.authority_id)
    forged = D.InterpRepLayer(log=rep.log, readings=rep.readings,
                              records=(forged_record,))
    report = KC.check_interp_rep_layer([a], forged)
    assert not report.ok and any('serialization' in r for r in report.reasons)


def test_reflow_authorized_in_window_accepted():
    """§9.4：有权限＋在窗内的回流接受且纯追加（append-only）。"""
    a = _adopted("c1")
    e = _reflow_event(at_day=15)
    log = D.rep_log([a])
    assert D.reflow_ok(WINDOW, e)
    new_log = D.apply_reflow(log, WINDOW, e, a)
    assert new_log == log + (a,)
    assert D.check_reflow(WINDOW, e, [a]) is a
    report = KC.check_reflow_layer([a], WINDOW, [(e, a)], new_log)
    assert report.ok, report.reasons


def test_reflow_unauthorized_rejected():
    """T124 原反例（独立保留）：无权限回流被拒——门抛 PermissionError，
    日志原样不动（历史不重写）。"""
    a = _adopted("c1")
    e = _reflow_event(authority=None, at_day=15)
    log = D.rep_log([a])
    with pytest.raises(PermissionError):
        D.check_reflow(WINDOW, e, [a])
    assert D.apply_reflow(log, WINDOW, e, a) == log
    gate = KC.check_unauthorized_reflow_rejected(WINDOW, e)
    assert gate.ok, gate.reasons
    report = KC.check_reflow_layer([a], WINDOW, [(e, a)], log)
    assert report.ok, report.reasons


@pytest.mark.parametrize('at_day', [9, 21])
def test_reflow_out_of_window_rejected(at_day):
    """T124 原反例（独立保留）：时点越窗回流被拒（越窗 9/21 两侧）。"""
    a = _adopted("c1")
    e = _reflow_event(at_day=at_day)
    log = D.rep_log([a])
    with pytest.raises(ValueError):
        D.check_reflow(WINDOW, e, [a])
    assert D.apply_reflow(log, WINDOW, e, a) == log
    gate = KC.check_out_of_window_reflow_rejected(WINDOW, e)
    assert gate.ok, gate.reasons


def test_reflow_non_adopted_candidate_rejected():
    """回流目标须是已采用候选：未采用候选的回流事件被拒。"""
    unauth = _unadopted("c9")
    e = _reflow_event(cid="c9", at_day=15)
    with pytest.raises(ValueError):
        D.check_reflow(WINDOW, e, [unauth])


# ---------------------------------------------------------------------------
# T125: 三参照偏离 ＋ 固定域 Hausdorff 偏移界
# ---------------------------------------------------------------------------


def _dev_lipschitz_ok(x, y, s_set):
    return abs(D.dev_of(x, s_set) - D.dev_of(y, s_set)) <= abs(x - y)


@pytest.mark.parametrize('x,s_set', [
    (Q(1), (Q(0), Q(2))),
    (Q(1, 2), (Q(0), Q(2), Q(5))),
    (Q(0), (Q(3),)),
    (Q(-4), (Q(-5), Q(0), Q(7))),
])
def test_dev_structure_nonneg_attained_lipschitz(x, s_set):
    """§12.2 距离结构：偏离非负、在参照点取到（min 可达）、对读数点
    Lipschitz、Hausdorff 对称。"""
    dev = D.dev_of(x, s_set)
    assert dev >= 0
    attained = min(abs(x - s) for s in s_set)
    assert dev == attained
    assert _dev_lipschitz_ok(x, x + Q(1, 3), s_set)
    assert _dev_lipschitz_ok(x, Q(99), s_set)
    other = tuple(s + Q(1) for s in s_set)
    assert D.d_haus(s_set, other) == D.d_haus(other, s_set)


@pytest.mark.parametrize('s_set,delta', [
    ((Q(0), Q(2)), Q(1, 2)),
    ((Q(0), Q(2)), Q(-3)),
    ((Q(1, 3), Q(7, 5)), Q(0)),
    ((Q(10),), Q(99)),
])
def test_hausdorff_shift_bound(s_set, delta):
    """§12.2 固定域平移偏移界：d_H(S, S+δ) ≤ |δ|（实算＋独立 checker）。"""
    reported = D.hausdorff_shift(s_set, delta)
    assert reported <= abs(delta)
    assert KC.check_hausdorff_shift(s_set, delta, reported).ok


def test_hausdorff_shift_witness_closed_form():
    """闭式数值例：S=[0,2]、δ=1/2 → 平移域 [1/2, 5/2]，d_H = 1/2（恰等）。"""
    assert D.hausdorff_shift((Q(0), Q(2)), Q(1, 2)) == Q(1, 2)
    assert KC.check_hausdorff_shift_witness(Q(1, 2)).ok


def test_hausdorff_overbound_report_rejected():
    """超界 Hausdorff 被拒：报告值 > |δ| 或与内联重算不符都被 checker 拒。"""
    s_set, delta = (Q(0), Q(2)), Q(1, 2)
    over = KC.check_hausdorff_shift(s_set, delta, Q(1))
    assert not over.ok and any('bound' in r for r in over.reasons)
    wrong = KC.check_hausdorff_shift(s_set, delta, Q(1, 3))
    assert not wrong.ok and any('re-derivation' in r for r in wrong.reasons)
    bad_witness = KC.check_hausdorff_shift_witness(Q(3, 4))
    assert not bad_witness.ok


def test_empty_ref_no_baseline():
    """§12.2 原反例面：空 S 是无比较基准——不能填 0 偏离（实算抛错＋checker
    拒绝任何对空池的读数）。"""
    refs = _refs((), (Q(1),), (Q(2),))
    with pytest.raises(ValueError):
        D.dev_three(Q(0), refs)
    assert not D.dev_reading_ok(())
    gate = KC.check_empty_ref_rejected(refs, {D.RefKind.SELF: Q(0)})
    assert not gate.ok
    gate_ok = KC.check_empty_ref_rejected(refs, {})
    assert gate_ok.ok, gate_ok.reasons


def test_incomparable_refs_rejected():
    """§12.2 可比性规则：不可比参照不进参照集（总装 fail-fast）。"""
    refs = _refs((Q(0),), (Q(1),), (Q(2),))
    with pytest.raises(ValueError):
        D.build_deviation_layer(
            [], comparability=INCOMPARABLE, refs=refs,
            shift_deltas=(Q(0),), strat_obs=(),
            assumptions=_named_assumptions(), interval=D.Uncert(Q(0), Q(1)))
    assert KC.check_comparability_gate(INCOMPARABLE, True).ok is False


def test_three_refs_full_layer():
    """三参照全实算：逐参照 min|x−s| 与手工值一致。"""
    refs = _refs((Q(0), Q(4)), (Q(1),), (Q(3), Q(10)))
    readings = D.dev_three(Q(1), refs)
    assert readings[D.RefKind.SELF] == Q(1)      # min(|1-0|, |1-4|) = 1
    assert readings[D.RefKind.PEER] == Q(0)
    assert readings[D.RefKind.UPPER] == Q(2)     # min(2, 9)
    assert KC.check_three_ref_deviation(Q(1), refs, readings).ok


# ---------------------------------------------------------------------------
# T126: 倾向分层实算 ＋ 不重复先验 ＋ 显式选择/迁移假设
# ---------------------------------------------------------------------------


@pytest.mark.parametrize('successes,failures,expected', [
    (3, 1, Q(3, 4)),
    (0, 5, Q(0)),
    (2, 2, Q(1, 2)),
    (7, 3, Q(7, 10)),
])
def test_propensity_exact_ratios(successes, failures, expected):
    """§12.3 分层倾向实算＝层内计数比（ℚ 精确）且落在单位区间。"""
    o = D.mk_strat_obs("k1", successes, failures)
    got = D.propensity(o)
    assert got == expected
    assert 0 <= got <= 1
    assert D.obs_ok(o)


def test_zero_and_negative_counts_rejected():
    """零计数层不进表（门过滤）；负计数构造直接拒绝（fail-fast）。"""
    zero = D.mk_strat_obs("k0", 0, 0)
    assert not D.obs_ok(zero)
    with pytest.raises(ValueError):
        D.propensity(zero)
    with pytest.raises(ValueError):
        D.mk_strat_obs("kx", -1, 3)


def test_strat_table_reads_obs_only():
    """分层表只由观测实算：层键唯一 fail-fast；零计数层被过滤。"""
    obs = (D.mk_strat_obs("court-a", 3, 1),
           D.mk_strat_obs("court-b", 1, 2),
           D.mk_strat_obs("court-c", 0, 0))
    table = D.build_strat_table(obs)
    assert dict(table.layers) == {"court-a": Q(3, 4), "court-b": Q(1, 3)}
    assert ("court-a", Q(3, 4)) in table.layers
    with pytest.raises(ValueError):
        D.build_strat_table((D.mk_strat_obs("k", 1, 1),
                             D.mk_strat_obs("k", 2, 1)))
    assert KC.check_strat_table(obs, table).ok


def test_prior_not_double_used():
    """§7.3 原反例（独立保留）：同一观测 (3/1) 的倾向实算是 3/4，混入 (1,1)
    先验的后验均值是 2/3——倾向层输出前者，从不输出后者。"""
    o = D.mk_strat_obs("k", 3, 1)
    assert D.propensity(o) == Q(3, 4)
    assert D.posterior_mean(1, 1, o) == Q(2, 3)
    assert D.propensity(o) != D.posterior_mean(1, 1, o)
    assert KC.check_prior_double_use_witness(D.propensity(o)).ok
    bad = KC.check_prior_double_use_witness(D.posterior_mean(1, 1, o))
    assert not bad.ok and any('double-used' in r for r in bad.reasons)


def test_prior_mixed_in_detected():
    """先验混入可检：把 (1,0) 先验计数加进观测得 4/5 ≠ 3/4，独立 checker 从
    原始观测重算并拒绝携带后验均值的伪造表（§7.3 不重复先验数据）。"""
    obs = (D.mk_strat_obs("k", 3, 1),)
    clean = D.build_strat_table(obs)
    forged = D.StratTable(layers=(("k", Q(4, 5)),))
    prior = D.PriorTable(entries=(("k", 1, 0),))
    assert D.propensity(D.mk_strat_obs("k", 3 + 1, 1)) == Q(4, 5)
    assert KC.check_strat_table(obs, clean).ok
    bad = KC.check_strat_table(obs, forged, prior)
    assert not bad.ok and any('prior' in r for r in bad.reasons)


def test_assumptions_gate():
    """§7.3 显式假设门：选择/迁移假设两面具名才放行比较；无名假设直接拒绝
    （显式假设参数，不在定理内隐含）。"""
    assert D.comparison_gate(_named_assumptions()) is True
    with pytest.raises(ValueError):
        D.comparison_gate(_unnamed_assumptions())
    with pytest.raises(ValueError):
        D.comparison_gate(_unnamed_assumptions(selection=False))
    assert KC.check_assumptions_gate(_named_assumptions(), True).ok
    assert not KC.check_assumptions_gate(_unnamed_assumptions(), True).ok
    assert not KC.check_assumptions_gate(_named_assumptions(), False).ok


def test_strat_use_has_no_norm_base_constructor():
    """T126：倾向不写入法源——用途分型只有描述/具名假设比较两值，没有
    "写入法源"构造子。"""
    assert {u.value for u in D.StratUse} == {
        "descriptive", "comparison_under_named_assumptions"}


# ---------------------------------------------------------------------------
# T127: 偏离报告——忠实投影 ＋ 完整性
# ---------------------------------------------------------------------------


def _source(sid="s-structural", kind=D.DevKind.STRUCTURAL):
    return D.DevSource(source_id=sid, kind=kind)


def _interval():
    return D.Uncert(Q(0), Q(1, 2))


def test_report_faithful_projection():
    """§12.5 忠实投影：报告读数＝底层计算原像；来源/区间/status 逐项保留。"""
    preimage = Q(1, 2)
    rep = D.mk_report("rpt-1", D.RefKind.SELF, preimage,
                      (_source(),), _interval())
    assert D.report_ok(rep, preimage)
    assert rep.reading == preimage
    assert rep.sources == (_source(),)
    assert rep.interval == _interval()
    assert rep.residual_named and rep.status_kept
    assert KC.check_report_faithful(rep, preimage, (_source(),)).ok
    assert KC.check_source_kind_preserved((_source(),), rep).ok


def test_tampered_report_rejected():
    """T127 原反例（独立保留）：读数被篡改的报告被忠实投影门拒绝
    （报告不重算——重算值≠投影值即漂移）。"""
    preimage = Q(1, 2)
    rep = D.mk_report("rpt-1", D.RefKind.SELF, preimage,
                      (_source(),), _interval())
    tampered = D.DeviationReport(
        report_id=rep.report_id, ref_kind=rep.ref_kind, reading=Q(3, 4),
        sources=rep.sources, interval=rep.interval,
        residual_named=rep.residual_named, status_kept=rep.status_kept)
    assert not D.report_ok(tampered, preimage)
    gate = KC.check_tampered_report_rejected(tampered, preimage,
                                             (_source(),))
    assert gate.ok, gate.reasons


def test_report_requires_sources_and_wf_interval():
    """构造器 fail-fast：无具名来源/区间倒挂直接拒绝。"""
    with pytest.raises(ValueError):
        D.mk_report("rpt-1", D.RefKind.SELF, Q(1), (), _interval())
    with pytest.raises(ValueError):
        D.mk_report("rpt-1", D.RefKind.SELF, Q(1), (_source(),),
                    D.Uncert(Q(2), Q(1)))


def test_coverage_gate_completeness():
    """§12.5 完整性：实际来源逐项枚举→门过；有来源未列且残余未具名→门拒
    （checker 全链同步拒绝）。"""
    s1, s2 = _source("s1"), _source("s2", D.DevKind.EMPIRICAL)
    full = D.mk_report("rpt", D.RefKind.SELF, Q(1), (s1, s2), _interval())
    assert D.coverage_ok((s1, s2), full)
    assert KC.check_report_faithful(full, Q(1), (s1, s2)).ok
    partial = D.mk_report("rpt", D.RefKind.SELF, Q(1), (s1,), _interval())
    # mk_report 默认残余具名；把残余标记也抹掉才是完整性缺失的伪造面
    unlisted = D.DeviationReport(
        report_id=partial.report_id, ref_kind=partial.ref_kind,
        reading=partial.reading, sources=partial.sources,
        interval=partial.interval, residual_named=False,
        status_kept=True)
    assert D.coverage_ok((s1, s2), full)
    assert KC.check_report_faithful(full, Q(1), (s1, s2)).ok
    assert not D.coverage_ok((s1, s2), unlisted)
    report = KC.check_report_faithful(unlisted, Q(1), (s1, s2))
    assert not report.ok and any('completeness' in r or 'missing' in r
                                 for r in report.reasons)
    # 残余具名则诚实列残余，门可过（§12.5：枚举∨具名残余）
    residual = D.DeviationReport(
        report_id=partial.report_id, ref_kind=partial.ref_kind,
        reading=partial.reading, sources=partial.sources,
        interval=partial.interval, residual_named=True,
        status_kept=True)
    assert D.coverage_ok((s1, s2), residual)
    assert KC.check_source_kind_preserved((s1, s2), partial).ok is False


def test_source_kind_swap_rejected():
    """来源分型被抹/被换被拒（§12.2 三种报告分别给依据）。"""
    rep = D.mk_report("rpt", D.RefKind.SELF, Q(1),
                      (_source("s1", D.DevKind.NORMATIVE),), _interval())
    assert KC.check_source_kind_preserved(
        (_source("s1", D.DevKind.NORMATIVE),), rep).ok
    assert not KC.check_source_kind_preserved(
        (_source("s1", D.DevKind.STRUCTURAL),), rep).ok


# ---------------------------------------------------------------------------
# 下游消费：经既有 interp 层入口（build_interp_layer）直接测试
# ---------------------------------------------------------------------------


def test_downstream_interp_entry_consumption():
    """T124 消费 T122/T123 解释层入口：run_case 同款 build_interp_layer 的
    采用集进表示层后，读数＝该层规则库（消费链不漂移）；独立 checker 认可。"""
    a, b = _adopted("c1"), _adopted("c2", RULE_B)
    unauth = _unadopted("c3")
    layer = R.build_interp_layer([a, b, unauth],
                                 (R.PriorityPair("c1", "c2"),))
    assert layer.resolved == ("c1",)
    adopted = [c for c in (a, b, unauth)
               if c.candidate_id in set(layer.resolved)]
    rep = D.build_interp_rep_layer(adopted)
    # 消费链不漂移：表示层读数＝解释层采用集的规则库原像
    assert frozenset(rep.readings) == layer.rule_base
    assert KC.check_interp_rep_layer(adopted, rep).ok
    # 未采用候选经主链亦不可回流（回流目标须已采用）
    e = _reflow_event(cid="c3", at_day=15)
    with pytest.raises(ValueError):
        D.check_reflow(WINDOW, e, adopted + [unauth])


def test_downstream_full_deviation_layer_checker():
    """全链差分：偏差层总装（T124–T127 四面）被独立 checker 认可。"""
    a, b = _adopted("c1"), _adopted("c2", RULE_B)
    refs = _refs((Q(0), Q(4)), (Q(1),), (Q(3), Q(10)))
    obs = (D.mk_strat_obs("court-a", 3, 1),
           D.mk_strat_obs("court-b", 1, 2))
    actual = (_source("s1"), _source("s2", D.DevKind.EMPIRICAL))
    layer = D.build_deviation_layer(
        [a, b],
        reflow_requests=((WINDOW, _reflow_event(cid="c1", at_day=15), a),),
        comparability=COMPARABLE, refs=refs, reading_point=Q(1),
        shift_deltas=(Q(0), Q(1, 2)), strat_obs=obs,
        assumptions=_named_assumptions(), actual_sources=actual,
        interval=_interval())
    assert layer.comparison_allowed is True
    assert layer.reflows == (("e1", True),)
    for delta, value in layer.hausdorff_shifts:
        assert value <= abs(delta)
    report = KC.check_deviation_layer([a, b], layer, obs)
    assert report.ok, report.reasons
    readings = {D.RefKind(k): v for k, v in layer.dev_readings}
    assert KC.check_three_ref_deviation(Q(1), refs, readings).ok


# ---------------------------------------------------------------------------
# 合成回执：completion/validate 六件套收口（W4:T124..T127）
# ---------------------------------------------------------------------------


def _lean_has(theorem: str) -> bool:
    local = theorem.split('.')[-1]
    text = LEAN_MODULE.read_text(encoding='utf-8')
    return f'theorem {local} ' in text


def _test_functions_of_this_module():
    tree = ast.parse(Path(__file__).read_text(encoding='utf-8'))
    return {node.name for node in ast.walk(tree)
            if isinstance(node, ast.FunctionDef) and
            node.name.startswith('test_')}


CONTRACT_NAME = 'JurisLean.Seams.UnifiedW4Deviation'

T124_THEOREM = 'JurisLean.Seams.UnifiedW4Deviation.t124_interp_consistency'
T125_THEOREM = 'JurisLean.Seams.UnifiedW4Deviation.t125_three_ref_deviation'
T126_THEOREM = 'JurisLean.Seams.UnifiedW4Deviation.t126_stratified_propensity'
T127_THEOREM = ('JurisLean.Seams.UnifiedW4Deviation.'
                't127_deviation_report_complete')
FLAGSHIP_THEOREM = 'JurisLean.Seams.UnifiedW4Deviation.w4_deviation_flagship'

_POS_T124 = [
    'tools/full_math/implementation_tests/test_deviation_w4.py::'
    'test_record_field_faithful',
    'tools/full_math/implementation_tests/test_deviation_w4.py::'
    'test_rep_layer_readings_match_rule_base',
    'tools/full_math/implementation_tests/test_deviation_w4.py::'
    'test_reflow_authorized_in_window_accepted',
    'tools/full_math/implementation_tests/test_deviation_w4.py::'
    'test_downstream_interp_entry_consumption',
]
_NEG_T124 = [
    'tools/full_math/implementation_tests/test_deviation_w4.py::'
    'test_reflow_unauthorized_rejected',
    'tools/full_math/implementation_tests/test_deviation_w4.py::'
    'test_reflow_out_of_window_rejected',
    'tools/full_math/implementation_tests/test_deviation_w4.py::'
    'test_unadopted_never_enters_rep_layer',
]
_POS_T125 = [
    'tools/full_math/implementation_tests/test_deviation_w4.py::'
    'test_dev_structure_nonneg_attained_lipschitz',
    'tools/full_math/implementation_tests/test_deviation_w4.py::'
    'test_hausdorff_shift_bound',
    'tools/full_math/implementation_tests/test_deviation_w4.py::'
    'test_hausdorff_shift_witness_closed_form',
]
_NEG_T125 = [
    'tools/full_math/implementation_tests/test_deviation_w4.py::'
    'test_hausdorff_overbound_report_rejected',
    'tools/full_math/implementation_tests/test_deviation_w4.py::'
    'test_empty_ref_no_baseline',
    'tools/full_math/implementation_tests/test_deviation_w4.py::'
    'test_incomparable_refs_rejected',
]
_POS_T126 = [
    'tools/full_math/implementation_tests/test_deviation_w4.py::'
    'test_propensity_exact_ratios',
    'tools/full_math/implementation_tests/test_deviation_w4.py::'
    'test_strat_table_reads_obs_only',
    'tools/full_math/implementation_tests/test_deviation_w4.py::'
    'test_assumptions_gate',
]
_NEG_T126 = [
    'tools/full_math/implementation_tests/test_deviation_w4.py::'
    'test_prior_not_double_used',
    'tools/full_math/implementation_tests/test_deviation_w4.py::'
    'test_prior_mixed_in_detected',
    'tools/full_math/implementation_tests/test_deviation_w4.py::'
    'test_zero_and_negative_counts_rejected',
]
_POS_T127 = [
    'tools/full_math/implementation_tests/test_deviation_w4.py::'
    'test_report_faithful_projection',
    'tools/full_math/implementation_tests/test_deviation_w4.py::'
    'test_coverage_gate_completeness',
    'tools/full_math/implementation_tests/test_deviation_w4.py::'
    'test_downstream_full_deviation_layer_checker',
]
_NEG_T127 = [
    'tools/full_math/implementation_tests/test_deviation_w4.py::'
    'test_tampered_report_rejected',
    'tools/full_math/implementation_tests/test_deviation_w4.py::'
    'test_report_requires_sources_and_wf_interval',
    'tools/full_math/implementation_tests/test_deviation_w4.py::'
    'test_source_kind_swap_rejected',
]


def _receipt_row(t_id, theorem, test_ids, negative_ids):
    return {
        'id': t_id,
        'theorem': theorem,
        'contract': CONTRACT_NAME,
        'proof_mode': 'KERNEL_CONTRACT_PROOF',
        'generality': 'PARAMETRIC_OVER_FINITE_POOLS_AND_OBSERVATIONS',
        'formal_scope': 'representation layer over the adopted candidate '
                        'pool; reflow gate over finite events; three '
                        'reference distances over finite rational pools; '
                        'stratified propensities over finite observation '
                        'tables; deviation reports over finite sources',
        'independent_semantics': 'deviation_check.py inline re-derivation '
                                 '(rep log/readings, reflow authority+'
                                 'window, min/max distances, Hausdorff, '
                                 'count ratios, prior separation, report '
                                 'projection/completion), shares frozen '
                                 'carriers only',
        'algorithm': 'deviation_ref.py build_interp_rep_layer, apply_reflow/'
                     'check_reflow, dev_of/d_haus/hausdorff_shift, '
                     'build_strat_table, mk_report/build_deviation_layer',
        'observation_contract': 'InterpRepLayer (log/readings/records) + '
                                'DeviationLayer (reflows/dev_readings/'
                                'hausdorff_shifts/strat_table/comparison_'
                                'allowed/report) + per-gate booleans',
        'external_assumptions': 'synthetic sources, pools and observation '
                                'counts only; no real precedent force is '
                                'asserted (三参照/先验为合成登记值)',
        'proof_sources': ['proofs/lean/juris_lean/JurisLean/Seams/'
                          'UnifiedW4Deviation.lean'],
        'implementation_sources': [
            'tools/full_math/implementation/deviation_ref.py',
            'tools/full_math/implementation/deviation_check.py',
            'tools/full_math/implementation/interpretation_ref.py',
        ],
        'test_ids': test_ids,
        'negative_test_ids': negative_ids,
        'semantic_links': ['JurisLean.Seams.UnifiedW4Deviation',
                           'JurisLean.Seams.UnifiedW4Interp'],
    }


def test_completion_receipt_t124():
    row = _receipt_row('W4:T124', T124_THEOREM, _POS_T124, _NEG_T124)
    C.validate_binding(row, {'id': row['id'], 'theorem': T124_THEOREM,
                             'contract': row['contract']}, repo=REPO)


def test_completion_receipt_t125():
    row = _receipt_row('W4:T125', T125_THEOREM, _POS_T125, _NEG_T125)
    C.validate_binding(row, {'id': row['id'], 'theorem': T125_THEOREM,
                             'contract': row['contract']}, repo=REPO)


def test_completion_receipt_t126():
    row = _receipt_row('W4:T126', T126_THEOREM, _POS_T126, _NEG_T126)
    C.validate_binding(row, {'id': row['id'], 'theorem': T126_THEOREM,
                             'contract': row['contract']}, repo=REPO)


def test_completion_receipt_t127():
    row = _receipt_row('W4:T127', T127_THEOREM, _POS_T127, _NEG_T127)
    C.validate_binding(row, {'id': row['id'], 'theorem': T127_THEOREM,
                             'contract': row['contract']}, repo=REPO)


def test_completion_receipt_negative_tampered():
    row = _receipt_row('W4:T124', T124_THEOREM, _POS_T124, _NEG_T124)
    row['proof_mode'] = 'FIXED_EXAMPLE_NOT_PROOF'
    with pytest.raises(C.EvidenceError):
        C.validate_binding(row, {'id': row['id'], 'theorem': T124_THEOREM,
                                 'contract': row['contract']})


def test_receipt_anchors_resolve():
    """回执锚点实盘：引用的 Lean 定理与本模块测试节点都真实存在。"""
    assert _lean_has(T124_THEOREM)
    assert _lean_has(T125_THEOREM)
    assert _lean_has(T126_THEOREM)
    assert _lean_has(T127_THEOREM)
    assert _lean_has(FLAGSHIP_THEOREM)
    tests = _test_functions_of_this_module()
    for name in (_POS_T124 + _NEG_T124 + _POS_T125 + _NEG_T125
                 + _POS_T126 + _NEG_T126 + _POS_T127 + _NEG_T127):
        assert name.split('::')[-1] in tests, name
