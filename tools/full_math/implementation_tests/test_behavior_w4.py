"""T116-T121 behavior batch tests (K rows 2545-2550).

T116: multi-issue negotiation — the IR set is defined directly (may be
empty/multi-component/non-convex) and the FULL argmax is kept; every
positive-weight-sum maximizer is a Pareto point (the flagship) — uniqueness
is never claimed (the row's counterexample reading, kept independently).
T117: robust action under the SHARED theta — the two-period theta/(1-theta)
instance keeps the shared total at 1 while the rectangular stepwise sum
forges 0, and the per-period box admits (1,1) which no shared theta reaches.
T118: gross VOI >= 0 but NET VOI subtracts the permission cost and can be
negative; the finite-horizon Snell policy achieves V and every admissible
stop pays at most V; a second (contradicting) piece of evidence can LOWER
the expected decision value (non-monotone, kept independently).
T119: causal / liability / utility readings of the SAME trace diverge —
privileged defense causes harm without liability (projection separation).
T120: the compliance comparison keeps the violating actions IN the space;
with sanctions p*F the compliance-dominance condition holds or fails by the
declared parameters (weak-deterrence counterexample kept independently).
T121: a behavior event updates the OBSERVATION layer and the SAME rule
re-evaluates: the verdict flips false->true; unauthorized events never
replace the rule.
Plus the independent-checker differential, the downstream consumption via
the unified process entries (see tools/unified_math_v2/tests/
test_behavior_backflow_w4.py), and the completion/validate receipts for
W4:T116..T121.
"""
import ast
import importlib.util
from fractions import Fraction
from pathlib import Path

import pytest

from tools.full_math.implementation import behavior_ref as R
from tools.full_math.implementation import behavior_check as K

F = Fraction

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[2]


def _load_completion():
    """Load tools/full_math/completion.py by explicit path — NO sys.path
    insert: tools/full_math carries a `reference` package that would shadow
    tools/unified_math_v2/reference in a shared pytest process."""
    path = REPO / 'tools/full_math/completion.py'
    spec = importlib.util.spec_from_file_location('completion_t116_t121',
                                                  str(path))
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


C = _load_completion()

LEAN_MODULE = (REPO / 'proofs/lean/juris_lean/JurisLean/Seams/'
               'UnifiedW4Behavior.lean')

# ---------------------------------------------------------------------------
# 共享夹具
# ---------------------------------------------------------------------------


def _nego():
    """三协议点：x=(2,1)、y=(1,2) 都过 IR；z=(3,0) 未过 IR（P2 低于外部
    选项）。等权下 x/y/z 的加权和同为 3——argmax 三个元素，全保留。"""
    return R.MultiIssueNegotiation(
        agreements=("x", "y", "z"),
        utilities={
            "P1": {"x": F(2), "y": F(1), "z": F(3)},
            "P2": {"x": F(1), "y": F(2), "z": F(0)},
        },
        reservations={"P1": F(1), "P2": F(1)},
        weights={"P1": F(1), "P2": F(1)},
    )


def _theta_tree():
    """θ∈{0,1} 决定两期收益 θ 与 1−θ：共享 θ 总收益恒 1。"""
    return R.ScenarioTree(
        scenarios=("0", "1"),
        r1={"0": F(0), "1": F(1)},
        r2={"0": F(1), "1": F(0)},
    )


def _info_problem(cost=None):
    return R.InfoAcquisition(
        states=("s1", "s2"),
        choices=("a1", "a2"),
        prior={"s1": F(1, 2), "s2": F(1, 2)},
        utils={
            "a1": {"s1": F(1), "s2": F(0)},
            "a2": {"s1": F(0), "s2": F(1)},
        },
        cost=F(1) if cost is None else cost,
    )


def _defense_trace():
    """特权防卫（行为人 7 致害 5 无净得）＋ 普通侵权（行为人 9 致害 3 净得 8）。"""
    return (
        R.Act("7", True, F(5), F(0)),
        R.Act("9", False, F(3), F(8)),
    )


def _strong_game():
    return R.ComplianceGame((
        R.ComplianceAction("comply", True, F(5), F(0), F(0)),
        R.ComplianceAction("violate", False, F(10), F(12), F(1, 2)),
    ))


def _weak_game():
    return R.ComplianceGame((
        R.ComplianceAction("comply", True, F(5), F(0), F(0)),
        R.ComplianceAction("violate", False, F(10), F(4), F(1, 2)),
    ))


# ---------------------------------------------------------------------------
# T116：多议题谈判（非凸 IR 与全 argmax）
# ---------------------------------------------------------------------------


def test_ir_set_direct_and_empty():
    """§8.4：S_IR 直接定义，可空——无协议过 IR 时单列空集（谈判无解诊断），
    不伪造协议；argmax 是对可行集的读法（与 Lean IsArgmaxW 口径一致）。"""
    nego = _nego()
    assert set(R.ir_set(nego)) == {"x", "y"}
    empty = R.MultiIssueNegotiation(
        agreements=("only",),
        utilities={"P1": {"only": F(0)}, "P2": {"only": F(0)}},
        reservations={"P1": F(1), "P2": F(1)},
        weights={"P1": F(1), "P2": F(1)},
    )
    assert R.ir_set(empty) == ()
    assert R.argmax_set(empty) == ("only",)  # 可行集 argmax 保留，IR 空单列


def test_argmax_kept_full_not_unique():
    """§8.4：非凸域保留全 argmax，不冒称唯一——x/y/z 加权和同 3，
    argmax 三元素（z 未过 IR 仍在可行 argmax 内，与 Lean 可行集口径一致）。"""
    nego = _nego()
    argmax = R.argmax_set(nego)
    assert set(argmax) == {"x", "y", "z"}
    assert len(set(argmax)) == 3  # 非唯一


def test_wsum_max_is_pareto_flagship():
    """T116 旗舰实例化：正权和的最大点全是 Pareto 点
    （对照 Lean wsum_max_is_pareto）。"""
    nego = _nego()
    assert R.pareto_of_argmax(nego)
    for aid in R.argmax_set(nego):
        assert R.is_pareto(nego, aid)


@pytest.mark.parametrize('utilities,reservations,ir_expected', [
    ({}, {}, ()),
    ({"P1": {"x": F(1)}, "P2": {"x": F(0)}}, {"P1": F(0), "P2": F(0)}, ("x",)),
    ({"P1": {"x": F(0)}, "P2": {"x": F(1)}}, {"P1": F(1), "P2": F(0)}, ()),
])
def test_ir_parametrized(utilities, reservations, ir_expected):
    """参数化 IR：外部选项移动时 IR 集随之收缩/翻空。"""
    agreements = ("x",)
    if not utilities:
        utilities = {"P1": {"x": F(1)}, "P2": {"x": F(1)}}
        reservations = {"P1": F(2), "P2": F(0)}
    nego = R.MultiIssueNegotiation(
        agreements=agreements, utilities=utilities,
        reservations=reservations,
        weights={"P1": F(1), "P2": F(1)})
    assert tuple(R.ir_set(nego)) == ir_expected


def test_negotiation_fail_fast():
    """构造门 fail-fast：float、负权重、重复协议 id、缺效用面全部拒绝。"""
    with pytest.raises(TypeError):
        R.MultiIssueNegotiation(
            agreements=("x",), utilities={"P1": {"x": 0.5}},
            reservations={"P1": F(0)}, weights={"P1": F(1)})
    with pytest.raises(ValueError):
        _nego().__class__(
            agreements=("x", "x"),
            utilities={"P1": {"x": F(1)}, "P2": {"x": F(1)}},
            reservations={"P1": F(0), "P2": F(0)},
            weights={"P1": F(1), "P2": F(1)})
    with pytest.raises(ValueError):
        R.MultiIssueNegotiation(
            agreements=("x",), utilities={"P1": {"x": F(1)}},
            reservations={"P1": F(0)}, weights={"P1": F(-1)})


def test_checker_negotiation_differential_and_forged_argmax():
    """checker 差分＋拒绝门：漏掉 argmax 元素或谎报 argmax 位被拒。"""
    nego = _nego()
    ir = R.ir_set(nego)
    argmax = R.argmax_set(nego)
    pareto = {aid: R.is_pareto(nego, aid) for aid in nego.agreements}
    assert K.check_negotiation(nego, ir, argmax, pareto).ok
    assert not K.check_negotiation(
        nego, ir, ("x", "y"), pareto).ok  # 漏 z：非全 argmax
    assert K.check_argmax_flag_forge(nego, "x", True).ok
    assert not K.check_argmax_flag_forge(nego, "x", False).ok
    assert not K.check_argmax_flag_forge(nego, "ghost", True).ok


# ---------------------------------------------------------------------------
# T117：稳健行动（共享 θ 与矩形反例）
# ---------------------------------------------------------------------------


def test_shared_theta_total_identity():
    """共享 θ 下两期总收益恒 1（θ 与 1−θ 互补相消）。"""
    tree = _theta_tree()
    for s in tree.scenarios:
        assert R.eval_under_shared_theta(tree, s) == 1


def test_rectangular_forges_zero():
    """§8.4 非矩形反例：逐期各取最坏相加得 0，伪造共享 θ 稳健值 1。"""
    tree = _theta_tree()
    assert R.robust_value(tree) == 1
    assert R.rectangular_value(tree) == 0
    assert R.rectangular_value(tree) != R.robust_value(tree)


def test_box_admits_unreachable_mixture():
    """矩形逐期范围之积允许混合点 (1,1)；共享 θ 可达集只有 (0,1),(1,0)。"""
    tree = _theta_tree()
    assert R.rectangular_box_contains(tree, (F(1), F(1)))
    assert (F(1), F(1)) not in R.shared_reachable_pairs(tree)
    assert R.shared_reachable_pairs(tree) == {(F(0), F(1)), (F(1), F(0))}


def test_robust_action_all_scenarios():
    """稳健行动＝全部情景满足约束：阈值 1 全过，阈值以上不过。"""
    tree = _theta_tree()
    assert R.robust_action_ok(tree, F(1), "0")
    assert not R.robust_action_ok(tree, F(2), "0")


def test_checker_robust_differential_and_forged_equality():
    """checker 差分＋拒绝门：在矩形≠共享的实例上谎报 rect==shared 被拒。"""
    tree = _theta_tree()
    assert K.check_robust_instance(
        tree, R.robust_value(tree), R.rectangular_value(tree)).ok
    forged = K.check_robust_instance(tree, F(0), F(0))
    assert not forged.ok and any("shared" in r or "rect" in r
                                 for r in forged.reasons)
    assert K.check_box_reach_claim(tree, (F(1), F(0)), True).ok
    assert not K.check_box_reach_claim(tree, (F(1), F(1)), True).ok


# ---------------------------------------------------------------------------
# T118：信息取得与停止（VOI、Snell、非单调补证）
# ---------------------------------------------------------------------------


def test_gross_voi_nonneg_and_net_negative():
    """§8.4：毛信息价值 ≥ 0；净信息价值还减权限成本，可为负。"""
    gross, net = R.voi_gross_and_net(_info_problem())
    assert gross == F(1, 2) and gross >= 0
    assert net == F(-1, 2) and net < 0
    # 无成本时净值即毛值
    gross0, net0 = R.voi_gross_and_net(_info_problem(cost=F(0)))
    assert gross0 == net0 == F(1, 2)


def test_voi_fail_fast_bad_prior():
    with pytest.raises(ValueError):
        R.InfoAcquisition(
            states=("s1", "s2"), choices=("a1",),
            prior={"s1": F(1, 2), "s2": F(1, 4)},  # 和 3/4 ≠ 1
            utils={"a1": {"s1": F(1), "s2": F(0)}}, cost=F(0))
    with pytest.raises(TypeError):
        R.InfoAcquisition(
            states=("s1",), choices=("a1",), prior={"s1": 0.5},
            utils={"a1": {"s1": F(1)}}, cost=F(0))


def test_snell_optimality_and_existence():
    """有限期停时：Snell 值 7；策略（首次满足停分支）取到 V_0（存在性）；
    全部适应停时收益 ≤ V_0（最优性）——对照 Lean stopPayoff_le_snell /
    snell_policy_achieves。"""
    g = [F(0), F(4), F(10)]
    c = [F(1), F(2)]
    report = R.snell_optimality_report(g, c)
    assert report["v0"] == 7
    assert report["stop_at"] == 2 and report["policy_payoff"] == 7
    assert all(pay <= report["v0"] for pay in report["all_payoffs"].values())
    # 期限强制：末点必停
    assert R.snell_values(g, c) == (F(7), F(8), F(10))


def test_snell_fail_fast():
    with pytest.raises(ValueError):
        R.snell_values([F(1)], [F(1)])  # c 必须比 g 短一位
    with pytest.raises(ValueError):
        R.stopping_payoff([F(1)], [], 5)  # 越界停时


def test_nonmonotone_evidence():
    """T118 非单调补证反例（独立保留）：再取一条反向证据，信念落到 1/5，
    期望决策值 9/10 → 4/5 下降。"""
    witness = R.nonmonotone_evidence_witness()
    assert witness["after_first"] == F(9, 10)
    assert witness["after_second"] == F(4, 5)
    assert witness["after_second"] < witness["after_first"]


def test_checker_voi_and_snell_enumeration():
    """checker：VOI 链差分＋伪造负毛值被拒；Snell 用**全枚举停时**独立
    重推 V_0（与主实现的 backward induction 零函数共享）。"""
    problem = _info_problem()
    gross, net = R.voi_gross_and_net(problem)
    assert K.check_voi(problem, gross, net).ok
    assert not K.check_voi(problem, F(-1), F(-2)).ok
    g = (F(0), F(4), F(10))
    c = (F(1), F(2))
    assert K.check_snell_by_enumeration(g, c, F(7), 2).ok
    assert not K.check_snell_by_enumeration(g, c, F(8), 1).ok
    assert not K.check_snell_by_enumeration(g, c, F(7), 1).ok
    witness = R.nonmonotone_evidence_witness()
    assert K.check_nonmonotone_witness(
        witness["after_first"], witness["after_second"]).ok
    assert not K.check_nonmonotone_witness(F(1, 5), F(9, 10)).ok


# ---------------------------------------------------------------------------
# T119：行为评价（同轨迹三投影）
# ---------------------------------------------------------------------------


def test_three_readings_of_same_trace():
    """三条投影读同一轨迹：因果 8、责任 {9}（特权 7 击败）、效用 7/8。"""
    trace = _defense_trace()
    assert R.causal_reading(trace) == 8
    assert R.liable_actors(trace) == frozenset({"9"})
    assert R.utility_reading(trace, "7") == 0
    assert R.utility_reading(trace, "9") == 8


def test_projection_separation():
    """T119 旗舰实例化：同轨迹不同投影结论不同——致害发生（8>0）而
    行为人 7 不担责（特权防卫），效用读数又是第三个数。"""
    witness = R.projection_separation_witness()
    assert witness["causal"] == 5 and witness["causal"] > 0
    assert witness["liable"] == frozenset()
    assert witness["utility7"] == 0
    assert witness["causal"] != witness["utility7"]


def test_act_fail_fast_negative_harm():
    with pytest.raises(ValueError):
        R.Act("1", False, F(-1), F(0))
    with pytest.raises(TypeError):
        R.Act("1", False, 0.5, F(0))


def test_checker_trace_readings_and_separation_gate():
    """checker 差分＋拒绝门：无特权致害的轨迹谎报投影分离被拒。"""
    trace = _defense_trace()
    report = K.check_trace_readings(
        trace, R.causal_reading(trace), R.liable_actors(trace),
        {a.actor: R.utility_reading(trace, a.actor) for a in trace})
    assert report.ok
    assert K.check_separation_gate(trace, True).ok
    plain = (R.Act("9", False, F(3), F(8)),)
    assert not K.check_separation_gate(plain, True).ok
    assert not K.check_trace_readings(
        plain, F(3), frozenset(), {"9": F(0)}).ok  # 效用谎报被拒


# ---------------------------------------------------------------------------
# T120：合规激励（含实际违规行动及制裁/执行）
# ---------------------------------------------------------------------------


def test_compliance_dominance_strong_deterrence():
    """达标数值例：罚 12×执行 1/2 → 违规期望 4 < 合规 5——合规占优。"""
    report = R.compliance_report(_strong_game())
    assert report["sup_permitted"] == 5
    assert report["sup_violating"] == 4
    assert report["compliance_dominates"] is True


def test_deterrence_can_fail_weak_sanction():
    """T120 反例（独立保留）：罚 4×执行 1/2 → 违规期望 8 > 合规 5——占优
    条件可失败；违规行动保留在行动空间内参与比较。"""
    report = R.compliance_report(_weak_game())
    assert report["sup_permitted"] == 5
    assert report["sup_violating"] == 8
    assert report["compliance_dominates"] is False
    assert any(not a.permitted for a in _weak_game().actions)


def test_violation_side_cannot_be_deleted():
    """§8.5：不能删掉违规选项制造定理——纯合规行动表的构造被 fail-fast
    拒绝。"""
    with pytest.raises(ValueError, match="violating"):
        R.ComplianceGame((
            R.ComplianceAction("comply", True, F(5), F(0), F(0)),
        ))


def test_compliance_fail_fast_params():
    """制裁/执行参数 fail-fast：概率出界、负罚额、float 全部拒绝。"""
    with pytest.raises(ValueError):
        R.ComplianceAction("v", False, F(10), F(4), F(3, 2))
    with pytest.raises(ValueError):
        R.ComplianceAction("v", False, F(10), F(-1), F(1, 2))
    with pytest.raises(TypeError):
        R.ComplianceAction("v", False, F(10), F(4), 0.5)


def test_checker_compliance_differential_and_forge():
    """checker 差分＋拒绝门：篡改占优结论或两侧 sup 被拒。"""
    for game in (_strong_game(), _weak_game()):
        report = R.compliance_report(game)
        assert K.check_compliance(game, report).ok
    forged = dict(R.compliance_report(_weak_game()))
    forged["compliance_dominates"] = True
    assert not K.check_compliance(_weak_game(), forged).ok
    forged2 = dict(R.compliance_report(_strong_game()))
    forged2["sup_violating"] = F(3)
    assert not K.check_compliance(_strong_game(), forged2).ok


# ---------------------------------------------------------------------------
# T121：行为回流（事件→观察→同一规则重新评价）
# ---------------------------------------------------------------------------


def test_backflow_chain_flips_verdict():
    """T121 旗舰实例化：事件把观察 5 推到 11，同一规则（阈 10）前后结论
    false→true 翻转；规则本身未被替换。"""
    receipt = R.backflow_witness()
    assert receipt["verdict_before"] is False
    assert receipt["verdict_after"] is True
    assert receipt["flipped"] is True
    assert receipt["obs_after"]["k"] == 11
    assert receipt["rule_replaced"] is False


def test_backflow_no_flip_below_threshold():
    """观察更新但未过阈：同一规则结论不翻转（更新≠结论）。"""
    receipt = R.backflow_chain(
        {"k": F(1)}, R.BehaviorEvent("k", F(2), True),
        R.ThresholdRule("k", F(10)))
    assert receipt["flipped"] is False
    assert receipt["verdict_before"] is False
    assert receipt["verdict_after"] is False
    assert receipt["obs_after"]["k"] == 3


def test_unauthorized_event_recorded_not_rule():
    """§9.4：无权限事件照实记录（观察层照常可见更新），但规则永不因行为
    事件替换。"""
    receipt = R.backflow_chain(
        {"k": F(5)}, R.BehaviorEvent("k", F(6), False),
        R.ThresholdRule("k", F(10)))
    assert receipt["flipped"] is True
    assert receipt["rule_replaced"] is False
    assert receipt["event_authorized"] is False


def test_event_fail_fast():
    with pytest.raises(ValueError):
        R.BehaviorEvent("k", F(-1), True)
    with pytest.raises(TypeError):
        R.BehaviorEvent("k", 1.5, True)


def test_checker_backflow_differential_and_forges():
    """checker 差分＋拒绝门：谎报规则被替换/篡改观察层/错报翻转被拒。"""
    obs = {"k": F(5)}
    event = R.BehaviorEvent("k", F(6), True)
    rule = R.ThresholdRule("k", F(10))
    receipt = R.backflow_chain(obs, event, rule)
    assert K.check_backflow(obs, event, rule, receipt).ok
    forged = dict(receipt)
    forged["rule_replaced"] = True
    assert not K.check_backflow(obs, event, rule, forged).ok
    forged2 = dict(receipt)
    forged2["obs_after"] = {"k": F(100)}
    assert not K.check_backflow(obs, event, rule, forged2).ok
    forged3 = dict(receipt)
    forged3["flipped"] = False
    assert not K.check_backflow(obs, event, rule, forged3).ok
    # 无权限事件同样只改观察层（checker 独立复算）
    receipt2 = R.backflow_chain(obs, R.BehaviorEvent("k", F(6), False), rule)
    assert K.check_backflow(obs, R.BehaviorEvent("k", F(6), False), rule,
                            receipt2).ok


# ---------------------------------------------------------------------------
# 独立 checker 与主实现的零函数共享审计
# ---------------------------------------------------------------------------


def test_checker_shares_no_functions():
    """checker 只 import 冻结载体（dataclass），不 import 主实现任何函数。"""
    import inspect
    from tools.full_math.implementation import behavior_check
    src = inspect.getsource(behavior_check)
    for fn in ("weighted_sum", "ir_set", "argmax_set", "dominates",
               "is_pareto", "eval_under_shared_theta", "robust_value",
               "rectangular_value", "voi_gross_and_net", "snell_values",
               "dec_value", "causal_reading", "liable_actors",
               "utility_reading", "expected_utility", "compliance_report",
               "apply_event_obs", "rule_eval", "backflow_chain"):
        assert f"R.{fn}" not in src
        assert f"behavior_ref.{fn}" not in src


# ---------------------------------------------------------------------------
# 合成回执：completion/validate 六件套收口 W4:T116..T121
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


CONTRACT_NAME = 'JurisLean.Seams.UnifiedW4Behavior'

LEAN_PROOF = ('proofs/lean/juris_lean/JurisLean/Seams/'
              'UnifiedW4Behavior.lean')
IMPL_ENTRY = 'tools/full_math/implementation/behavior_ref.py'
IMPL_CHECK = 'tools/full_math/implementation/behavior_check.py'
DOWNSTREAM = 'tools/unified_math_v2/unified/process.py'
DOWNSTREAM_TEST = ('tools/unified_math_v2/tests/'
                   'test_behavior_backflow_w4.py')
THIS = 'tools/full_math/implementation_tests/test_behavior_w4.py'


def _receipt_row(t_id, theorem, test_ids, negative_ids):
    return {
        'id': t_id,
        'theorem': theorem,
        'contract': CONTRACT_NAME,
        'proof_mode': 'KERNEL_CONTRACT_PROOF',
        'generality': 'PARAMETRIC_OVER_FINITE_ACTION_AND_SCENARIO_SETS',
        'formal_scope': 'T116 negotiation over finite agreement sets with '
                        'direct IR and full argmax; T117 shared-theta '
                        'scenario trees of finite depth with the '
                        'theta/(1-theta) closed-form counterexample; T118 '
                        'gross/net VOI with permission cost and the '
                        'finite-horizon Snell recursion; T119 three '
                        'readings of one finite trace; T120 compliance '
                        'comparison over finite physical action spaces '
                        'including the violating side; T121 backflow over '
                        'finite observation layers',
        'independent_semantics': 'behavior_check.py inline re-derivation '
                                 '(IR/argmax/Pareto enumeration, shared vs '
                                 'rectangular values, VOI chain, Snell by '
                                 'full stop-rule enumeration, three trace '
                                 'projections, compliance sups, backflow '
                                 'chain), shares frozen carriers only',
        'algorithm': 'behavior_ref.py constructors and entries: '
                     'ir_set/argmax_set/is_pareto, robust_value/'
                     'rectangular_value, voi_gross_and_net, snell_values/'
                     'snell_optimality_report, causal_reading/'
                     'liable_actors/utility_reading, compliance_report, '
                     'backflow_chain',
        'observation_contract': 'negotiation solution sets; robust vs '
                                'rectangular values with reachable-pair '
                                'sets; (gross, net) VOI and Snell value '
                                'vectors with policy receipts; per-trace '
                                'reading dictionaries; compliance verdict '
                                'reports; backflow chain receipts',
        'external_assumptions': 'synthetic scenarios only; no real statute '
                                'force is asserted (制裁/执行参数为合成'
                                '登记值)；gross-VOI witness function is a '
                                'named hypothesis, not a constructed argmax',
        'proof_sources': [LEAN_PROOF],
        'implementation_sources': [IMPL_ENTRY, IMPL_CHECK, DOWNSTREAM],
        'test_ids': test_ids,
        'negative_test_ids': negative_ids,
        'semantic_links': [CONTRACT_NAME],
    }


T_THEOREMS = {
    'W4:T116': 'JurisLean.Seams.UnifiedW4Behavior.wsum_max_is_pareto',
    'W4:T117': 'JurisLean.Seams.UnifiedW4Behavior.'
               'shared_theta_not_rectangular',
    'W4:T118': 'JurisLean.Seams.UnifiedW4Behavior.snell_policy_achieves',
    'W4:T119': 'JurisLean.Seams.UnifiedW4Behavior.projection_separation',
    'W4:T120': 'JurisLean.Seams.UnifiedW4Behavior.compliance_dominance',
    'W4:T121': 'JurisLean.Seams.UnifiedW4Behavior.backflow_chain_general',
}

_POSITIVE = {
    'W4:T116': [f'{THIS}::test_wsum_max_is_pareto_flagship',
                f'{THIS}::test_argmax_kept_full_not_unique'],
    'W4:T117': [f'{THIS}::test_shared_theta_total_identity',
                f'{DOWNSTREAM_TEST}::test_process_backflow_same_rule_reeval'],
    'W4:T118': [f'{THIS}::test_snell_optimality_and_existence',
                f'{THIS}::test_gross_voi_nonneg_and_net_negative'],
    'W4:T119': [f'{THIS}::test_projection_separation',
                f'{DOWNSTREAM_TEST}::'
                'test_process_layer_three_readings_of_one_history'],
    'W4:T120': [f'{THIS}::test_compliance_dominance_strong_deterrence'],
    'W4:T121': [f'{THIS}::test_backflow_chain_flips_verdict',
                f'{DOWNSTREAM_TEST}::test_process_backflow_same_rule_reeval'],
}

_NEGATIVE = {
    'W4:T116': [f'{THIS}::test_ir_set_direct_and_empty'],
    'W4:T117': [f'{THIS}::test_rectangular_forges_zero'],
    'W4:T118': [f'{THIS}::test_nonmonotone_evidence'],
    'W4:T119': [f'{THIS}::test_checker_trace_readings_and_separation_gate'],
    'W4:T120': [f'{THIS}::test_deterrence_can_fail_weak_sanction'],
    'W4:T121': [f'{THIS}::test_checker_backflow_differential_and_forges'],
}


@pytest.mark.parametrize('t_id', list(T_THEOREMS),
                         ids=list(T_THEOREMS))
def test_completion_receipt(t_id):
    """validate_binding 回执：W4:T116..T121 逐项过合同
    （KERNEL_CONTRACT_PROOF＋六字段＋正反例分离＋repo 实盘文件存在）。"""
    row = _receipt_row(t_id, T_THEOREMS[t_id], _POSITIVE[t_id],
                       _NEGATIVE[t_id])
    C.validate_binding(row, {'id': row['id'],
                             'theorem': T_THEOREMS[t_id],
                             'contract': row['contract']}, repo=REPO)


def test_completion_receipt_negative_tampered():
    """篡改 proof_mode 被拒：固定反例不是全量计划证明。"""
    row = _receipt_row('W4:T116', T_THEOREMS['W4:T116'],
                       _POSITIVE['W4:T116'], _NEGATIVE['W4:T116'])
    row['proof_mode'] = 'FIXED_EXAMPLE_NOT_PROOF'
    with pytest.raises(C.EvidenceError):
        C.validate_binding(row, {'id': row['id'],
                                 'theorem': T_THEOREMS['W4:T116'],
                                 'contract': row['contract']})


def test_receipt_positive_negative_disjoint():
    for t_id in T_THEOREMS:
        row = _receipt_row(t_id, T_THEOREMS[t_id], _POSITIVE[t_id],
                           _NEGATIVE[t_id])
        assert not set(row['test_ids']) & set(row['negative_test_ids'])


def test_receipt_anchors_resolve():
    """回执锚点实盘：引用的 Lean 定理与本模块测试节点都真实存在。"""
    for theorem in T_THEOREMS.values():
        assert _lean_has(theorem)
    tests = _test_functions_of_this_module()
    for name in ('test_wsum_max_is_pareto_flagship',
                 'test_rectangular_forges_zero',
                 'test_snell_optimality_and_existence',
                 'test_projection_separation',
                 'test_deterrence_can_fail_weak_sanction',
                 'test_backflow_chain_flips_verdict',
                 'test_nonmonotone_evidence'):
        assert name in tests
    assert (REPO / DOWNSTREAM_TEST).is_file()
