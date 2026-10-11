"""T112-T115 W4 games layer tests (K rows 2541-2544).

T112 量刑双线: the normative domain bounds the prevention line (composition
always lands in-domain via the clip; raw out-of-domain empirical values are
rejected); penalty kinds are a three-way enum; same-source certificate gates
reject foreign-facts pairs (the row's original counterexample, kept
independently).
T113 动态谈判: two-round alternating-offer backward induction — last round
first, then the root; single-step deviation check over all four subgame
nodes; tampered offers (bid rigging) rejected by the independent checker.
T114 隐藏信息与信念: path-Bayes pins reachable beliefs (inconsistent beliefs
rejected); off-path beliefs must stay in support; all continuation deviations
covered by the pure-plan check plus the convexity identity.
T115 重复博弈: finite tail bound (closed form vs summation, differential);
over-bound tail sums rejected; one-deviation principle; grim-trigger
credible punishment threshold δ ≥ (T−R)/(T−P).
Plus the independent-checker differentials and the completion/validate
receipts for the six-piece closure (W4:T112..T115).
"""
import ast
import importlib.util
from fractions import Fraction as Q
from pathlib import Path

import pytest

from tools.full_math.implementation import games_ref as R
from tools.full_math.implementation import games_check as K

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[2]


def _load_completion():
    """Load tools/full_math/completion.py by explicit path — NO sys.path
    insert: tools/full_math carries a `reference` package that would shadow
    tools/unified_math_v2/reference in a shared pytest process."""
    path = REPO / 'tools/full_math/completion.py'
    spec = importlib.util.spec_from_file_location('completion_t112_115',
                                                  str(path))
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


C = _load_completion()

LEAN_MODULE = (REPO / 'proofs/lean/juris_lean/JurisLean/Seams/'
               'UnifiedW4Games.lean')


# ---------------------------------------------------------------------------
# 合成材料（全部 ℚ；无浮点）
# ---------------------------------------------------------------------------

DOMAIN = R.NormDomain(months_lo=Q(10), months_hi=Q(60),
                      allows_life=False, allows_death=False)
EMP_HIGH = R.EmpPrediction(base=Q(70), span=Q(10), value=Q(75))
EMP_OK = R.EmpPrediction(base=Q(12), span=Q(8), value=Q(20))

CERT_RESP = R.SentCert('cert-1', 'facts-100', R.LineKind.RESPONSIBILITY,
                       R.mk_fixed(Q(30)))
CERT_PREV = R.SentCert('cert-2', 'facts-100', R.LineKind.PREVENTION,
                       R.mk_fixed(Q(36)))
CERT_PREV_FOREIGN = R.SentCert('cert-3', 'facts-200', R.LineKind.PREVENTION,
                               R.mk_fixed(Q(36)))

BARGAIN = R.BargainParams(cake=Q(100), delta=Q(1, 2),
                          offers_x=(Q(40), Q(60)), offers_y=(Q(20), Q(50)))

DEMO_GAME = R.SigGame(
    prior=Q(1, 2),
    pay_l_u=(Q(2), Q(2)), pay_l_d=(Q(1), Q(1)),
    pay_h_u=(Q(1), Q(1)), pay_h_d=(Q(0), Q(0)),
    us_l_u=(Q(3), Q(3)), us_l_d=(Q(0), Q(0)),
    us_h_u=(Q(1), Q(1)), us_h_d=(Q(0), Q(0)))
POOL_S = (True, True)      # 两型同发 L（池化）
ALWAYS_U = (True, True)    # 接收者在两信息集都选 u
MU_HALF = R.Belief(Q(1, 2))


# ---------------------------------------------------------------------------
# T112: 量刑双线
# ---------------------------------------------------------------------------


def test_penalty_kinds_distinct_not_one_number_line():
    """§11.3.10：Term(months)、无期、死刑是不同类，不用 −1/−2 混算——
    分型值对象互不相交（对照 Lean penalty_exhaust/penalty_pairwise_ne）。"""
    fixed = R.mk_fixed(Q(30))
    life = R.mk_life()
    death = R.mk_death()
    assert fixed.kind != life.kind != death.kind
    assert life.months is None and death.months is None
    assert fixed.months == Q(30)
    with pytest.raises(ValueError):
        R.Penalty(R.PenaltyKind.LIFE, Q(12))  # 无期不携带月数（分型不相交）


def test_norm_domain_and_penalty_construction_fail_fast():
    """构造门 fail-fast：域倒置、浮点、越界经验值、unknown kind 一律拒绝。"""
    with pytest.raises(ValueError):
        R.NormDomain(months_lo=Q(60), months_hi=Q(10), allows_life=False,
                     allows_death=False)
    with pytest.raises(ValueError):
        R.NormDomain(months_lo=10.5, months_hi=Q(60), allows_life=False,
                     allows_death=False)
    with pytest.raises(ValueError):
        R.mk_fixed(30.5)  # 浮点月数拒绝
    with pytest.raises(ValueError):
        R.EmpPrediction(base=Q(0), span=Q(10), value=Q(11))  # 越自身界
    with pytest.raises(ValueError):
        R.Penalty('forever')


@pytest.mark.parametrize('r,t,expected', [
    (Q(25), Q(40), Q(60)),    # 越上界 → 裁回 60
    (Q(25), Q(-30), Q(10)),   # 越下界 → 裁回 10
    (Q(25), Q(10), Q(35)),    # 域内 → 不扭曲
    (Q(10), Q(0), Q(10)),     # 贴下界 → 不扭曲
])
def test_dual_line_composition_stays_normative(r, t, expected):
    """§8.6/11.3.10：双线合成恒在规范域内（预防线调整不得越出责任刑边界），
    域内合成不扭曲（对照 Lean dual_line_stays_normative/clip_in_domain/
    clip_fix_in_domain）。"""
    layer = R.build_sentencing_layer(DOMAIN, r, t, [])
    assert layer.composed_penalty.months == expected
    assert layer.in_domain
    assert layer.unclipped_in_domain == (r + t == expected)


def test_empirical_cannot_rewrite_statutory_range():
    """§8.6：经验拟合不反向修改法定范围——预测 75 在自身值域内但越出法定域：
    裸值判不在域，只有裁剪（60）可入域（对照 Lean empirical_outside_needs_clip
    与见证 empHighDemo）。"""
    assert R.penalty_in_domain(DOMAIN, R.mk_fixed(EMP_HIGH.value)) is False
    clipped = R.clip_to(DOMAIN, EMP_HIGH.value)
    assert clipped == Q(60)
    assert R.penalty_in_domain(DOMAIN, R.mk_fixed(clipped)) is True
    layer = R.build_sentencing_layer(DOMAIN, Q(70), Q(5), [])
    assert layer.composed_penalty.months == Q(60) and layer.in_domain


def test_same_source_gate_accepts_and_foreign_rejected():
    """T112 原反例（独立保留）：同源双线过门；异源（factsId 不同）被拒
    （对照 Lean composeGateB_rejects_foreign_facts/witness_foreign_facts_rejected）。"""
    assert R.compose_gate(CERT_RESP, CERT_PREV)
    assert not R.compose_gate(CERT_RESP, CERT_PREV_FOREIGN)
    layer = R.build_sentencing_layer(
        DOMAIN, Q(25), Q(6), [CERT_RESP, CERT_PREV, CERT_PREV_FOREIGN])
    assert ('cert-1', 'cert-2') in layer.same_source_pairs
    assert ('cert-1', 'cert-3') in layer.foreign_pairs
    assert K.check_sentencing_layer(DOMAIN, Q(25), Q(6),
                                    [CERT_RESP, CERT_PREV, CERT_PREV_FOREIGN],
                                    layer).ok


def test_checker_rejects_forged_sentencing_layer():
    """checker 独立差分：伪造合成刑（裁剪被绕过）与伪造异源对被拒。"""
    layer = R.build_sentencing_layer(DOMAIN, Q(25), Q(40), [CERT_RESP])
    forged = R.SentencingLayer(
        domain=layer.domain, composed_penalty=R.mk_fixed(Q(65)),
        in_domain=True, unclipped_in_domain=True,
        same_source_pairs=layer.same_source_pairs,
        foreign_pairs=(('cert-1', 'ghost'),))
    report = K.check_sentencing_layer(DOMAIN, Q(25), Q(40), [CERT_RESP], forged)
    assert not report.ok
    assert any('clip projection' in r for r in report.reasons)
    assert any('foreign-facts' in r for r in report.reasons)


# ---------------------------------------------------------------------------
# T113: 动态谈判（后向归纳）
# ---------------------------------------------------------------------------


def test_backward_induction_numeric_demo():
    """合成数值例（对照 Lean bParamsDemo/witness_bargain_bi）：末轮 y=20
    （B 得 40 > 25），门槛 40 ≥ δ·40=20，A 取 40 → 结果 (60, 40)。"""
    res = R.backward_induction(BARGAIN)
    assert res.b1 == Q(20)
    assert res.r1_value == (Q(10), Q(40))
    assert res.a0 == Q(40)
    assert res.outcome == (Q(60), Q(40))
    assert all(not c.endswith(':FAIL') for c in res.sp_checks)
    assert len(res.sp_checks) == 4
    assert K.check_bargain_result(BARGAIN, res).ok


@pytest.mark.parametrize('delta,x1,x2,y1,y2', [
    (Q(1, 3), Q(10), Q(50), Q(5), Q(30)),     # 大蛋糕差距
    (Q(1), Q(60), Q(40), Q(50), Q(20)),       # δ=1（菜单顺序反转）
    (Q(0), Q(40), Q(40), Q(20), Q(20)),       # 退化折扣：全部平局
    (Q(3, 4), Q(-5), Q(10), Q(-20), Q(15)),   # 负报价：末轮两拒 → (0,0) 延续
])
def test_backward_induction_parametrized(delta, x1, x2, y1, y2):
    """参数化后向归纳：任何参数下四节点单步偏离检查都通过，且独立 checker
    复核通过（存在性由构造见证；SP 面由检查器闭合）。"""
    p = R.BargainParams(cake=Q(80), delta=delta,
                        offers_x=(x1, x2), offers_y=(y1, y2))
    res = R.backward_induction(p)
    assert res.b1 in p.offers_y and res.a0 in p.offers_x
    assert all(not c.endswith(':FAIL') for c in res.sp_checks)
    assert K.check_bargain_result(p, res).ok


def test_checker_rejects_bid_rigging():
    """T113 拒绝门（原反例面）：篡改出价（把非收益最大化报价报成 BI 选择）
    被独立 checker 拒绝。"""
    res = R.backward_induction(BARGAIN)
    rigged = R.BIResult(b1=Q(50), a0=res.a0, outcome=res.outcome,
                        r1_value=res.r1_value, sp_checks=res.sp_checks,
                        strict_no_indifference=res.strict_no_indifference)
    report = K.check_bargain_result(BARGAIN, rigged)
    assert not report.ok
    assert any('round-1 proposer choice tampered' in r for r in report.reasons)
    rigged_root = R.BIResult(b1=res.b1, a0=Q(60), outcome=res.outcome,
                             r1_value=res.r1_value, sp_checks=res.sp_checks,
                             strict_no_indifference=res.strict_no_indifference)
    report = K.check_bargain_result(BARGAIN, rigged_root)
    assert not report.ok
    assert any('root proposer choice tampered' in r for r in report.reasons)


def test_bi_outcome_unique_under_menu_maximization():
    """唯一类定理的 Python 面：任一在菜单上最大化 A 第一分量收益的报价产出
    同一结果（对照 Lean bi_outcome_unique）；严格性标记在无差异边缘为 False。"""
    res = R.backward_induction(BARGAIN)
    for x in BARGAIN.offers_x:
        if R.r0_pay(BARGAIN, x)[0] == res.outcome[0]:
            assert R.r0_pay(BARGAIN, x) == res.outcome
    assert res.strict_no_indifference  # 数值例无差异边缘被排除


# ---------------------------------------------------------------------------
# T114: 隐藏信息与信念
# ---------------------------------------------------------------------------


def test_pooling_seq_eq_passes_all_components():
    """池化均衡见证（对照 Lean demoGame/witness_pooling_seq_eq）：一致性、
    接收者两信息集最优回应、发送者两型最优回应全部通过。"""
    rep = R.seq_eq_check(DEMO_GAME, POOL_S, ALWAYS_U, MU_HALF, MU_HALF)
    assert rep.ok and rep.reasons == ()
    assert all((rep.consistent_l, rep.consistent_h, rep.receiver_br_l,
                rep.receiver_br_h, rep.sender_br_strong, rep.sender_br_weak))
    assert K.check_beliefs_and_seq(DEMO_GAME, POOL_S, ALWAYS_U, MU_HALF,
                                   MU_HALF, rep).ok


def test_inconsistent_onpath_belief_rejected():
    """T114 原反例（独立保留）：池化下 L 可达，路径贝叶斯钉定 μL＝先验 1/2；
    谎报 9/10 被拒（对照 Lean witness_inconsistent_mu_rejected）。"""
    liar = R.Belief(Q(9, 10))
    rep = R.seq_eq_check(DEMO_GAME, POOL_S, ALWAYS_U, liar, MU_HALF)
    assert not rep.ok and any('path Bayes' in r for r in rep.reasons)
    assert not K.check_beliefs_and_seq(DEMO_GAME, POOL_S, ALWAYS_U, liar,
                                       MU_HALF, rep).ok


def test_offpath_belief_must_stay_in_support():
    """T114 原反例（独立保留）：H 离轨只要求支撑内良构——3/2 越界被拒
    （不能任填 0/0，对照 Lean witness_offpath_unnormalized_rejected）。"""
    crazy = R.Belief(Q(3, 2))
    assert not R.belief_wf(crazy)
    rep = R.seq_eq_check(DEMO_GAME, POOL_S, ALWAYS_U, MU_HALF, crazy)
    assert not rep.ok and any('inconsistent/off-support' in r
                              for r in rep.reasons)
    ok_offpath = R.Belief(Q(4, 5))  # 离轨支撑内任一点：在闭包内
    assert R.seq_eq_check(DEMO_GAME, POOL_S, ALWAYS_U, MU_HALF,
                          ok_offpath).ok


def test_onpath_belief_pinned_unique():
    """可达信息集上信念被路径贝叶斯唯一钉定（对照 Lean
    consistentB_on_path_pins）：两型同发 ⇒ 后验必为先验，唯一无自由度。"""
    assert R.bayes_mu_strong(DEMO_GAME, POOL_S, True) == Q(1, 2)
    assert R.bayes_mu_strong(DEMO_GAME, POOL_S, False) is None
    sep = (True, False)  # 分离：L 只有强型发
    assert R.bayes_mu_strong(DEMO_GAME, sep, True) == Q(1)
    assert R.bayes_mu_strong(DEMO_GAME, sep, False) == Q(0)
    assert R.consistent(DEMO_GAME, sep, True, R.Belief(Q(1)))
    assert not R.consistent(DEMO_GAME, sep, True, R.Belief(Q(1, 2)))


def test_all_mixed_continuation_deviations_covered():
    """全部延续偏离无益（对照 Lean receiver_all_continuation_no_gain）：
    纯计划检查通过后，任意凸组合（混合偏离）也不增收益——数值核验 w=2/5。"""
    mu = Q(1, 2)
    eu_u = R.eu_r(DEMO_GAME, True, R.Belief(mu), True)
    eu_d = R.eu_r(DEMO_GAME, True, R.Belief(mu), False)
    assert eu_u == Q(2) and eu_d == Q(1)
    for w in (Q(0), Q(1, 5), Q(2, 5), Q(4, 5), Q(1)):
        mixed = w * eu_u + (1 - w) * eu_d
        assert mixed <= eu_u


def test_checker_rejects_forged_seq_report():
    """checker 差分：把不合格剖面报成 ok=True 的伪造读数被拒。"""
    liar = R.Belief(Q(9, 10))
    rep = R.seq_eq_check(DEMO_GAME, POOL_S, ALWAYS_U, liar, MU_HALF)
    forged = R.SeqEqReport(consistent_l=True, consistent_h=rep.consistent_h,
                           receiver_br_l=rep.receiver_br_l,
                           receiver_br_h=rep.receiver_br_h,
                           sender_br_strong=rep.sender_br_strong,
                           sender_br_weak=rep.sender_br_weak,
                           ok=True, reasons=())
    report = K.check_beliefs_and_seq(DEMO_GAME, POOL_S, ALWAYS_U, liar,
                                     MU_HALF, forged)
    assert not report.ok and any('path Bayes' in r for r in report.reasons)


# ---------------------------------------------------------------------------
# T115: 无限重复折扣
# ---------------------------------------------------------------------------


def test_tail_bound_instances_exact():
    """尾界（对照 Lean tail_bound/tail_bound_mul）：多组 (δ, M, N, k) 的
    |Σ|·(1−δ) ≤ M·δ^N 精确成立（惩罚流每期 2、δ=2/3 的见证含在参数内）。"""
    cases = [
        (Q(2, 3), Q(2), Q(2), 1, 5),
        (Q(1, 2), Q(3), Q(3), 0, 7),
        (Q(1, 3), Q(4), Q(-4), 2, 6),   # 负收益流：绝对值尾界同形
        (Q(9, 10), Q(1), Q(1), 10, 3),
    ]
    for delta, m, per, big_n, k in cases:
        u = (lambda per: lambda t: per)(per)
        lhs, rhs, ok = R.tail_bound(delta, m, u, big_n, k)
        assert ok, (delta, m, big_n, k)
        report = K.check_tail_bound(delta, m, per, big_n, k, lhs, rhs, ok)
        assert report.ok, report.reasons


def test_tail_bound_rejects_over_bound_claim():
    """T115 拒绝门：把超界尾和报成可接受被独立 checker 拒绝。"""
    delta, m, per = Q(9, 10), Q(1), Q(1)
    lhs, rhs, ok = R.tail_bound(delta, m, lambda _: per, 0, 30)
    assert lhs <= rhs and ok
    report = K.check_tail_bound(delta, m, per, 0, 30, lhs, rhs, False)
    assert not report.ok and any('acceptable' in r for r in report.reasons)
    # 闭式路径差分：篡改 lhs 立即暴露
    report = K.check_tail_bound(delta, m, per, 0, 30, lhs + Q(1, 7), rhs, True)
    assert not report.ok and any('closed-form' in r for r in report.reasons)


def test_one_deviation_principle_streams():
    """离轨单偏离原理（对照 Lean one_dev_principle）：任何单期替换都不获利
    ⇒ 窗口内偏离的整体流不获利；任一单期替换获利即 fail-closed。"""
    delta = Q(1, 2)

    def g_profit(t: int, joint: bool) -> Q:
        # 合作流每期 0，单期改判偏离得 3：单期替换获利 → fail-closed
        return Q(0) if joint else Q(3)

    a = lambda t: True
    b = lambda t: t != 2
    ok, reasons = R.one_dev_report(delta, g_profit, a, b, 6)
    assert not ok
    assert any('single deviation at 2' in r for r in reasons)

    def g_lose(t: int, joint: bool) -> Q:
        # 合作流每期 2、偏离只值 1：单期替换全不获利
        return Q(2) if joint else Q(1)

    c = lambda t: True
    d = lambda t: t != 2
    ok2, reasons2 = R.one_dev_report(delta, g_lose, c, d, 6)
    assert ok2 and reasons2 == ()


def test_coop_threshold_and_credibility():
    """可信惩罚阈值（对照 Lean coop_threshold_iff/见证）：R=3, T=4, P=2 →
    δ* = 1/2；δ=2/3 维持、δ=1/3 背离；惩罚路径必须在许可行动集内。"""
    assert R.coop_threshold(Q(3), Q(4), Q(2)) == Q(1, 2)
    assert R.grim_sustains(Q(3), Q(4), Q(2), Q(2, 3))
    assert not R.grim_sustains(Q(3), Q(4), Q(2), Q(1, 3))
    assert R.punish_credible(lambda _a: True)
    assert not R.punish_credible(lambda a: a)  # 惩罚行动 false 不在许可集
    report = K.check_threshold(Q(3), Q(4), Q(2), Q(2, 3), Q(1, 2), True, True)
    assert report.ok
    forged = K.check_threshold(Q(3), Q(4), Q(2), Q(1, 3), Q(1, 2), True, True)
    assert not forged.ok  # δ=1/3 不维持却被报成维持 → 拒绝
    no_cred = K.check_threshold(Q(3), Q(4), Q(2), Q(2, 3), Q(1, 2), True, False)
    assert not no_cred.ok and any('non-permitted punishment' in r
                                  for r in no_cred.reasons)


def test_threshold_requires_t_greater_p():
    """T ≤ P 时阈值无定义（fail-fast，对照 Lean coop_threshold_iff 前提
    hTP : P < T）。"""
    with pytest.raises(ValueError):
        R.coop_threshold(Q(3), Q(4), Q(5))
    report = K.check_threshold(Q(3), Q(4), Q(4), Q(2, 3), Q(1, 2), True, True)
    assert not report.ok and any('T ≤ P' in r for r in report.reasons)


# ---------------------------------------------------------------------------
# 层总装与回执（completion/validate 六件套收口）
# ---------------------------------------------------------------------------


def test_build_games_layer_end_to_end():
    """四件读数一次总装：域内合成、后向归纳、序贯检查、尾界＋阈值＋可信。"""
    layer = R.build_games_layer(
        DOMAIN, Q(25), Q(6), [CERT_RESP, CERT_PREV],
        BARGAIN, DEMO_GAME, POOL_S, ALWAYS_U, MU_HALF, MU_HALF,
        Q(3), Q(4), Q(2), Q(2, 3))
    assert layer.sentencing.composed_penalty.months == Q(31)
    assert layer.bargaining.outcome == (Q(60), Q(40))
    assert layer.seq_eq.ok
    assert layer.tail_ok
    assert layer.threshold == Q(1, 2)
    assert layer.sustains and layer.credible


def test_floats_rejected_everywhere():
    """ℑ 纪律：概率/金额/折扣一律 ℚ——浮点从构造器到收益表全部拒绝。"""
    with pytest.raises(ValueError):
        R.BargainParams(cake=100.5, delta=Q(1, 2),
                        offers_x=(Q(40), Q(60)), offers_y=(Q(20), Q(50)))
    with pytest.raises(ValueError):
        R.Belief(0.5)
    with pytest.raises(ValueError):
        R.SigGame(prior=0.5,
                  pay_l_u=(Q(2), Q(2)), pay_l_d=(Q(1), Q(1)),
                  pay_h_u=(Q(1), Q(1)), pay_h_d=(Q(0), Q(0)),
                  us_l_u=(Q(3), Q(3)), us_l_d=(Q(0), Q(0)),
                  us_h_u=(Q(1), Q(1)), us_h_d=(Q(0), Q(0)))
    with pytest.raises(ValueError):
        R.tail_bound(0.5, Q(1), lambda _: Q(1), 0, 3)


def _lean_has(theorem: str) -> bool:
    local = theorem.split('.')[-1]
    text = LEAN_MODULE.read_text(encoding='utf-8')
    return f'theorem {local} ' in text


def _test_functions_of_this_module():
    tree = ast.parse(Path(__file__).read_text(encoding='utf-8'))
    return {node.name for node in ast.walk(tree)
            if isinstance(node, ast.FunctionDef) and
            node.name.startswith('test_')}


CONTRACT_NAME = 'JurisLean.Seams.UnifiedW4Games'


def _receipt_row(t_id, theorem, test_ids, negative_ids):
    return {
        'id': t_id,
        'theorem': theorem,
        'contract': CONTRACT_NAME,
        'proof_mode': 'KERNEL_CONTRACT_PROOF',
        'generality': 'PARAMETRIC_OVER_FINITE_GAMES',
        'formal_scope': 'T112 sentencing dual line over ℚ normative domains '
                        'and certificate pairs; T113 two-round alternating '
                        'offers over finite menus; T114 two-type signaling '
                        'with path-Bayes beliefs; T115 discounted streams '
                        'with bounded per-period payoffs',
        'independent_semantics': 'games_check.py inline re-derivation (clip, '
                                 'backward induction, path Bayes, tail-bound '
                                 'closed form), shares frozen carriers only',
        'algorithm': 'games_ref.py mk_* constructors, clip_to, '
                     'backward_induction, seq_eq_check, tail_bound, '
                     'coop_threshold, one_dev_report',
        'observation_contract': 'SentencingLayer/BIResult/SeqEqReport/'
                                'GamesLayer snapshots plus (lhs, rhs, ok) '
                                'tail certificates',
        'external_assumptions': 'synthetic payoff tables only; no real '
                                'statute force asserted (法源/量刑域为合成 '
                                '登记值)；δ∈[0,1)、逐期收益有界为声明前提',
        'proof_sources': ['proofs/lean/juris_lean/JurisLean/Seams/'
                          'UnifiedW4Games.lean'],
        'implementation_sources': [
            'tools/full_math/implementation/games_ref.py',
            'tools/full_math/implementation/games_check.py',
        ],
        'test_ids': test_ids,
        'negative_test_ids': negative_ids,
        'semantic_links': ['JurisLean.Seams.UnifiedW4Games'],
    }


T112_THEOREM = 'JurisLean.Seams.UnifiedW4Games.dual_line_stays_normative'
T113_THEOREM = 'JurisLean.Seams.UnifiedW4Games.bi_one_step_no_gain'
T114_THEOREM = ('JurisLean.Seams.UnifiedW4Games.'
                'receiver_all_continuation_no_gain')
T115_THEOREM = 'JurisLean.Seams.UnifiedW4Games.tail_bound'


def test_completion_receipt_t112():
    row = _receipt_row(
        'W4:T112', T112_THEOREM,
        ['tools/full_math/implementation_tests/test_games_w4.py::'
         'test_dual_line_composition_stays_normative',
         'tools/full_math/implementation_tests/test_games_w4.py::'
         'test_same_source_gate_accepts_and_foreign_rejected'],
        ['tools/full_math/implementation_tests/test_games_w4.py::'
         'test_empirical_cannot_rewrite_statutory_range'])
    C.validate_binding(row, {'id': row['id'], 'theorem': T112_THEOREM,
                             'contract': row['contract']}, repo=REPO)


def test_completion_receipt_t113():
    row = _receipt_row(
        'W4:T113', T113_THEOREM,
        ['tools/full_math/implementation_tests/test_games_w4.py::'
         'test_backward_induction_numeric_demo',
         'tools/full_math/implementation_tests/test_games_w4.py::'
         'test_backward_induction_parametrized'],
        ['tools/full_math/implementation_tests/test_games_w4.py::'
         'test_checker_rejects_bid_rigging'])
    C.validate_binding(row, {'id': row['id'], 'theorem': T113_THEOREM,
                             'contract': row['contract']}, repo=REPO)


def test_completion_receipt_t114():
    row = _receipt_row(
        'W4:T114', T114_THEOREM,
        ['tools/full_math/implementation_tests/test_games_w4.py::'
         'test_pooling_seq_eq_passes_all_components',
         'tools/full_math/implementation_tests/test_games_w4.py::'
         'test_all_mixed_continuation_deviations_covered'],
        ['tools/full_math/implementation_tests/test_games_w4.py::'
         'test_inconsistent_onpath_belief_rejected',
         'tools/full_math/implementation_tests/test_games_w4.py::'
         'test_offpath_belief_must_stay_in_support'])
    C.validate_binding(row, {'id': row['id'], 'theorem': T114_THEOREM,
                             'contract': row['contract']}, repo=REPO)


def test_completion_receipt_t115():
    row = _receipt_row(
        'W4:T115', T115_THEOREM,
        ['tools/full_math/implementation_tests/test_games_w4.py::'
         'test_tail_bound_instances_exact',
         'tools/full_math/implementation_tests/test_games_w4.py::'
         'test_coop_threshold_and_credibility'],
        ['tools/full_math/implementation_tests/test_games_w4.py::'
         'test_tail_bound_rejects_over_bound_claim',
         'tools/full_math/implementation_tests/test_games_w4.py::'
         'test_threshold_requires_t_greater_p'])
    C.validate_binding(row, {'id': row['id'], 'theorem': T115_THEOREM,
                             'contract': row['contract']}, repo=REPO)


def test_completion_receipt_negative_tampered():
    """回执合同负例：proof_mode 篡改被 validate_binding 拒绝。"""
    row = _receipt_row(
        'W4:T113', T113_THEOREM,
        ['tools/full_math/implementation_tests/test_games_w4.py::'
         'test_backward_induction_numeric_demo'],
        ['tools/full_math/implementation_tests/test_games_w4.py::'
         'test_checker_rejects_bid_rigging'])
    row['proof_mode'] = 'FIXED_EXAMPLE_NOT_PROOF'
    with pytest.raises(C.EvidenceError):
        C.validate_binding(row, {'id': row['id'], 'theorem': T113_THEOREM,
                                 'contract': row['contract']})


def test_receipt_anchors_resolve():
    """回执锚点实盘：引用的 Lean 定理与本模块测试节点都真实存在。"""
    assert _lean_has(T112_THEOREM)
    assert _lean_has(T113_THEOREM)
    assert _lean_has(T114_THEOREM)
    assert _lean_has(T115_THEOREM)
    tests = _test_functions_of_this_module()
    for name in ('test_dual_line_composition_stays_normative',
                 'test_same_source_gate_accepts_and_foreign_rejected',
                 'test_backward_induction_numeric_demo',
                 'test_checker_rejects_bid_rigging',
                 'test_pooling_seq_eq_passes_all_components',
                 'test_inconsistent_onpath_belief_rejected',
                 'test_tail_bound_instances_exact',
                 'test_tail_bound_rejects_over_bound_claim'):
        assert name in tests
