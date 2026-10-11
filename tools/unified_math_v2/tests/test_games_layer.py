"""Downstream consumption of the T112-T115 W4 games layer by run_case.

The main chain (J.6.1) consumes the environment's four optional frozen
carriers (SentencingInput / games_ref.BargainParams / SignalInput /
RepetitionInput — attribute names mirror the games_ref formal parameters)
through games_ref.build_games_layer and attaches the resulting
GamesLayerSnapshot to every selection branch; any gate failure (missing
carrier, missing attribute, out-of-gate parameters) converges into the
existing technical FAILED path, never a legal verdict.  The independent
checker re-validates the attached readouts from the raw fixtures.
"""

from fractions import Fraction as Q
from unittest import TestCase

from theory.spec.canonical_v2.case import (
    CaseInput,
    Claim,
    ExactQuantity,
    FactRecord,
    FactStanding,
    LegalEnvironment,
    Polar,
    ProcessState,
    RepetitionInput,
    RunStatus,
    ScopedAtom,
    SentencingInput,
    SignalInput,
)
from theory.spec.canonical_v2.kernel import (
    Jurisdiction,
    JurisdictionRoute,
    NormState,
)
from unified.pipeline import run_case

from tools.full_math.implementation import games_check as K
from tools.full_math.implementation import games_ref as R


def _atom(predicate, polar=Polar.POS, subject="D"):
    return ScopedAtom(case_id="case-1", subject=subject, issue="loan",
                      stage="trial", predicate=predicate, polar=polar)


def _state():
    return ProcessState(
        r=NormState(relations=()),
        environment_id="env-1",
        stages=(("loan-trial", "trial"),),
        events=(),
        target_day=10,
        as_of_day=10,
    )


def _case():
    return CaseInput(
        case_id="case-1",
        initial_state=_state(),
        parties=("C", "D"),
        issues=("loan",),
        claims=(Claim("c1", "C", "D", "loan", "money", "payment"),),
        defenses=(),
        fact_records=(
            FactRecord("f-contract", _atom("contract_signed"),
                       FactStanding.ADMITTED_POSITIVE, produced_at=1,
                       known_at=1),
        ),
        evidence_records=(),
        questions=(),
        quantities=(ExactQuantity(Q(100), "CNY", "principal", "contract"),),
    )


# ---------------------------------------------------------------------------
# 合成博弈载体（全部 ℚ）
# ---------------------------------------------------------------------------

DOMAIN = R.NormDomain(months_lo=Q(10), months_hi=Q(60),
                      allows_life=False, allows_death=False)
CERT_RESP = R.SentCert('cert-1', 'facts-100', R.LineKind.RESPONSIBILITY,
                       R.mk_fixed(Q(30)))
CERT_PREV = R.SentCert('cert-2', 'facts-100', R.LineKind.PREVENTION,
                       R.mk_fixed(Q(36)))

BARGAIN = R.BargainParams(cake=Q(100), delta=Q(1, 2),
                          offers_x=(Q(40), Q(60)), offers_y=(Q(20), Q(50)))

GAME = R.SigGame(
    prior=Q(1, 2),
    pay_l_u=(Q(2), Q(2)), pay_l_d=(Q(1), Q(1)),
    pay_h_u=(Q(1), Q(1)), pay_h_d=(Q(0), Q(0)),
    us_l_u=(Q(3), Q(3)), us_l_d=(Q(0), Q(0)),
    us_h_u=(Q(1), Q(1)), us_h_d=(Q(0), Q(0)))
POOL_S = (True, True)
ALWAYS_U = (True, True)
MU_HALF = R.Belief(Q(1, 2))


def _carriers(delta=Q(2, 3), punishment_permitted=True,
              responsibility=Q(25), prevention=Q(6)):
    """四槽完整载体：量刑双线（25+6=31 在域内）、谈判数值例、池化序贯、
    Trigger R=3/T=4/P=2 与给定折扣（默认 2/3 ≥ 阈值 1/2 → 维持）。"""
    return (
        SentencingInput(domain=DOMAIN, responsibility=responsibility,
                        prevention_adjustment=prevention,
                        certs=(CERT_RESP, CERT_PREV)),
        BARGAIN,
        SignalInput(game=GAME, sS=POOL_S, sR=ALWAYS_U,
                    mu_l=MU_HALF, mu_h=MU_HALF),
        RepetitionInput(r=Q(3), t=Q(4), p=Q(2), delta=delta,
                        punishment_permitted=punishment_permitted),
    )


def _env(sentencing=None, bargain=None, signal=None, repetition=None,
         cands=()):
    return LegalEnvironment(
        environment_id="env-1",
        jurisdiction=Jurisdiction(route=JurisdictionRoute.MAINLAND),
        interpretation_candidates=tuple(cands),
        sentencing_input=sentencing,
        bargain_params=bargain,
        signal_input=signal,
        repetition_input=repetition,
    )


class GamesLayerConsumptionTests(TestCase):
    def test_no_carriers_leaves_games_layer_none(self):
        """未委托博弈分析（四槽全空）：games_layer 为 None，主链不受影响
        （加性默认，既有用例零回归）。"""
        run = run_case(_case(), _env())
        self.assertIs(run.status, RunStatus.COMPLETE)
        self.assertTrue(run.branches)
        self.assertTrue(all(b.games_layer is None for b in run.branches))
        self.assertFalse(any("repetition" in n for n in run.pending))

    def test_run_case_attaches_games_layer(self):
        """正例：四载体齐备 → Γ 级快照挂到每个 selection 分支，四槽读数
        逐一核对（域内合成 31、后向归纳 (60,40)、序贯通过、尾界/阈值/可信）。"""
        sentencing, bargain, signal, repetition = _carriers()
        env = _env(sentencing, bargain, signal, repetition)
        run = run_case(_case(), env)
        self.assertIs(run.status, RunStatus.COMPLETE)
        self.assertTrue(run.branches)
        layer = run.branches[0].games_layer
        self.assertIsNotNone(layer)
        # T112：双线合成恒在规范域内（25+6=31），同源双线过门、无异源对
        self.assertEqual(layer.sentencing.composed_penalty.months, Q(31))
        self.assertTrue(layer.sentencing.in_domain)
        self.assertIn(('cert-1', 'cert-2'), layer.sentencing.same_source_pairs)
        self.assertEqual(layer.sentencing.foreign_pairs, ())
        # T113：后向归纳读数与单步偏离检查
        self.assertEqual(layer.bargaining.b1, Q(20))
        self.assertEqual(layer.bargaining.outcome, (Q(60), Q(40)))
        self.assertTrue(all(not c.endswith(':FAIL')
                            for c in layer.bargaining.sp_checks))
        # T114：序贯检查全分量通过
        self.assertTrue(layer.seq_eq.ok)
        # T115：尾界证书、阈值 δ*、维持读数、可信门
        self.assertTrue(layer.tail_ok)
        self.assertEqual(layer.threshold, Q(1, 2))
        self.assertTrue(layer.sustains)
        self.assertTrue(layer.credible)
        # Γ-level：同一快照挂到每个分支；无博弈类 pending 注记
        self.assertTrue(
            all(b.games_layer is layer for b in run.branches))
        self.assertFalse(any("repetition" in n for n in run.pending))

    def test_attached_layer_passes_independent_checker(self):
        """下游消费差分：挂接的四槽读数被独立 checker 从原始载体重算认可。"""
        sentencing, bargain, signal, repetition = _carriers()
        run = run_case(_case(), _env(sentencing, bargain, signal, repetition))
        layer = run.branches[0].games_layer
        srep = K.check_sentencing_layer(
            DOMAIN, Q(25), Q(6), (CERT_RESP, CERT_PREV), layer.sentencing)
        self.assertTrue(srep.ok, srep.reasons)
        brep = K.check_bargain_result(BARGAIN, layer.bargaining)
        self.assertTrue(brep.ok, brep.reasons)
        qrep = K.check_beliefs_and_seq(
            GAME, POOL_S, ALWAYS_U, MU_HALF, MU_HALF, layer.seq_eq)
        self.assertTrue(qrep.ok, qrep.reasons)
        trep = K.check_threshold(Q(3), Q(4), Q(2), Q(2, 3), layer.threshold,
                                 layer.sustains, layer.credible)
        self.assertTrue(trep.ok, trep.reasons)

    def test_below_threshold_delta_is_a_finding_note_not_failure(self):
        """δ=1/3 低于可信惩罚阈值：合作不维持是**发现**（pending 注记），
        不是技术失败——主链仍 COMPLETE。"""
        sentencing, bargain, signal, repetition = _carriers(delta=Q(1, 3))
        run = run_case(_case(), _env(sentencing, bargain, signal, repetition))
        self.assertIs(run.status, RunStatus.COMPLETE)
        layer = run.branches[0].games_layer
        self.assertFalse(layer.sustains)
        self.assertTrue(any("not sustained" in n for n in run.pending))

    def test_partial_carriers_fail_closed(self):
        """只声明部分载体：协议要求四槽全要——缺失槽 fail-closed 进 FAILED
        （技术失败不是法律结论）。"""
        sentencing, bargain, signal, repetition = _carriers()
        run = run_case(_case(), _env(sentencing, bargain))
        self.assertIs(run.status, RunStatus.FAILED)
        self.assertTrue(any("all four carriers" in f for f in run.failures),
                        run.failures)

    def test_malformed_carrier_attribute_error_is_failed(self):
        """载体缺属性（裸 object 顶槽）：AttributeError → 既有 FAILED 路径。"""
        sentencing, bargain, signal, repetition = _carriers()
        run = run_case(_case(), _env(object(), bargain, signal, repetition))
        self.assertIs(run.status, RunStatus.FAILED)
        self.assertTrue(any("AttributeError" in f for f in run.failures),
                        run.failures)

    def test_failed_seqeq_profile_is_failed(self):
        """序贯检查不过的剖面（发送者更爱离轨信号 H）：门校验 ValueError →
        FAILED——不是把不合格剖面当均衡输出。"""
        deviant_game = R.SigGame(
            prior=Q(1, 2),
            pay_l_u=(Q(2), Q(2)), pay_l_d=(Q(1), Q(1)),
            pay_h_u=(Q(1), Q(1)), pay_h_d=(Q(0), Q(0)),
            us_l_u=(Q(3), Q(3)), us_l_d=(Q(0), Q(0)),
            us_h_u=(Q(10), Q(10)), us_h_d=(Q(0), Q(0)))  # H 显著占优
        signal = SignalInput(game=deviant_game, sS=POOL_S, sR=ALWAYS_U,
                             mu_l=MU_HALF, mu_h=MU_HALF)
        sentencing, bargain, _signal, repetition = _carriers()
        run = run_case(_case(), _env(sentencing, bargain, signal, repetition))
        self.assertIs(run.status, RunStatus.FAILED)
        self.assertTrue(any("sequential check failed" in f
                            for f in run.failures), run.failures)

    def test_bad_discount_is_failed(self):
        """折扣越界（重复博弈 δ=1 不满足 [0,1)）：尾界证书门 ValueError →
        FAILED（构造级 BargainParams 门的同类失败见 implementation_tests）。"""
        sentencing, bargain, signal, _repetition = _carriers()
        bad_rep = RepetitionInput(r=Q(3), t=Q(4), p=Q(2), delta=Q(1))
        run = run_case(_case(), _env(sentencing, bargain, signal, bad_rep))
        self.assertIs(run.status, RunStatus.FAILED)
        self.assertTrue(any("discount" in f for f in run.failures),
                        run.failures)

    def test_threshold_undefined_is_failed(self):
        """T ≤ P：可信惩罚阈值无定义（coop_threshold fail-fast）→ FAILED。"""
        sentencing, bargain, signal, repetition = _carriers()
        bad_rep = RepetitionInput(r=Q(3), t=Q(2), p=Q(4), delta=Q(2, 3))
        run = run_case(_case(), _env(sentencing, bargain, signal, bad_rep))
        self.assertIs(run.status, RunStatus.FAILED)
        self.assertTrue(any("T > P" in f for f in run.failures), run.failures)

    def test_non_credible_punishment_rejected_when_sustaining_claimed(self):
        """惩罚路径不在许可行动集而参数下主张合作维持：可信门 ValueError →
        FAILED（§8.3：惩罚必须本身为其子博弈允许/可信行动）。"""
        sentencing, bargain, signal, repetition = _carriers(
            punishment_permitted=False)
        run = run_case(_case(), _env(sentencing, bargain, signal, repetition))
        self.assertIs(run.status, RunStatus.FAILED)
        self.assertTrue(any("non-permitted punishment" in f
                            for f in run.failures), run.failures)

    def test_interp_and_games_layers_coexist(self):
        """与 T122/T123 解释层并存：同一 run 同时挂 interp_layer 与
        games_layer（Γ 级两层互不挤占）。"""
        from tools.full_math.implementation import interpretation_ref as RI
        rule = RI.RuleAst(rule_id="R-1", premises=("contract_signed",),
                          conclusion="payment_due")
        inp = RI.InterpInput(text_id="art7-text", context_ids=("mat-11",))
        cand = RI.mk_candidate(RI.InterpMethod.LITERAL, "c1", inp, "art7",
                               "civil", RI.InterpEffect.SELECT_READING,
                               rule, "reason-1", "court-9")
        sentencing, bargain, signal, repetition = _carriers()
        env = _env(sentencing, bargain, signal, repetition, cands=[cand])
        run = run_case(_case(), env)
        self.assertIs(run.status, RunStatus.COMPLETE)
        self.assertIsNotNone(run.branches[0].interp_layer)
        self.assertIsNotNone(run.branches[0].games_layer)
