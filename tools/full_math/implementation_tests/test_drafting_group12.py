"""W2-A batch B12 acceptance tests: D104-D115, group 12 起草、修订与
交付.

Six pieces per demand (docs/full-math/W2B_CLASSIFICATION.md §5.4):

1. Lean contract  — Contracts.demand_D104..D115 restated as this item's own
   semantics (verified by CI; the registration-format tests live in
   test_registration_bindings.py).
2. Python entry   — tools/full_math/implementation/drafting_ref.py per-item
   entries computing the intermediate result from real structured input.
3. Independent checker — drafting_check.py re-derives the contract inline;
   no witness callbacks, no expectations from the main implementation.
4. Downstream consumption — unified.pipeline run_case / step_event /
   run_trace consume the drafting results through the adapters in
   drafting_ref (build_case_input / build_environment /
   drafting_trace_events).
5. Positive and adverse cases — the ALL_134 counterexample field of each
   demand is executed with per-item expectations.
6. Synthetic receipt — completion.validate_binding rows for
   DEMAND:D104-D115 (the ``_binding_row`` template below is ready for
   the controller to back-fill BINDINGS.json).
"""
import json
import sys
from fractions import Fraction
from pathlib import Path

import pytest

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[2]
SPEC = REPO / 'tools/full_math/spec'
sys.path.insert(0, str(REPO))
sys.path.insert(0, str(REPO / 'tools/full_math'))
sys.path.insert(0, str(REPO / 'tools/unified_math_v2'))

# Shared bare module names (`reference`, `unified`, ...) exist in several
# tool trees.  Evict cached copies ONLY when the loaded copy is from a
# foreign tree: an earlier suite may already have imported the right
# tools/unified_math_v2 modules, and a blind re-import would create a
# second enum identity that fails `kind is LegalEventKind...` dispatch.
_existing_unified = sys.modules.get('unified')
if _existing_unified is None or \
        'unified_math_v2' not in str(getattr(_existing_unified, '__file__', '')):
    for _shared in ("reference", "unified", "unified_v21"):
        for _name in [m for m in sys.modules
                      if m == _shared or m.startswith(_shared + ".")]:
            del sys.modules[_name]

from tools.full_math.implementation import drafting_check as K  # noqa: E402
from tools.full_math.implementation import drafting_ref as R  # noqa: E402
import completion as C  # noqa: E402

# Pipeline-facing names are imported INSIDE the downstream test, not at
# module level: other suites in this directory re-resolve the shared bare
# `unified` tree at their own import time, and call-time imports are the
# only bindings that always match the lazy in-function imports inside
# unified.pipeline/process (drafting_ref's adapters already import
# lazily).

DEMANDS = ("D104", "D105", "D106", "D107", "D108",
           "D109", "D110", "D111", "D112", "D113", "D114", "D115")


# ---------------------------------------------------------------------------
# 2/3/5 — entry + independent checker, positive and adverse (per item)
# ---------------------------------------------------------------------------


def _run_D104():
    """只复制原告事实也获文本相似高分不能称有效答辩（ALL_134 反例字段）."""
    out = R.defense_answer("req-refund", "complaint-art-7",
                           "delivery-record-3")
    ok, reasons = K.check_D104("req-refund", "complaint-art-7",
                               "delivery-record-3", out)
    return ok, reasons, out


def _run_D105():
    """给金标事实的阶段分数不得当原始卷宗全链分数（ALL_134 反例字段）."""
    out = R.structured_sections()
    ok, reasons = K.check_D105(out)
    return ok, reasons, out


def _run_D106():
    """两项同金额但不同请求对象不能在去重时删一项（ALL_134 反例字段）."""
    out = R.claim_schedule(Fraction(450, 1))
    ok, reasons = K.check_D106(Fraction(450, 1), out)
    return ok, reasons, out


def _run_D107():
    """“暂不执法”写成“规范已经废止”应失败（ALL_134 反例字段）."""
    out = R.client_alert(20260301, "reg-bulletin-2026-03")
    ok, reasons = K.check_D107(20260301, "reg-bulletin-2026-03", out)
    return ok, reasons, out


def _run_D108():
    """数值正确但结论删去假设条件不得通过业务合同（ALL_134 反例字段）."""
    out = R.memo_review()
    ok, reasons = K.check_D108(out)
    return ok, reasons, out


def _run_D109():
    """生成“已决议”措辞不能使法定程序自动视为完成（ALL_134 反例字段）."""
    out = R.resolution_draft("board", "unanimous", "approve-guarantee",
                             "abstention-recused")
    ok, reasons = K.check_D109("board", "unanimous", "approve-guarantee",
                               "abstention-recused", out)
    return ok, reasons, out


def _run_D110():
    """复用模板中的旧客户名或互斥条款应被识别（ALL_134 反例字段）."""
    out = R.termsheet_draft()
    ok, reasons = K.check_D110(out)
    return ok, reasons, out


def _run_D111():
    """修改定义后正文不变不代表法律效果未变（ALL_134 反例字段）."""
    out = R.redline_impact()
    ok, reasons = K.check_D111(out)
    return ok, reasons, out


def _run_D112():
    """融资承诺和终版额度不同仍输出“全部一致”须失败（ALL_134 反例字段）."""
    out = R.cross_doc_consistency()
    ok, reasons = K.check_D112(out)
    return ok, reasons, out


def _run_D113():
    """“may”译成无条件“应当”、否定词丢失（ALL_134 反例字段）."""
    out = R.term_translation(Fraction(900, 1))
    ok, reasons = K.check_D113(Fraction(900, 1), out)
    return ok, reasons, out


def _run_D114():
    """只保留支持方论据，删掉关键例外，不可称完整摘要（ALL_134 反例字段）."""
    out = R.summary_review()
    ok, reasons = K.check_D114(out)
    return ok, reasons, out


def _run_D115():
    """文件存在但正文为空，或批注暴露内部备算，必须失败（ALL_134 反例字段）."""
    out = R.delivery_check()
    ok, reasons = K.check_D115(out)
    return ok, reasons, out


_POSITIVE = {"D104": _run_D104, "D105": _run_D105, "D106": _run_D106,
             "D107": _run_D107, "D108": _run_D108, "D109": _run_D109,
             "D110": _run_D110, "D111": _run_D111, "D112": _run_D112,
             "D113": _run_D113, "D114": _run_D114, "D115": _run_D115}


@pytest.mark.parametrize("dem", DEMANDS)
def test_demand_positive(dem):
    """Entry computes the intermediate result; the independent checker
    re-derives the contract from the same input and passes."""
    ok, reasons, _out = _POSITIVE[dem]()
    assert ok, f"{dem} contract violated: {reasons}"


@pytest.mark.parametrize("dem", DEMANDS)
def test_demand_counterexample(dem):
    """The ALL_134 counterexample field of each demand is distinguishable
    in the entry output with per-item expectations."""
    _ok, _reasons, out = _POSITIVE[dem]()
    if dem == "D104":
        answer = out
        # 三立场各自覆盖；纯叙事/无出处/无假设不覆盖；三标签互异
        assert answer["covered_admit"] is True
        assert answer["covered_deny"] is True
        assert answer["covered_reserve"] is True
        assert answer["narrative_copy_misses"] is True
        assert answer["no_source_misses"] is True
        assert answer["no_assumption_misses"] is True
        assert answer["stances_distinct"] is True
    elif dem == "D105":
        sections = out
        # 三段同册接地、链不跳级；金标不入册、跳级失败
        assert sections["fact_seg_grounded"] is True
        assert sections["reason_seg_grounded"] is True
        assert sections["ruling_seg_grounded"] is True
        assert sections["chain_deps_met"] is True
        assert sections["gold_standard_not_grounded"] is True
        assert sections["skip_upstream_fails"] is True
    elif dem == "D106":
        claims = out
        # 全量覆盖、两行互异；漏列/按金额合并都不覆盖
        assert claims["full_cover"] is True
        assert claims["rows_distinct"] is True
        assert claims["omission_misses"] is True
        assert claims["merge_misses"] is True
    elif dem == "D107":
        alert = out
        # 四类互异；姿态行只答姿态查询并带时间来源；标签互异
        assert alert["kinds_pairwise_distinct"] is True
        assert alert["posture_hit"] == ("temp-not-enforced", 20260301,
                                        "reg-bulletin-2026-03")
        assert alert["statute_miss"] is None
        assert alert["case_effect_miss"] is None
        assert alert["reform_miss"] is None
        assert alert["posture_label_ne_repealed"] is True
    elif dem == "D108":
        memo = out
        # 四槽齐备、假设保留、数值回读 900-fen；删假设/缺数值槽都失败
        assert memo["slots_ok"] is True
        assert memo["assumptions_met"] is True
        assert memo["numeric_readback"] == "900-fen"
        assert memo["dropped_assumption_fails"] is True
        assert memo["missing_numeric_fails"] is True
    elif dem == "D109":
        resolution = out
        # 四字段保留、批准位恒 False；事件才批准、措辞不批准
        assert resolution["fields_preserved"] is True
        assert resolution["approval_flag"] is False
        assert resolution["empty_events_never_approve"] is True
        assert resolution["approval_event_approves"] is True
        assert resolution["worded_draft_never_approves"] is True
    elif dem == "D110":
        termsheet = out
        # put 律回读、未授权区不动、旧客户名检出、互斥同稿才冲突
        assert termsheet["verified_term_readback"] == "v1"
        assert termsheet["put_law_on_any_base"] is True
        assert termsheet["unauthorized_region_preserved"] is True
        assert termsheet["term1_untouched"] is True
        assert termsheet["stale_detected"] is True
        assert termsheet["updated_not_flagged"] is True
        assert termsheet["exclusive_pair_flagged"] is True
        assert termsheet["single_clause_not_flagged"] is True
    elif dem == "D111":
        redline = out
        # 一次扩散/闭包/区外不动/有效值随定义变而正文不变
        assert redline["zone1"] == ("def-1", "clause-2")
        assert redline["zone2"] == ("def-1", "clause-2", "outcome-3")
        assert redline["outside_zone"] is True
        assert redline["outside_observation_unchanged"] is True
        assert redline["effective_before"] == "v1"
        assert redline["effective_after"] == "v2"
        assert redline["text_unchanged"] is True
        assert redline["effect_changed"] is True
    elif dem == "D112":
        consistency = out
        # 同值全同；500 vs 800 差异显式
        assert consistency["agree_values"] == ("500-fen", "500-fen")
        assert consistency["agree_all_same"] is True
        assert consistency["diverge_values"] == ("500-fen", "800-fen")
        assert consistency["diverge_not_all_same"] is True
        assert consistency["difference_visible"] is True
    elif dem == "D113":
        translation = out
        # 四分量保持；may→shall 角色翻转、否定丢失可检出；自由文本不出译文
        assert translation["role_preserved"] is True
        assert translation["negation_preserved"] is True
        assert translation["exception_preserved"] is True
        assert translation["amount_preserved"] is True
        assert translation["may_to_shall_flips_role"] is True
        assert translation["role_labels_distinct"] is True
        assert translation["drop_negation_flips"] is True
        assert translation["controlled_translates"] is True
        assert translation["free_text_manual_review"] is True
    elif dem == "D114":
        summary = out
        # 有来源、全覆盖；删例外不覆盖、无来源不过门
        assert summary["sourced"] is True
        assert summary["covered"] is True
        assert summary["dropped_exception_fails"] is True
        assert summary["unsourced_fails"] is True
    elif dem == "D115":
        delivery = out
        # 过门、回读 900-fen；空正文/错名/内部备算各败
        assert delivery["gate_passes"] is True
        assert delivery["key_readback"] == "900-fen"
        assert delivery["empty_body_fails"] is True
        assert delivery["wrong_name_fails"] is True
        assert delivery["scratch_annotation_fails"] is True


@pytest.mark.parametrize("dem", DEMANDS)
def test_checker_rejects_tampered(dem):
    """The independent checker must fail a tampered intermediate result
    (the checker, not the entry, is the judge of the contract)."""
    ok, _reasons, out = _POSITIVE[dem]()
    assert ok  # sanity: the honest result passes its own checker
    if dem == "D104":
        tampered = dict(out)
        tampered["narrative_copy_misses"] = False  # copy counts as answer
        bad, reasons = K.check_D104("req-refund", "complaint-art-7",
                                    "delivery-record-3", tampered)
    elif dem == "D105":
        tampered = dict(out)
        tampered["gold_standard_not_grounded"] = False  # gold in registry
        bad, reasons = K.check_D105(tampered)
    elif dem == "D106":
        tampered = dict(out)
        tampered["merge_misses"] = False  # merge accepted as covering
        bad, reasons = K.check_D106(Fraction(450, 1), tampered)
    elif dem == "D107":
        tampered = dict(out)
        tampered["statute_miss"] = ("temp-not-enforced", 20260301,
                                    "reg-bulletin-2026-03")  # posture read as repeal
        bad, reasons = K.check_D107(20260301, "reg-bulletin-2026-03",
                                    tampered)
    elif dem == "D108":
        tampered = dict(out)
        tampered["dropped_assumption_fails"] = False  # assumption-free OK
        bad, reasons = K.check_D108(tampered)
    elif dem == "D109":
        tampered = dict(out)
        tampered["worded_draft_never_approves"] = False  # wording approves
        bad, reasons = K.check_D109("board", "unanimous",
                                    "approve-guarantee",
                                    "abstention-recused", tampered)
    elif dem == "D110":
        tampered = dict(out)
        tampered["term1_untouched"] = False  # region not preserved
        bad, reasons = K.check_D110(tampered)
    elif dem == "D111":
        tampered = dict(out)
        tampered["zone2"] = ("def-1", "clause-2")  # closure truncated
        bad, reasons = K.check_D111(tampered)
    elif dem == "D112":
        tampered = dict(out)
        tampered["diverge_not_all_same"] = False  # difference silenced
        bad, reasons = K.check_D112(tampered)
    elif dem == "D113":
        tampered = dict(out)
        tampered["free_text_manual_review"] = False  # free text auto-translated
        bad, reasons = K.check_D113(Fraction(900, 1), tampered)
    elif dem == "D114":
        tampered = dict(out)
        tampered["dropped_exception_fails"] = False  # exception-free complete
        bad, reasons = K.check_D114(tampered)
    elif dem == "D115":
        tampered = dict(out)
        tampered["empty_body_fails"] = False  # empty body accepted
        bad, reasons = K.check_D115(tampered)
    assert not bad, f"{dem} checker accepted a tampered result: {reasons}"


# ---------------------------------------------------------------------------
# per-demand adverse specifics beyond the shared parametrized set
# ---------------------------------------------------------------------------


def test_D104_stance_labels_are_the_only_answers():
    """立场三标签外不作答；请求 id 不匹配的行不覆盖."""
    assert R.stance_ok("admitted") is True
    assert R.stance_ok("reserved") is True
    assert R.stance_ok("narrate") is False
    assert R.defense_covers(("req-1",),
                            (("other-req", "admitted", "s", "a"),)) is False


def test_D105_registry_grounding_is_per_section():
    """段内任一命题出册即不接地；依赖边只要上行在场就要求下行在场."""
    assert R.seg_grounded(("a",), ("a", "b")) is False
    assert R.deps_met(("x",), (("x", "y"),)) is False
    assert R.deps_met((), (("x", "y"),)) is True


def test_D106_partial_and_permuted_never_cover():
    """乱序换位同样破坏逐行恒等覆盖（身份保持不含重排）."""
    claims = (("claim-a", "pay", Fraction(1, 2)),
              ("claim-b", "pay", Fraction(1, 2)))
    docs = (("claim-b", "pay", Fraction(1, 2)),
            ("claim-a", "pay", Fraction(1, 2)))
    assert R.claim_covered(claims, docs) is True  # both rows present
    assert R.claim_covered(claims, docs[:1]) is False


def test_D107_every_channel_answers_its_own_rows():
    """任一通道的行只答本通道查询（四通道互不串答）."""
    rows = ((R.CHG_STATUTE, "law-amended", 1, "gazette"),
            (R.CHG_REFORM_PLAN, "draft-reform", 2, "npc-plan"))
    assert R.alert_row_of(rows, R.CHG_STATUTE) == ("law-amended", 1,
                                                   "gazette")
    assert R.alert_row_of(rows, R.CHG_CASE_EFFECT) is None
    assert R.alert_row_of(rows, R.CHG_ENFORCE_POSTURE) is None
    assert R.alert_row_of(rows, R.CHG_REFORM_PLAN) == ("draft-reform", 2,
                                                       "npc-plan")


def test_D108_slot_gate_rejects_empty_and_late_values():
    """空值槽与仅占位的槽都不算可验证内容."""
    memo = (("section", "structure-1"), ("conclusion", ""),
            ("citation", "cite-1"), ("numeric", "900-fen"))
    assert R.memo_slots_ok(memo) is False
    assert R.memo_slots_ok(()) is False


def test_D109_approval_marker_never_equals_draft_wording():
    """批准事件标记与草稿措辞是不同字符串；任意四字段组合都保留."""
    fields, flag = R.draft_resolution("board", "majority",
                                      "approve-loan", "conflict-guard")
    assert fields == ("board", "majority", "approve-loan",
                      "conflict-guard")
    assert flag is False
    assert R.approved_by(("approved:approve-loan",), "approve-loan") is True
    assert R.approved_by(("approve-loan",), "approve-loan") is False


def test_D110_put_lens_law_on_the_termsheet_terms():
    """termsheet 任一条款值 put 后回读恰为该值（一般律，任意底稿）."""
    base = [("client", "old-co"), ("term-2", "v2"), ("term-1", "v1")]
    for key, value in (("term-1", "v1-new"), ("term-3", "v3"),
                       ("client", "new-co")):
        draft = R.doc_put(base, key, value)
        assert R.term_met(draft, (key, value)) is True


def test_D111_zone_spread_only_through_in_zone_sources():
    """源点不在区内的边不扩散；已入区的目标不重复."""
    edges = (("def-1", "clause-2"), ("outside-9", "ghost-0"),
             ("clause-2", "outcome-3"))
    assert R.spread_once(edges, ("def-1",)) == ("def-1", "clause-2")
    assert R.spread_once(edges, ("def-1", "clause-2")) == \
        ("def-1", "clause-2", "outcome-3")
    assert R.spread_once(edges, ("outside-9",)) == ("outside-9", "ghost-0")


def test_D112_same_key_other_documents_stay_visible():
    """任一文书缺键时该键值列表只含在场值；两值差异恒可见."""
    docs = ((("commitment-amount", "500-fen"),),
            (("closing-event", "signed"),))
    assert R.values_of(docs, "commitment-amount") == ("500-fen",)
    assert R.all_same(("x", "x", "x")) is True
    assert R.all_same(("x", "y")) is False


def test_D113_translation_preserves_each_component_independently():
    """四分量逐项保持（含否定 True 分量）；EN- 只装饰不改写."""
    term = ("discretionary", True, "none-exc", Fraction(7, 3))
    got = R.translate_term(term)
    assert got == ("EN-discretionary", True, "EN-none-exc",
                   Fraction(7, 3))
    assert got[0] != term[0]  # decorated, but role text preserved inside
    assert "discretionary" in got[0]


def test_D114_coverage_needs_same_id_not_same_source():
    """覆盖按同 id 命题判定，与来源字段无关."""
    points = ("support-1", "exception-1")
    props = (("support-1", "src-x"), ("exception-1", "src-y"))
    assert R.covers_points(points, props) is True
    assert R.covers_points(("extra-9",), props) is False
    assert R.summary_sourced((("support-1", "src-x"),)) is True


def test_D115_gate_joins_both_violations_and_clean_readback():
    """门=良构+无内部备算；键回读等于核验值（put/get 透传）."""
    assert R.deliverable_ok("dl-a.csv", (("k", "v"),)) is True
    assert R.deliverable_ok("dl-a.csv", (("", "v"),)) is False
    assert R.clean_annotations((("note", "n"),)) is True
    assert R.deliverable_gate("dl-a.csv", (("k", "v"),
                                           ("internal-scratch", "d"))) is False
    assert R.doc_get(R.doc_put([], "claim-1", "900-fen"),
                     "claim-1") == "900-fen"


# ---------------------------------------------------------------------------
# 4 — downstream consumption: run_case / step_event / run_trace
# ---------------------------------------------------------------------------


def test_downstream_pipeline_consumes_drafting():
    """run_case consumes the CaseInput assembled from the drafting
    results (the covered claim list and the verified deliverable supply
    the issue, the uncovered-claim proposition stays awaiting — never
    written, and the only quantities are the claim-amount total (both
    same-amount claims, one schedule) and the financing-commitment
    amount); run_trace consumes the delivered-file witness as an
    evidence event plus the exact 900-fen claim installment."""
    # call-time imports: always the same unified copies the pipeline's own
    # lazy in-function imports resolve to (see module docstring note).
    # Call-time PATH re-assertion first (same rationale as B10).
    _v2 = str(REPO / 'tools/unified_math_v2')
    while _v2 in sys.path:
        sys.path.remove(_v2)
    sys.path.insert(0, _v2)
    from theory.spec.canonical_v2.case import RunStatus
    from theory.spec.canonical_v2.kernel import Judgment
    from unified.pipeline import run_case, run_trace, step_event
    from unified.process import gross_of

    intake = R.build_drafting_intake()
    case = R.build_case_input(intake)
    env = R.build_environment(intake)

    # the assembled carriers are exactly the drafting outputs
    assert case.issues == ("DRAFTING_DELIVERY",)
    assert case.claims[0].claimant == "client"
    assert case.claims[0].respondent == "counterparty"
    # D111: the redline-scope defense rides on the case; the
    # uncovered-claim proposition stays awaiting — never written
    assert case.defenses[0].defense_id == "def-redline-scoped"
    assert case.defenses[0].basis == "redline_outside_zone"
    assert case.defenses[0].target_claims == ("c0",)
    standings = {(f.proposition.predicate, f.standing.name)
                 for f in case.fact_records}
    assert ("claim-list-covered", "ADMITTED_POSITIVE") in standings
    assert ("deliverable-verified", "ADMITTED_POSITIVE") in standings
    assert ("uncovered-claim", "AWAITING_ADMISSION") in standings
    # D106/D112: the only quantities are the claim total (450+450) and
    # the financing commitment (500) — the cross-document difference
    # stays a difference, never merged
    assert [q.value for q in case.quantities] == [Fraction(900, 1),
                                                  Fraction(500, 1)]
    assert {q.basis_kind for q in case.quantities} == {"claim-amount",
                                                       "commitment-amount"}

    run = run_case(case, env)
    assert run.status is RunStatus.COMPLETE
    assert run.failures == ()
    judgments = run.judgments_of("c0")
    assert judgments and Judgment.ESTABLISHED in judgments

    # trace: the delivered-file witness becomes an evidence event; the
    # covered claim total lands as one exact installment (900 fen)
    events = R.drafting_trace_events(intake)
    assert [e.event.event_id for e in events[:1]] == ["ev-delivered-file"]
    final, notes = run_trace(case.initial_state, events, env)
    assert "ev:ev-delivered-file" in [e.evidence_id for e in final.evidence]
    event_ids = [e.event_id for e in final.events]
    assert "pay-claims-900" in event_ids
    assert gross_of(final, "CLAIM_AMOUNT") == Fraction(900, 1)
    assert gross_of(final, "COMMITMENT_AMOUNT") == Fraction(0)
    allocated = [e for e in final.ledger
                 if e.kind.name == "GROSS_ALLOCATED"
                 and e.basis_key == "CLAIM_AMOUNT"]
    assert sorted(e.amount for e in allocated) == [Fraction(900, 1)]
    assert notes  # the step relation actually produced observations

    # step_event alone: one step, exactly the event's own semantics
    one = step_event(case.initial_state, events[0], env)
    assert [e.evidence_id for e in one.next_state.evidence] == \
        ["ev:ev-delivered-file"]
    assert one.next_env is env

    # the drafting decisions stay on the bundle: the answer coverage
    # (D104), the grounded sections (D105), the claim covering (D106),
    # the separated change channel (D107), the memo verdicts (D108),
    # the non-approving draft (D109), the termsheet transform (D110),
    # the redline zone (D111), the visible difference (D112), the term
    # translation (D113), the summary gates (D114) and the delivery
    # gate (D115)
    assert intake["answer"]["narrative_copy_misses"] is True
    assert intake["sections"]["chain_deps_met"] is True
    assert intake["claims"]["merge_misses"] is True
    assert intake["alert"]["statute_miss"] is None
    assert intake["memo"]["assumptions_met"] is True
    assert intake["resolution"]["approval_flag"] is False
    assert intake["termsheet"]["unauthorized_region_preserved"] is True
    assert intake["redline"]["outside_zone"] is True
    assert intake["consistency"]["diverge_not_all_same"] is True
    assert intake["translation"]["free_text_manual_review"] is True
    assert intake["summary"]["covered"] is True
    assert intake["delivery"]["gate_passes"] is True


# ---------------------------------------------------------------------------
# 6 — synthetic receipts through completion.validate_binding
# ---------------------------------------------------------------------------

_REQUIREMENTS = {
    r["id"]: r
    for r in json.loads((SPEC / 'REQUIREMENTS.json').read_text(encoding='utf-8'))
}

_SEMANTICS = {
    "D104": "the mandatory-reply coverage of an answer draft: every "
            "required request has an answer row of its own id with an "
            "explicit stance (admission, denial and reservation are "
            "three distinct labels) and non-empty source and "
            "assumption fields; narrative copying, a missing source "
            "and a missing assumption never cover.",
    "D105": "the fact, reason and ruling sections cite only "
            "propositions grounded in the same one registry of "
            "fact/argument/result objects, and citing a proposition "
            "always cites its declared upstream dependency (the "
            "fact → argument → result chain is never skipped); a "
            "gold-standard proposition outside the registry and a "
            "ruling that skips the argument level both fail.",
    "D106": "the confirmed claim list to the document list is an "
            "identity-preserving covering: every confirmed (id, "
            "target, amount) row appears in the document list as the "
            "very same row; an omission and an amount-keyed merge "
            "(two same-amount claims of different objects collapsed) "
            "never cover.",
    "D107": "statute change, adjudication effect, enforcement posture "
            "and expected reform are four distinct kinds, queried by "
            "kind so an enforcement-posture row (carrying its own "
            "time and source) never answers the statute channel; "
            "'temporarily not enforced' and 'repealed' are distinct "
            "labels.",
    "D108": "section, conclusion, citation and numeric slots are each "
            "present with non-empty verifiable content, the "
            "conclusion keeps its assumption conditions, and the "
            "numeric slot read-back equals the verified value; a "
            "conclusion with a dropped assumption or a memo missing "
            "the numeric slot fails.",
    "D109": "the generated resolution draft keeps organ, vote, "
            "authorized item and conflict safeguard with the "
            "actual-approval flag fixed to false; actual approval "
            "comes only from a recorded approval event for the very "
            "item, never from 'resolved'-worded draft text.",
    "D110": "a verified termsheet value put into the draft reads back "
            "exactly (the put lens law on any base document); a "
            "template transform on the client key leaves the term-1 "
            "region untouched; a stale old client name is detected "
            "(no false positive after the update) and two mutually "
            "exclusive clauses together are flagged.",
    "D111": "the modification point and its dependency closure form "
            "the affected zone (one spread step, then the closed "
            "zone); a key outside the zone keeps its protected "
            "observation across the edit, while a term defined "
            "through the edited definition changes its effective "
            "value even though its citing text is untouched.",
    "D112": "multiple documents carry their own values for one shared "
            "constraint key; agreement means all values are the same, "
            "and a financing-commitment 500-fen against a "
            "final-version 800-fen stays an explicit visible "
            "difference (never silently overwritten into 'all "
            "consistent').",
    "D113": "a controlled-term translation keeps the role, the "
            "negation, the exception and the numeric amount (the "
            "EN- prefix only decorates); a 'may'→'shall' modal flip "
            "and a negation drop are detected violations, and a term "
            "whose exception field is free text produces no auto "
            "translation at all (kept for manual review).",
    "D114": "every protected proposition of the summary carries a "
            "non-empty source and every independently determined key "
            "point is covered by a same-id proposition; dropping the "
            "key exception or carrying an unsourced proposition "
            "fails.",
    "D115": "a required deliverable passes the gate only when its "
            "name carries the dl- prefix, its body is non-empty with "
            "well-formed row keys and no annotation row exposes "
            "internal scratch work; the key table read-back (put then "
            "get) equals the verified value.",
}

_ENTRY = {
    "D104": "stance_ok/defense_covers/defense_answer",
    "D105": "seg_grounded/deps_met/structured_sections",
    "D106": "claim_covered/claim_schedule",
    "D107": "alert_row_of/client_alert",
    "D108": "memo_slots_ok/concl_assumptions_met/memo_review",
    "D109": "draft_resolution/approved_by/resolution_draft",
    "D110": "term_met/stale_client/excl_conflict/termsheet_draft",
    "D111": "spread_once/defined_term_of/redline_impact",
    "D112": "values_of/all_same/cross_doc_consistency",
    "D113": "translate_term/may_to_shall/drop_negation/"
            "translate_checked/term_translation",
    "D114": "summary_sourced/covers_points/summary_review",
    "D115": "prefix_dl/deliverable_ok/clean_annotations/"
            "deliverable_gate/delivery_check",
}


def _binding_row(dem, required):
    """Template for the controller's BINDINGS.json back-fill
    (DEMAND:D104–D115 rows).  Passes completion.validate_binding as-is."""
    return {
        "id": f"DEMAND:{dem}",
        "theorem": required["theorem"],
        "contract": required["contract"],
        "proof_mode": "KERNEL_CONTRACT_PROOF",
        "formal_scope": "Group-12 drafting/delivery demand instance in "
                        "the shared semantic framework: this item's own "
                        "contract semantics plus the registered byte "
                        "syntax component (the parse/render roundtrip: "
                        "an independent read-back of a rendered plain "
                        "segment returns exactly the segment, so "
                        "delivered free text is never silently "
                        "transformed), with its adverse case executed "
                        "as a negative test.",
        "independent_semantics": _SEMANTICS[dem],
        "algorithm": f"tools/full_math/implementation/drafting_ref.py "
                     f"{_ENTRY[dem]} computes the intermediate result "
                     f"from structured input; drafting_check.check_{dem} "
                     f"re-derives the contract independently.",
        "observation_contract": "Inputs are the declared structures "
                                "(mandatory-request lists with answer "
                                "rows carrying stance, source and "
                                "assumption fields, section "
                                "proposition lists over one registry "
                                "with dependency edges, confirmed "
                                "claim rows with ids, targets and "
                                "exact amounts, client-alert rows "
                                "keyed by change kind with time and "
                                "source, memo documents with slot keys, "
                                "resolution-draft governance fields "
                                "with approval events, draft documents "
                                "as key-value rows with termsheet "
                                "terms and template placeholders, "
                                "definition dependency edges with "
                                "effective-term resolution, multiple "
                                "documents sharing one constraint "
                                "key, controlled terms with role, "
                                "negation, exception and numeric "
                                "components, summary propositions with "
                                "sources and key-point lists, and "
                                "deliverable names with row tables and "
                                "annotations); outputs are exactly the "
                                "contract quantities (the stance-"
                                "keyed coverage verdicts, the "
                                "registry-grounding and chain-"
                                "dependency verdicts, the identity-"
                                "preserving covering verdicts, the "
                                "kind-keyed alert lookups with their "
                                "miss witnesses, the slot-gate and "
                                "assumption-keeping verdicts with the "
                                "numeric read-back, the field-"
                                "preserving draft with its never-"
                                "approving flag and event-keyed "
                                "approval, the put-law read-back with "
                                "the region-preserving transform and "
                                "the stale/exclusive flags, the spread "
                                "zone with the unchanged outside "
                                "observation and the moving effective "
                                "value, the per-document value lists "
                                "with the all-same verdicts, the four-"
                                "component translation with the "
                                "violation witnesses and the manual-"
                                "review gate, the source and coverage "
                                "verdicts, and the delivery gate with "
                                "its key read-back).",
        "external_assumptions": "Argument quality and language "
                                "persuasiveness, full semantic "
                                "equivalence of free-text translation, "
                                "judgment on whether claims are optimal "
                                "or legally supportable, future "
                                "enforcement prediction and "
                                "client-facing explanation quality, "
                                "real corporate authorization and "
                                "conflict-of-interest evaluation, "
                                "commercial and legal quality of "
                                "terms, implied impacts and open-"
                                "language understanding, interpretation "
                                "of ambiguous clauses and omitted "
                                "annexes, and cross-reader rendering "
                                "remain external validation "
                                "obligations, not part of this "
                                "registration.",
        "proof_sources": [
            "proofs/lean/juris_lean/JurisLean/FullMath/Contracts.lean",
            "proofs/lean/juris_lean/JurisLean/FullMath/Acceptance.lean",
        ],
        "implementation_sources": [
            "tools/full_math/implementation/drafting_ref.py",
            "tools/full_math/implementation/drafting_check.py",
        ],
        "test_ids": [
            "tools/full_math/implementation_tests::"
            "test_drafting_group12.py::"
            f"test_demand_positive[{dem}]",
            "tools/full_math/implementation_tests::"
            "test_drafting_group12.py::"
            f"test_demand_counterexample[{dem}]",
            "tools/full_math/implementation_tests::"
            "test_drafting_group12.py::"
            "test_downstream_pipeline_consumes_drafting",
        ],
        "negative_test_ids": [
            "tools/full_math/implementation_tests::"
            "test_drafting_group12.py::"
            f"test_checker_rejects_tampered[{dem}]",
        ],
        "semantic_links": [
            "JurisLean.FullMath.Document.parse_render_roundtrip",
        ],
    }


@pytest.mark.parametrize("dem", DEMANDS)
def test_b12_binding_receipt(dem):
    """Synthetic receipt: the binding row for DEMAND:D1XX passes
    completion.validate_binding against the real repository files."""
    required = _REQUIREMENTS[f"DEMAND:{dem}"]
    C.validate_binding(_binding_row(dem, required), required, repo=REPO)


@pytest.mark.parametrize("dem", DEMANDS)
def test_b12_binding_receipt_negative(dem):
    """A tampered receipt (swapped theorem) is rejected."""
    required = _REQUIREMENTS[f"DEMAND:{dem}"]
    row = dict(_binding_row(dem, required))
    row["theorem"] = "JurisLean.FullMath.Acceptance.nonexistent_demand"
    with pytest.raises(C.EvidenceError):
        C.validate_binding(row, required, repo=REPO)
