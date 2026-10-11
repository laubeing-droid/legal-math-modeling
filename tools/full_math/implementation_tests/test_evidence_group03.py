"""W2-A batch B03 acceptance tests: D019-D028, group 03 证据内容、事件与冲突.

Six pieces per demand (docs/full-math/W2B_CLASSIFICATION.md §5.4):

1. Lean contract  — Contracts.demand_D019..D028 restated as this item's own
   semantics (verified by CI; the registration-format tests live in
   test_registration_bindings.py).
2. Python entry   — tools/full_math/implementation/evidence_ref.py per-item
   entries computing the intermediate result from real structured input.
3. Independent checker — evidence_check.py re-derives the contract inline;
   no witness callbacks, no expectations from the main implementation.
4. Downstream consumption — unified.pipeline run_case / step_event /
   run_trace consume the evidence results through the adapters in
   evidence_ref (build_case_input / build_environment /
   evidence_trace_events).
5. Positive and adverse cases — the ALL_134 counterexample field of each
   demand is executed with per-item expectations.
6. Synthetic receipt — completion.validate_binding rows for DEMAND:D019-D028
   (the ``_binding_row`` template below is ready for the controller to
   back-fill BINDINGS.json).
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
# foreign tree: test_intake_group01 may already have imported the right
# tools/unified_math_v2 modules, and a blind re-import would create a
# second enum identity that fails `kind is LegalEventKind...` dispatch.
_existing_unified = sys.modules.get('unified')
if _existing_unified is None or \
        'unified_math_v2' not in str(getattr(_existing_unified, '__file__', '')):
    for _shared in ("reference", "unified", "unified_v21"):
        for _name in [m for m in sys.modules
                      if m == _shared or m.startswith(_shared + ".")]:
            del sys.modules[_name]

from tools.full_math.implementation import evidence_check as K  # noqa: E402
from tools.full_math.implementation import evidence_ref as R  # noqa: E402
import completion as C  # noqa: E402

# Pipeline-facing names are imported INSIDE the downstream test, not at
# module level: other suites in this directory re-resolve the shared bare
# `unified` tree at their own import time, and call-time imports are the
# only bindings that always match the lazy in-function imports inside
# unified.pipeline/process (evidence_ref's adapters already import lazily).

DEMANDS = ("D019", "D020", "D021", "D022", "D023", "D024", "D025",
           "D026", "D027", "D028")

_SOURCE = ("被告", "于", "3月", "向", "原告", "借款",
           "若", "借款", "未还", "则", "承担", "责任")
_TRIGGERS = (
    ("借款", "LOAN_GRANT", ("被告", "原告"), "principal", False, 0, 6),
    ("若", "HYPOTHESIS", (), "condition", True, 6, 9),
    ("未还", "DEFAULT_EVENT", ("被告",), "principal", True, 7, 9),
    ("责任", "LIABILITY", ("被告",), "damages", False, 9, 12),
)


# ---------------------------------------------------------------------------
# 2/3/5 — entry + independent checker, positive and adverse (per item)
# ---------------------------------------------------------------------------


def _run_D019():
    """触发词来自引述假设，不得变成已发生事件（ALL_134 反例字段）."""
    extraction = R.extract_events(_SOURCE, _TRIGGERS)
    ok, reasons = K.check_D019(_SOURCE, _TRIGGERS, extraction)
    return ok, reasons, (_SOURCE, _TRIGGERS, extraction)


def _run_D020():
    """前案被害人不得由位置默认绑定到本案（ALL_134 反例字段）."""
    edges = (
        ("case-b03", "plaintiff", "principal", "trial", "admitted-evidence"),
        ("case-b03", "defendant", "principal", "trial", "disputed"),
        ("case-prior", "prior-victim", "prior-object", "prior-trial",
         "adjudicated"),
    )
    binding = R.bind_roles(edges, "case-b03")
    ok, reasons = K.check_D020(edges, "case-b03", binding)
    return ok, reasons, (edges, binding)


def _run_D021():
    """没有时间的事件不凭叙述顺序补造精确日期（ALL_134 反例字段）."""
    items = (("chat-2024-01-05", 1), ("transfer", 3), ("call", None),
             ("receipt", 8))
    timeline = R.build_timeline(items)
    ok, reasons = K.check_D021(items, timeline)
    return ok, reasons, (items, timeline)


def _run_D022():
    """两个不同时点地址不能自动判为同一时点矛盾（ALL_134 反例字段）."""
    claims = (("defendant", 10, "repaid-full"),
              ("defendant", 10, "unpaid"),
              ("defendant", 20, "repaid-full"),
              ("defendant", 20, "moved-away"))
    contrary = (("repaid-full", "unpaid"), ("unpaid", "repaid-full"))
    conflicts = R.find_conflicts(claims, contrary)
    ok, reasons = K.check_D022(claims, contrary, conflicts)
    return ok, reasons, (claims, contrary, conflicts)


def _run_D023():
    """材料未附付款凭证不得推出肯定未付款（ALL_134 反例字段）."""
    record = (("loan_granted", True), ("demand_sent", True))
    missing = R.missing_support(record, "receipt_attached",
                                ("receipt_attached",))
    negative_entry = R.missing_support(
        record + (("receipt_attached", False),), "receipt_attached",
        ("receipt_attached",))
    ok, r1 = K.check_D023(record, "receipt_attached", ("receipt_attached",),
                          missing)
    ok2, r2 = K.check_D023(record + (("receipt_attached", False),),
                           "receipt_attached", ("receipt_attached",),
                           negative_entry)
    return ok and ok2, r1 + r2, (record, missing, negative_entry)


def _run_D024():
    """给正确答案但引用无关原句，不通过支持检查（ALL_134 反例字段）."""
    links = (("ans-payment", "span-transfer", 3, 5, "transfer-made"),
             ("ans-payment", "span-chat", 1, 2, "transfer-made"),
             ("ans-payment", "span-unrelated", 9, 10, ""))
    support = R.support_check(links, len(_SOURCE))
    ok, reasons = K.check_D024(links, len(_SOURCE), support)
    return ok, reasons, (links, support)


def _run_D025():
    """unknown 进 if 分支当 False 产生否定结论须拦截（ALL_134 反例字段）."""
    status = R.project_status("unknown")
    branch = R.decide_branch(status, "open-question-retained")
    conflict_branch = R.decide_branch("conflict", "conflict-preserved")
    yes_branch = R.decide_branch("yes", "unused-default")
    no_branch = R.decide_branch("no", "unused-default")
    ok1, r1 = K.check_D025(status, branch, "open-question-retained")
    ok2, r2 = K.check_D025("conflict", conflict_branch, "conflict-preserved")
    ok3, r3 = K.check_D025("yes", yes_branch, "unused-default")
    ok4, r4 = K.check_D025("no", no_branch, "unused-default")
    return ok1 and ok2 and ok3 and ok4, r1 + r2 + r3 + r4, \
        (status, branch, conflict_branch, yes_branch, no_branch)


def _run_D026():
    """原告诉称不得经摘要变成法院查明（ALL_134 反例字段）."""
    records = (
        ("asserted", "loan_granted", "complaint-summary",
         "party-allegation"),
        ("evidenceContent", "transfer_made", "bank-slips",
         "fact-finding-input"),
        ("adjudicated", "transfer_made", "court-registry", "adjudicated"),
    )
    classified = R.classify_records(records)
    ok, reasons = K.check_D026(records, classified)
    return ok, reasons, (records, classified)


def _run_D027():
    """把未确认行为改写为既成事实应使语义差量失败（ALL_134 反例字段）."""
    draft = ("loan_granted", "transfer_made", "fees_charged")
    section = R.draft_fact_section(draft, ("loan_granted", "transfer_made"),
                                   ("fees_charged",))
    delta = R.semantic_delta(section, ("fees_charged",))
    ok, r1 = K.check_D027(draft, ("loan_granted", "transfer_made"),
                          ("fees_charged",), ("fees_charged",), section,
                          delta)
    clean = R.semantic_delta(section, ())
    ok2, r2 = K.check_D027(draft, ("loan_granted", "transfer_made"),
                           ("fees_charged",), (), section, clean)
    return ok and ok2, r1 + r2, (draft, section, delta, clean)


def _run_D028():
    """过去抢劫经历不能直接加入本次危险驾驶罪名清单（ALL_134 反例字段）."""
    acts = (("case-b03", "ev-drive", "dangerous-driving", False),
            ("case-old", "ev-rob", "robbery", True))
    scoped = R.scope_acts(acts, "case-b03", (("recidivism-art-74", True),))
    ok, reasons = K.check_D028(acts, "case-b03", (("recidivism-art-74", True),),
                               scoped)
    return ok, reasons, (acts, scoped)


_POSITIVE = {"D019": _run_D019, "D020": _run_D020, "D021": _run_D021,
             "D022": _run_D022, "D023": _run_D023, "D024": _run_D024,
             "D025": _run_D025, "D026": _run_D026, "D027": _run_D027,
             "D028": _run_D028}


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
    if dem == "D019":
        _source, _triggers, extraction = out
        # 引述假设的触发词不成事件；事件跨度回指原文；标签无碰撞
        types = [e["type"] for e in extraction["events"]]
        assert "HYPOTHESIS" not in types and "DEFAULT_EVENT" not in types
        assert types == ["LOAN_GRANT", "LIABILITY"]
        first = extraction["events"][0]
        assert first["span"] == _SOURCE[first["start"]:first["end"]]
        assert first["span_length"] == first["end"] - first["start"]
        assert [b[0] for b in extraction["quoted_blocked"]] == ["若", "未还"]
    elif dem == "D020":
        _edges, binding = out
        # 前案被害人不在本案绑定里；逐边字段（stage/standing）原样保留
        persons = [e[1] for e in binding["bound"]]
        assert persons == ["plaintiff", "defendant"]
        assert "prior-victim" not in persons
        assert binding["outside"][0][0] == "case-prior"
        assert binding["bound"][0][3:5] == ("trial", "admitted-evidence")
        assert binding["bound"][1][3:5] == ("trial", "disputed")
    elif dem == "D021":
        _items, timeline = out
        # 日期偏序给拓扑序；无日期事件保持 unknown，不补造日期
        assert timeline["order"] == ("chat-2024-01-05", "transfer", "receipt")
        days = [t["day"] for t in timeline["timeline"]]
        assert days == sorted(days) == [1, 3, 8]
        assert timeline["pending"] == ({"event": "call", "day": None,
                                        "status": "unknown"},)
        assert all(p["day"] is None for p in timeline["pending"])
    elif dem == "D022":
        _claims, _contrary, conflicts = out
        # 同时点相反声明成矛盾且带见证；不同时点只是含混，两种读法保留
        assert len(conflicts["conflicts"]) == 2
        for c in conflicts["conflicts"]:
            assert c["day"] == 10 and c["witness"]
        assert conflicts["conflicts"][0]["propositions"] == \
            ("repaid-full", "unpaid")
        assert all(a["readings"] for a in conflicts["ambiguities"])
        assert any(a["readings"] == ("repaid-full", "moved-away")
                   for a in conflicts["ambiguities"])
        # 不同时点的同主体对：same_time=False，不成同一时点矛盾
        cross_time = [a for a in conflicts["ambiguities"]
                      if a["readings"] in (("repaid-full", "unpaid"),
                                           ("unpaid", "repaid-full"))]
        assert cross_time and all(a["same_time"] is False
                                  for a in cross_time)
        assert all(c["day"] == 10 for c in conflicts["conflicts"])
    elif dem == "D023":
        _record, missing, negative_entry = out
        # 缺记录≠否定证据：negation 不被推出；显式否定条目是另一载体
        assert missing["in_record"] is False
        assert missing["negative_evidence"] is False
        assert missing["negation_inferred_from_missing"] is False
        assert missing["carrier"] == "no-record"
        assert negative_entry["negative_evidence"] is True
        assert negative_entry["carrier"] == "negative-record"
    elif dem == "D024":
        _links, support = out
        # 无关引用被拒；同答案两条冗余支持都保留
        assert support["rejected_irrelevant"] == (
            {"span": "span-unrelated", "start": 9, "end": 10,
             "proposition": ""},)
        kept = support["supports"]["ans-payment"]
        assert [s["span"] for s in kept] == ["span-transfer", "span-chat"]
        assert all(s["proposition"] == "transfer-made" for s in kept)
    elif dem == "D025":
        status, branch, conflict_branch, yes_branch, no_branch = out
        # unknown/conflict 被拦截落到默认分支，绝不当 False 产生否定结论
        assert status == "unknown"
        assert branch == {"branch": "default",
                          "value": "open-question-retained",
                          "definite": False}
        assert conflict_branch["definite"] is False
        assert yes_branch["branch"] == "then"
        assert no_branch["branch"] == "else"
    elif dem == "D026":
        _records, classified = out
        # asserted 记录不被升格；仅 court-registry 条目构成 adjudicated
        pairs = {(r["content"], r["kind"]) for r in classified["records"]}
        assert ("loan_granted", "asserted") in pairs
        assert ("transfer_made", "evidenceContent") in pairs
        assert ("transfer_made", "adjudicated") in pairs
        assert ("loan_granted", "adjudicated") not in pairs
        assert classified["explicit_adjudications"] == ("transfer_made",)
        assert classified["refused_promotions"] == (
            {"content": "loan_granted", "source": "complaint-summary"},)
        asserted_row = next(r for r in classified["records"]
                            if r["content"] == "loan_granted")
        assert asserted_row["source"] == "complaint-summary"
        assert asserted_row["use"] == "party-allegation"
    elif dem == "D027":
        draft, section, delta, clean = out
        # 未确认项保留为 pending；改写为既成事实使语义差量失败
        assert section["included"] == ("loan_granted", "transfer_made",
                                       "fees_charged")
        assert section["pending"] == ()
        assert section["conditional_basis"] == ("fees_charged",)
        assert delta["delta"] == ()
        assert "fees_charged" in draft
        pending_case = R.draft_fact_section(
            ("loan_granted", "fees_charged"), ("loan_granted",), ())
        assert pending_case["pending"] == ("fees_charged",)
        tampered = R.semantic_delta(pending_case, ("fees_charged",))
        assert tampered["semantic_difference_failed"] is True
        assert tampered["delta"] == ("fees_charged",)
        assert clean["semantic_difference_failed"] is False
    elif dem == "D028":
        _acts, scoped = out
        # 抢劫史不入本案罪名清单；历史仅经具名规则通道
        assert [c[2] for c in scoped["charges"]] == ["dangerous-driving"]
        assert scoped["blocked_direct_history"] == \
            (("case-old", "ev-rob", "robbery", True),)
        assert [h["rule"] for h in scoped["history_channel"]] == \
            ["recidivism-art-74"]
        assert all(h["act_scope"] == "case-b03"
                   for h in scoped["history_channel"])


@pytest.mark.parametrize("dem", DEMANDS)
def test_checker_rejects_tampered(dem):
    """The independent checker must fail a tampered intermediate result
    (the checker, not the entry, is the judge of the contract)."""
    ok, _reasons, out = _POSITIVE[dem]()
    assert ok  # sanity: the honest result passes its own checker
    if dem == "D019":
        _source, _triggers, extraction = out
        tampered = dict(extraction)
        tampered["events"] = tuple(
            dict(e, span=("伪造",)) if e["type"] == "LIABILITY" else e
            for e in extraction["events"])
        bad, reasons = K.check_D019(_SOURCE, _TRIGGERS, tampered)
    elif dem == "D020":
        edges, binding = out
        tampered = dict(binding)
        tampered["bound"] = tuple(
            ("case-b03",) + e[1:] if e[0] == "case-prior" else e
            for e in binding["bound"]) + (("case-b03",) + edges[2][1:],)
        bad, reasons = K.check_D020(edges, "case-b03", tampered)
    elif dem == "D021":
        items, timeline = out
        tampered = dict(timeline)
        tampered["pending"] = ({"event": "call", "day": 2,
                                "status": "unknown"},)
        bad, reasons = K.check_D021(items, tampered)
    elif dem == "D022":
        claims, contrary, conflicts = out
        tampered = dict(conflicts)
        tampered["conflicts"] = tuple(
            dict(c, day=20) if c["day"] == 10 else c
            for c in conflicts["conflicts"])
        bad, reasons = K.check_D022(claims, contrary, tampered)
    elif dem == "D023":
        record, _missing, _negative_entry = out
        tampered = {"query": "receipt_attached", "in_record": False,
                    "negative_evidence": True,
                    "negative_allowed_in_scope": True,
                    "negation_inferred_from_missing": True,
                    "carrier": "negative-record"}
        bad, reasons = K.check_D023(record, "receipt_attached",
                                    ("receipt_attached",), tampered)
    elif dem == "D024":
        links, support = out
        tampered = dict(support)
        tampered["supports"] = dict(support["supports"])
        tampered["supports"]["ans-payment"] = support["supports"][
            "ans-payment"] + ({"span": "span-unrelated", "start": 9,
                               "end": 10, "proposition": ""},)
        bad, reasons = K.check_D024(links, len(_SOURCE), tampered)
    elif dem == "D025":
        _status, _branch, _conflict_branch, _yes_branch, _no_branch = out
        tampered = {"branch": "else", "value": "denied", "definite": True}
        bad, reasons = K.check_D025("unknown", tampered,
                                    "open-question-retained")
    elif dem == "D026":
        records, classified = out
        tampered = dict(classified)
        tampered["records"] = tuple(
            dict(r, kind="adjudicated", source="court-registry")
            if r["content"] == "loan_granted" else r
            for r in classified["records"])
        bad, reasons = K.check_D026(records, tampered)
    elif dem == "D027":
        draft, section, _delta, _clean = out
        tampered_section = dict(section, pending=())
        tampered_delta = dict(R.semantic_delta(section, ("fees_charged",)),
                              delta=(), semantic_difference_failed=False)
        bad, reasons = K.check_D027(
            draft, ("loan_granted", "transfer_made"), (),
            ("fees_charged",), tampered_section, tampered_delta)
    elif dem == "D028":
        acts, scoped = out
        tampered = dict(scoped)
        tampered["charges"] = scoped["charges"] + \
            (("case-old", "ev-rob", "robbery", True),)
        bad, reasons = K.check_D028(acts, "case-b03",
                                    (("recidivism-art-74", True),), tampered)
    assert not bad, f"{dem} checker accepted a tampered result: {reasons}"


# ---------------------------------------------------------------------------
# per-demand adverse specifics beyond the shared parametrized set
# ---------------------------------------------------------------------------


def test_D019_rejects_span_out_of_bounds_and_label_collision():
    """越界跨度与标签碰撞在入口即拒绝（外边界防御 fail-fast）."""
    with pytest.raises(ValueError):
        R.extract_events(("a", "b"),
                         (("t", "TY", (), "o", False, 1, 5)))
    with pytest.raises(ValueError):
        R.extract_events(("a", "b"),
                         (("t", "TY1", (), "o", False, 0, 1),
                          ("t", "TY2", (), "o", False, 1, 2)))


def test_D021_identical_days_stay_ordered_stable():
    """同日事件按 (day, id) 稳定排序，拓扑有效性不因并列日破坏."""
    items = (("b", 4), ("a", 4), ("c", 2))
    out = R.build_timeline(items)
    assert out["order"] == ("c", "a", "b")
    days = [t["day"] for t in out["timeline"]]
    assert days == sorted(days)


def test_D022_identical_content_never_conflicts_with_itself():
    """同一内容与自己不成矛盾（自反对不进冲突集）."""
    claims = (("d", 1, "x"), ("d", 1, "x"))
    out = R.find_conflicts(claims, (("x", "x"),))
    assert out["conflicts"] == ()


def test_D023_negative_query_outside_scope_not_granted():
    """范围外负查询不获准（只在声明的完整记录范围内开放）."""
    out = R.missing_support((("a", True),), "q", ("other",))
    assert out["negative_allowed_in_scope"] is False


def test_D025_project_status_rejects_foreign_values():
    """四值之外的状态在入口即拒绝（unknown/conflict 不被强转）."""
    assert R.project_status("yes") == "yes"
    assert R.project_status("conflict") == "conflict"
    with pytest.raises(ValueError):
        R.project_status("probably-true")
    with pytest.raises(ValueError):
        R.project_status("false-ish")


def test_D027_unconditional_pending_kept_without_tamper():
    """无篡改时差量为空（差量载体只在改写发生时非空）."""
    section = R.draft_fact_section(("a", "b"), ("a",), ())
    assert section["pending"] == ("b",)
    clean = R.semantic_delta(section, ())
    assert clean == {"delta": (), "semantic_difference_failed": False}


def test_D028_history_channel_requires_true_rule_rows():
    """规则表内未声明为 true 的条目不构成历史通道."""
    scoped = R.scope_acts((("c", "e", "act", True),), "c",
                          (("rule-1", False), ("rule-2", True)))
    assert [h["rule"] for h in scoped["history_channel"]] == ["rule-2"]
    assert scoped["charges"] == ()


# ---------------------------------------------------------------------------
# 4 — downstream consumption: run_case / step_event / run_trace
# ---------------------------------------------------------------------------


def test_downstream_pipeline_consumes_evidence():
    """run_case consumes the CaseInput assembled from the evidence results
    (the D019 occurred event type as issue, the D020 bound edge as parties,
    the D026 classification standings for the fact records); run_trace
    consumes the D019 events as evidence events plus the per-obligor
    payments."""
    # call-time imports: always the same unified copies the pipeline's own
    # lazy in-function imports resolve to (see module docstring note).
    # Call-time PATH re-assertion first: test_registration_bindings inserts
    # tools/full_math at sys.path[0] at its own import time, which happens
    # AFTER this module's import (e < r), and tools/full_math carries a
    # competing bare `reference` package (without unified_reference) that
    # would shadow tools/unified_math_v2 at the lazy-import moment.
    _v2 = str(REPO / 'tools/unified_math_v2')
    while _v2 in sys.path:
        sys.path.remove(_v2)
    sys.path.insert(0, _v2)
    from theory.spec.canonical_v2.case import RunStatus
    from theory.spec.canonical_v2.kernel import Judgment
    from unified.pipeline import run_case, run_trace, step_event
    from unified.process import LegalEventKind, ProcessEvent, gross_of

    intake = R.build_evidence_intake()
    case = R.build_case_input(intake)
    env = R.build_environment(intake)

    # the assembled carriers are exactly the evidence outputs
    assert case.issues == ("LOAN_GRANT",)  # the D019 occurred event type
    assert set(case.parties) == {"plaintiff", "defendant"}  # D020 bound edge
    assert case.claims[0].claimant == "plaintiff"
    assert case.claims[0].respondent == "defendant"
    assert case.claims[0].basis == "LOAN_GRANT"
    standings = {(f.proposition.predicate, f.standing.name)
                 for f in case.fact_records}
    # D026: only explicit court-registry entries are admitted; the asserted
    # record and the raw evidence content keep awaiting admission — no
    # implicit promotion into findings
    assert ("transfer_made", "ADMITTED_POSITIVE") in standings
    assert ("loan_granted", "ADMITTED_POSITIVE") in standings
    assert ("loan_granted", "AWAITING_ADMISSION") in standings
    assert ("transfer_made", "AWAITING_ADMISSION") in standings
    subject = case.fact_records[0].proposition.subject
    assert subject == "span:0:6"  # the D019 event's source span

    run = run_case(case, env)
    assert run.status is RunStatus.COMPLETE
    assert run.failures == ()
    judgments = run.judgments_of("c0")
    assert judgments and Judgment.ESTABLISHED in judgments

    # trace: each D019 occurred event is its own evidence event bound to
    # its span; the quoted-hypothesis triggers never became events
    initial = case.initial_state
    events = R.evidence_trace_events(intake)
    assert [e.event.event_id for e in events[:2]] == \
        ["ev-借款-0-6", "ev-责任-9-12"]
    final, notes = run_trace(initial, events, env)
    assert "ev:ev-借款-0-6" in [e.evidence_id for e in final.evidence]
    event_ids = [e.event_id for e in final.events]
    assert "pay-D1" in event_ids and "pay-D2" in event_ids
    # per-obligor payments land on the event-type basis; the totals are
    # the sum of the individual dispositions (two separate gross entries,
    # never averaged)
    assert gross_of(final, "LOAN_GRANT") == Fraction(1_000_000)
    allocated = [e for e in final.ledger
                 if e.kind.name == "GROSS_ALLOCATED"
                 and e.basis_key == "LOAN_GRANT"]
    assert sorted(e.amount for e in allocated) == [Fraction(400_000),
                                                   Fraction(600_000)]
    assert notes  # the step relation actually produced observations

    # step_event alone: one step, exactly the event's own semantics
    one = step_event(initial, events[0], env)
    assert [e.evidence_id for e in one.next_state.evidence] == \
        ["ev:ev-借款-0-6"]
    assert one.next_env is env

    # the evidence decisions stay on the bundle: the hypothesis trigger is
    # blocked (D019), the prior-case victim is outside (D020), the call is
    # undated (D021), unknown is intercepted (D025), the asserted record is
    # not promoted (D026), and the robbery history stays out (D028)
    assert [e["type"] for e in intake["extraction"]["events"]] == \
        ["LOAN_GRANT", "LIABILITY"]
    assert intake["binding"]["outside"][0][1] == "prior-victim"
    assert intake["timeline"]["pending"][0]["day"] is None
    assert intake["branch"]["definite"] is False
    assert intake["scoped"]["blocked_direct_history"][0][2] == "robbery"


# ---------------------------------------------------------------------------
# 6 — synthetic receipts through completion.validate_binding
# ---------------------------------------------------------------------------

_REQUIREMENTS = {
    r["id"]: r
    for r in json.loads((SPEC / 'REQUIREMENTS.json').read_text(encoding='utf-8'))
}

_SEMANTICS = {
    "D019": "every event row (type, actors, object, span) points back into "
            "the source text: its [start,end) coordinates slice the source "
            "verbatim; the trigger-to-type label map is collision-free "
            "(one trigger under two type labels is refused, never merged); "
            "a trigger quoted as a hypothesis never becomes an occurred "
            "event.",
    "D020": "event participants, objects, legal stages and evidence "
            "standings are bound edge by edge under an explicit case key; "
            "no row is bound to this case by positional default, so a "
            "prior-case victim stays outside this case's bindings.",
    "D021": "explicitly dated events form a strict partial order and the "
            "output timeline is a valid topological order of the day "
            "order; undated events are marked unknown/pending and never "
            "receive a precise date invented from narrative order.",
    "D022": "a contradiction is reported only with the named proposition, "
            "the same subject and the same time, a declared contrary pair "
            "and a nonempty witness; different-time or undeclared pairs "
            "stay ambiguity and both readings are preserved.",
    "D023": "missing_support(q) does not entail not-q: a query absent "
            "from the record is only missing, the no-record marker and the "
            "explicit negative-evidence record are separate carriers, and "
            "negative queries are granted only inside the declared "
            "complete-record scope.",
    "D024": "every answer's supporting span exists, has legal bounds and "
            "links to the corresponding proposition; an irrelevant "
            "citation fails the support check; redundant supports are "
            "retained.",
    "D025": "true/false/unknown/conflict stay distinct and are never "
            "coerced into one another; a conditional branch consumes only "
            "a definite yes/no — unknown and conflict are intercepted and "
            "fall back to the declared default instead of manufacturing a "
            "negated conclusion.",
    "D026": "asserted, evidence-content and adjudicated records each "
            "carry their own source and use; promotion from asserted to "
            "adjudicated requires an explicit court-registry entry, never "
            "an implicit upgrade through a summary.",
    "D027": "the drafted fact section's protected propositions are "
            "contained in the admitted facts or the declared conditional "
            "semantics; undecided items are retained as pending; an "
            "unconfirmed act rewritten as established makes the semantic "
            "delta fail (nonempty).",
    "D028": "every act carries its (case, event) scope; the current "
            "charge list contains only this case's non-historical acts; "
            "historical experience enters the current analysis only "
            "through a named admission rule — a past robbery never joins "
            "the current charge list by itself.",
}

_ENTRY = {
    "D019": "extract_events",
    "D020": "bind_roles",
    "D021": "build_timeline",
    "D022": "find_conflicts",
    "D023": "missing_support",
    "D024": "support_check",
    "D025": "project_status/decide_branch",
    "D026": "classify_records",
    "D027": "draft_fact_section/semantic_delta",
    "D028": "scope_acts",
}


def _binding_row(dem, required):
    """Template for the controller's BINDINGS.json back-fill
    (DEMAND:D019–D028 rows).  Passes completion.validate_binding as-is."""
    return {
        "id": f"DEMAND:{dem}",
        "theorem": required["theorem"],
        "contract": required["contract"],
        "proof_mode": "KERNEL_CONTRACT_PROOF",
        "formal_scope": "Group-03 evidence/event demand instance in the "
                        "shared semantic framework: this item's own "
                        "contract semantics plus the registered "
                        "evidence-identity component (conflicting "
                        "resubmission never overwrites the first "
                        "acceptance), with its adverse case executed as a "
                        "negative test.",
        "independent_semantics": _SEMANTICS[dem],
        "algorithm": f"tools/full_math/implementation/evidence_ref.py "
                     f"{_ENTRY[dem]} computes the intermediate result from "
                     f"structured input; evidence_check.check_{dem} "
                     f"re-derives the contract independently.",
        "observation_contract": "Inputs are the declared structures "
                                "(source token list with per-trigger spans "
                                "and quoted flags, per-edge case/person/"
                                "object/stage/standing rows, dated and "
                                "undated timeline items, same-subject/"
                                "same-day claim pairs with a declared "
                                "contrary table, record rows with "
                                "polarity and a negative-query scope, "
                                "answer support links with span bounds, "
                                "four-value status strings with a branch "
                                "default, kind/content/source/use record "
                                "rows, draft/admitted/conditional/tamper "
                                "proposition lists, per-act (case, event, "
                                "historical) rows with named history "
                                "rules); outputs are exactly the contract "
                                "quantities (source-pointing event spans "
                                "with blocked quoted triggers and the "
                                "collision-free label map, case-keyed "
                                "binding edges, the topological timeline "
                                "with unknown pending, witnessed "
                                "conflicts with preserved ambiguity "
                                "readings, the missing/negative carrier "
                                "split, passing and rejected support "
                                "spans, the identity status projection "
                                "with intercepted branches, classified "
                                "records with refused promotions, the "
                                "section/pending split with the semantic "
                                "delta, and the scoped charge list with "
                                "the named history channel).",
        "external_assumptions": "Trigger-word recall and event "
                                "understanding, multi-subject coreference "
                                "resolution, event date extraction, "
                                "conflict-discovery recall and pragmatic "
                                "interpretation, real-world evidence "
                                "availability, annotation faithfulness, "
                                "reliability of actual findings, "
                                "free-narrative completeness and the "
                                "truth of external legal facts remain "
                                "external validation obligations, not "
                                "part of this registration.",
        "proof_sources": [
            "proofs/lean/juris_lean/JurisLean/FullMath/Contracts.lean",
            "proofs/lean/juris_lean/JurisLean/FullMath/Acceptance.lean",
        ],
        "implementation_sources": [
            "tools/full_math/implementation/evidence_ref.py",
            "tools/full_math/implementation/evidence_check.py",
        ],
        "test_ids": [
            "tools/full_math/implementation_tests::test_evidence_group03.py::"
            f"test_demand_positive[{dem}]",
            "tools/full_math/implementation_tests::test_evidence_group03.py::"
            f"test_demand_counterexample[{dem}]",
            "tools/full_math/implementation_tests::test_evidence_group03.py::"
            "test_downstream_pipeline_consumes_evidence",
        ],
        "negative_test_ids": [
            "tools/full_math/implementation_tests::test_evidence_group03.py::"
            f"test_checker_rejects_tampered[{dem}]",
        ],
        "semantic_links": [
            "JurisLean.FullMath.Probability.dedup_conflict_not_overwrite",
        ],
    }


@pytest.mark.parametrize("dem", DEMANDS)
def test_b03_binding_receipt(dem):
    """Synthetic receipt: the binding row for DEMAND:D0XX passes
    completion.validate_binding against the real repository files."""
    required = _REQUIREMENTS[f"DEMAND:{dem}"]
    C.validate_binding(_binding_row(dem, required), required, repo=REPO)


@pytest.mark.parametrize("dem", DEMANDS)
def test_b03_binding_receipt_negative(dem):
    """A tampered receipt (swapped theorem) is rejected."""
    required = _REQUIREMENTS[f"DEMAND:{dem}"]
    row = dict(_binding_row(dem, required))
    row["theorem"] = "JurisLean.FullMath.Acceptance.nonexistent_demand"
    with pytest.raises(C.EvidenceError):
        C.validate_binding(row, required, repo=REPO)
