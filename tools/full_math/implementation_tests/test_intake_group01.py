"""W2-A batch B01 acceptance tests: D001-D008, group 01 接案、问题与主体识别.

Six pieces per demand (docs/full-math/W2B_CLASSIFICATION.md §5.4):

1. Lean contract  — Contracts.demand_D001..D008 restated as this item's own
   semantics (verified by CI; the registration-format tests live in
   test_registration_bindings.py).
2. Python entry   — tools/full_math/implementation/intake_ref.py per-item
   entries computing the intermediate result from real structured input.
3. Independent checker — intake_check.py re-derives the contract inline;
   no witness callbacks, no expectations from the main implementation.
4. Downstream consumption — unified.pipeline run_case / step_event /
   run_trace consume the intake results through the adapters in
   intake_ref (build_case_input / build_environment / intake_trace_events).
5. Positive and adverse cases — the ALL_134 counterexample field of each
   demand is executed with per-item expectations.
6. Synthetic receipt — completion.validate_binding rows for DEMAND:D001-D008.
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
# tool trees; evict cached copies so this tree re-resolves them against
# its own path entries (same discipline as tools/unified_math_v2 conftest).
for _shared in ("reference", "unified", "unified_v21"):
    for _name in [m for m in sys.modules
                  if m == _shared or m.startswith(_shared + ".")]:
        del sys.modules[_name]

from tools.full_math.implementation import intake_check as K  # noqa: E402
from tools.full_math.implementation import intake_ref as R  # noqa: E402
import completion as C  # noqa: E402
from unified.pipeline import run_case, run_trace, step_event  # noqa: E402
from unified.process import gross_of  # noqa: E402
from theory.spec.canonical_v2.case import CaseEvent, RunStatus  # noqa: E402
from theory.spec.canonical_v2.kernel import Judgment  # noqa: E402
from unified.process import LegalEventKind, ProcessEvent  # noqa: E402

DEMANDS = ("D001", "D002", "D003", "D004", "D005", "D006", "D007", "D008")


# ---------------------------------------------------------------------------
# 2/3/5 — entry + independent checker, positive and adverse (per item)
# ---------------------------------------------------------------------------


def _run_D001():
    """同一咨询含欠款与名誉请求，不能因主主题只报一个（ALL_134 反例字段）."""
    scope = ("debt_claim", "reputation_claim")
    paragraphs = ("debt_claim", "reputation_claim", "unrelated_note")
    out = R.classify_topics(scope, paragraphs)
    ok, reasons = K.check_D001(scope, paragraphs, out)
    return ok, reasons, out


def _run_D002():
    """同一行为同时涉民事责任与犯罪线索，不强制二选一（ALL_134 反例字段）."""
    table = (("case-x", True, True),)
    facts = ("civil_liability", "criminal_clue")
    out = R.classify_route(table, "case-x", facts)
    ok, reasons = K.check_D002(table, "case-x", facts, out)
    return ok, reasons, out


def _run_D003():
    """法定代表人签字不得自动变成其个人承担全部公司债务（反例字段）."""
    bindings = (
        ("mgr", "company-x", "trial", "legal_rep_signing", "board_minutes"),
        ("mgr", "company-x", "trial", "personal_debtor", "iou_note"),
    )
    out = R.resolve_role(bindings, "mgr", "company-x", "trial")
    ok, reasons = K.check_D003(bindings, "mgr", "company-x", "trial", out)
    return ok, reasons, (out, bindings)


def _run_D004():
    """交换两被告刑期而整案平均不变，检查仍须失败（反例字段）."""
    per_defendant = {"D1": True, "D2": False}
    required = ("D1", "D2")
    case_ok = R.case_correctness(per_defendant, required)
    ok_case, reasons_case = K.check_D004(per_defendant, required, case_ok)
    sentences = {"D1": 30, "D2": 24}
    swap = R.swap_detected(sentences, "D1", "D2")
    ok_swap, reasons_swap = K.check_D004_swap(sentences, "D1", "D2", swap)
    return ok_case and ok_swap, reasons_case + reasons_swap, (case_ok, swap)


def _run_D005():
    """同名异码不合并（反例字段，前半）."""
    snapshot = (
        (111, "Alpha Ltd", 0),
        (222, "Alpha Ltd", 0),
        (333, "Beta Ltd", 50),
    )
    out = {
        "by_code_a": R.resolve_by_code(snapshot, 111),
        "by_code_b": R.resolve_by_code(snapshot, 222),
        "alias_key": R.alias_join_canonical_key(snapshot, "Alpha Ltd", 10),
    }
    ok, reasons = K.check_D005(snapshot, 111, 222, "Alpha Ltd", 10, out)
    return ok, reasons, out


def _run_D006():
    """两公司同地址不能由等号传播成同一债务人（反例字段）."""
    entities = ((1, "corp", "addr-9"), (2, "corp", "addr-9"))
    rules = (("D1", ("D2", "joint_debt_declaration")),)
    merge_decisions = {
        (a[0], b[0]): R.merged_by_equality(a, b)
        for a in entities for b in entities
    }
    out = {"edges": R.responsibility_edges(rules),
           "merge_decisions": merge_decisions}
    ok, reasons = K.check_D006(entities, rules, out)
    return ok, reasons, out


def _run_D007():
    """正确解析法院代字不等于该法院有管辖权（反例字段）."""
    court_table = (("Y11", "Y-Court", "intermediate"),)
    sources = ()  # 无适用法源
    court = R.resolve_court(court_table, "Y11")
    jurisdiction = R.jurisdiction_status(sources, 10, (), "Y11")
    out = {"court": court, "jurisdiction": jurisdiction}
    ok, reasons = K.check_D007(court_table, "Y11", sources, 10, (), "Y11", out)
    return ok, reasons, out


def _run_D008():
    """本金请求与担保责任请求不得共用无主体的金额字段（反例字段）."""
    rows = (
        {"claimant": "C", "respondent": "D", "basis": "loan",
         "object": "principal", "remedy": "payment", "scope": "loan",
         "amount_fen": 1_000_000},
        {"claimant": "C", "respondent": "G", "basis": "surety",
         "object": "surety_debt", "remedy": "payment", "scope": "loan",
         "amount_fen": 500_000},
    )
    out = {"claims": R.parse_claims(rows)}
    ok, reasons = K.check_D008(rows, out)
    return ok, reasons, (rows, out["claims"])


_POSITIVE = {"D001": _run_D001, "D002": _run_D002, "D003": _run_D003,
             "D004": _run_D004, "D005": _run_D005, "D006": _run_D006,
             "D007": _run_D007, "D008": _run_D008}


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
    if dem == "D001":
        # 不能因主主题只报一个：两个并列争点各有一个规范需求对象
        assert set(out["objects"]) == {"debt_claim", "reputation_claim"}
        assert out["objects"]["debt_claim"]["demand_object"] != \
            out["objects"]["reputation_claim"]["demand_object"]
        assert "unrelated_note" in out["residual"]
    elif dem == "D002":
        # 并行不强制二选一：民刑并行是一个独立路由值；事实层原样保留
        assert out["route"] == R.ROUTE_PARALLEL
        assert out["facts"] == ("civil_liability", "criminal_clue")
    elif dem == "D003":
        resolved, bindings = out
        # 签字角色绑定存在，但未声明的个人债务人绑定不会被发明
        assert resolved["key"] == ("mgr", "company-x", "trial",
                                   "legal_rep_signing")
        undeclared = R.resolve_role(bindings, "mgr", "company-debt", "trial")
        assert undeclared["binding"] is None
        # 主体、角色为不同字段：同主体不同角色的键不同
        assert R.role_binding_key(bindings[0]) != R.role_binding_key(bindings[1])
    elif dem == "D004":
        case_ok, swap = out
        # 整案不正确（一名被告映射错误）；交换后总量不变而逐人检查失败
        assert case_ok is False
        assert swap is True
        assert sum({"D1": 30, "D2": 24}.values()) == \
            sum({"D1": 24, "D2": 30}.values())
    elif dem == "D005":
        # 同名异码：两条记录各自解析，不合并
        assert out["by_code_a"][0] == 111 and out["by_code_b"][0] == 222
        assert out["by_code_a"] != out["by_code_b"]
        assert out["alias_key"] == 111
    elif dem == "D006":
        # 同地址不合并；无规则声明则无责任边
        assert out["merge_decisions"][(1, 2)] is False
        assert out["edges"] == (("D1", "D2"),)
        assert R.responsibility_edges(()) == ()
    elif dem == "D007":
        # 代字解析成功，但管辖仍是待定
        assert out["court"] == ("Y11", "Y-Court", "intermediate")
        assert out["jurisdiction"] == ("pending", None)
    elif dem == "D008":
        rows, claims = out
        # 两条请求保留关联与差异：各自金额键=各自主体对
        assert claims[0]["party_pair"] == ("C", "D")
        assert claims[1]["party_pair"] == ("C", "G")
        assert claims[0] != claims[1]
        assert rows[0]["amount_fen"] != rows[1]["amount_fen"]


@pytest.mark.parametrize("dem", DEMANDS)
def test_checker_rejects_tampered(dem):
    """The independent checker must fail a tampered intermediate result
    (the checker, not the entry, is the judge of the contract)."""
    ok, _reasons, out = _POSITIVE[dem]()
    assert ok  # sanity: the honest result passes its own checker
    if dem == "D001":
        tampered = dict(out, topics=("debt_claim",),
                        objects={"debt_claim": out["objects"]["debt_claim"]})
        bad, reasons = K.check_D001(("debt_claim", "reputation_claim"),
                                    ("debt_claim", "reputation_claim",
                                     "unrelated_note"), tampered)
    elif dem == "D002":
        tampered = dict(out, route=R.ROUTE_CIVIL)
        bad, reasons = K.check_D002((("case-x", True, True),), "case-x",
                                    ("civil_liability", "criminal_clue"),
                                    tampered)
    elif dem == "D003":
        resolved, bindings = out
        auto_created = dict(resolved,
                            binding=("mgr", "company-x", "trial",
                                     "personal_debtor", ""),
                            key=("mgr", "company-x", "trial",
                                 "personal_debtor"))
        bad, reasons = K.check_D003(bindings, "mgr", "company-x", "trial",
                                    auto_created)
    elif dem == "D004":
        bad, reasons = K.check_D004({"D1": True, "D2": False},
                                    ("D1", "D2"), True)
        assert not bad
        bad2, reasons2 = K.check_D004_swap({"D1": 30, "D2": 24},
                                           "D1", "D2", False)
        bad, reasons = bad2, reasons2
    elif dem == "D005":
        tampered = dict(out, alias_key=222)
        snapshot = ((111, "Alpha Ltd", 0), (222, "Alpha Ltd", 0))
        bad, reasons = K.check_D005(snapshot, 111, 222, "Alpha Ltd", 10,
                                    tampered)
    elif dem == "D006":
        tampered = dict(out, edges=(("D1", "D2"), ("D2", "D1")))
        entities = ((1, "corp", "addr-9"), (2, "corp", "addr-9"))
        bad, reasons = K.check_D006(
            entities, (("D1", ("D2", "joint_debt_declaration")),), tampered)
    elif dem == "D007":
        tampered = dict(out, jurisdiction=("applies", {"fake": 1}))
        bad, reasons = K.check_D007((("Y11", "Y-Court", "intermediate"),),
                                    "Y11", (), 10, (), "Y11", tampered)
    elif dem == "D008":
        rows = (
            {"claimant": "C", "respondent": "D", "basis": "loan",
             "object": "principal", "remedy": "payment", "scope": "loan",
             "amount_fen": 1_000_000},
            {"claimant": "C", "respondent": "G", "basis": "surety",
             "object": "surety_debt", "remedy": "payment", "scope": "loan",
             "amount_fen": 500_000},
        )
        merged = {"claims": (out[1][0],
                             dict(out[1][0], basis="surety"))}
        bad, reasons = K.check_D008(rows, merged)
    assert not bad, f"{dem} checker accepted a tampered result: {reasons}"


def test_D008_rejects_subjectless_amount():
    """无主体的金额字段在入口处即被拒绝（不静默合并）."""
    with pytest.raises(ValueError):
        R.parse_claim({"claimant": "C", "respondent": "", "basis": "loan",
                       "object": "principal", "remedy": "payment",
                       "scope": "loan", "amount_fen": 1})


def test_D005_rename_same_code_by_time():
    """更名前后同码按时间处理（反例字段，后半）."""
    snapshot = (
        (333, "OldName Ltd", 0),
        (333, "Beta Ltd", 50),
    )
    assert R.alias_join_canonical_key(snapshot, "OldName Ltd", 10) == 333
    assert R.alias_join_canonical_key(snapshot, "Beta Ltd", 60) == 333
    assert R.alias_lookup(snapshot, "Beta Ltd", 10) is None  # 未生效不命中


# ---------------------------------------------------------------------------
# 4 — downstream consumption: run_case / step_event / run_trace
# ---------------------------------------------------------------------------


def test_downstream_pipeline_consumes_intake():
    """run_case consumes the CaseInput assembled from the intake results
    (D001 issues, D003 parties, D005 canonical subject, D008 claims);
    run_trace consumes the per-defendant payment dispositions (D004) on
    the declared responsibility basis (D006) and the intake evidence."""
    intake = R.build_loan_intake()
    case = R.build_case_input(intake)
    env = R.build_environment(intake)

    # the assembled carriers are exactly the intake outputs
    assert case.issues == ("loan",)  # D001 objects
    assert set(case.parties) == {"C", "D"}  # D003 bindings
    assert case.claims[0].claimant == "C" and case.claims[0].respondent == "D"
    assert case.fact_records[0].proposition.subject == "911100001"  # D005 key

    run = run_case(case, env)
    assert run.status is RunStatus.COMPLETE
    assert run.failures == ()
    judgments = run.judgments_of("c0")
    assert judgments and Judgment.ESTABLISHED in judgments

    # trace: intake evidence event + per-defendant payments (separate
    # events, never averaged)
    initial = case.initial_state
    evidence_event = ProcessEvent(
        event=CaseEvent(event_id="ev-loan-contract",
                        event_type="EVIDENCE_SUBMITTED",
                        occurred_at=5, observed_at=6,
                        object_ref="loan_contract_signed"),
        kind=LegalEventKind.EVIDENCE_SUBMITTED,
    )
    events = (evidence_event,) + R.intake_trace_events(intake)
    final, notes = run_trace(initial, events, env)
    assert "ev:ev-loan-contract" in [e.evidence_id for e in final.evidence]
    event_ids = [e.event_id for e in final.events]
    assert "pay-D1" in event_ids and "pay-D2" in event_ids
    # per-defendant payments land on the declared basis; the totals are
    # the sum of the individual dispositions (D004 keeps per-defendant
    # visibility: two separate gross-allocated entries)
    assert gross_of(final, "loan") == Fraction(5_000_000)
    allocated = [e for e in final.ledger
                 if e.kind.name == "GROSS_ALLOCATED" and e.basis_key == "loan"]
    assert sorted(e.amount for e in allocated) == [Fraction(2_000_000),
                                                   Fraction(3_000_000)]
    assert notes  # the step relation actually produced observations

    # step_event alone: one step, exactly the event's own semantics
    one = step_event(initial, evidence_event, env)
    assert [e.evidence_id for e in one.next_state.evidence] == \
        ["ev:ev-loan-contract"]
    assert one.next_env is env

    # D007 jurisdiction stays on the bundle, separate from the pipeline's
    # own jurisdiction axis
    assert intake["jurisdiction_status"] == ("pending", None)


# ---------------------------------------------------------------------------
# 6 — synthetic receipts through completion.validate_binding
# ---------------------------------------------------------------------------

_REQUIREMENTS = {
    r["id"]: r
    for r in json.loads((SPEC / 'REQUIREMENTS.json').read_text(encoding='utf-8'))
}

_SEMANTICS = {
    "D001": "topics(out) is inside the declared Topics_scope; every confirmed "
            "parallel issue has its own canonical demand object; unclassified "
            "paragraphs enter residual.",
    "D002": "route(s) allows civil, criminal, parallel or pending; a declared "
            "parallel is returned as-is; classification never rewrites the "
            "admitted facts.",
    "D003": "every Role(person,matter,stage) binding is resolved from the "
            "declared binding table; person, role and name are distinct typed "
            "fields.",
    "D004": "per-defendant result edges keep the same actor_id, act set and "
            "case; case correctness = every required per-defendant mapping; "
            "a disposition swap stays detected while totals match.",
    "D005": "for a fixed registry snapshot, canonical-key (registration code) "
            "join and alias resolution equal the independent table semantics; "
            "same name with different codes never merges; same code across a "
            "rename resolves by validity time.",
    "D006": "natural person, legal person, affiliate and representative "
            "relations are not identity equality; responsibility edges are "
            "generated only by explicitly declared rules.",
    "D007": "court code resolves to (institution, level) by the declared "
            "table; jurisdiction is a separate applicable-source decision and "
            "stays pending without an applicable source.",
    "D008": "Claim=(claimant,respondent,basis,object,remedy,scope); every "
            "amount field is keyed to a named party pair; relations and "
            "differences among claims are preserved.",
}

_ENTRY = {
    "D001": "classify_topics", "D002": "classify_route", "D003": "resolve_role",
    "D004": "case_correctness/swap_detected", "D005": "resolve_registry",
    "D006": "responsibility_edges/merged_by_equality",
    "D007": "resolve_court/jurisdiction_status", "D008": "parse_claims",
}


def _binding_row(dem, required):
    return {
        "id": f"DEMAND:{dem}",
        "theorem": required["theorem"],
        "contract": required["contract"],
        "proof_mode": "KERNEL_CONTRACT_PROOF",
        "formal_scope": "Group-01 intake demand instance in the shared "
                        "semantic framework: this item's own contract "
                        "semantics plus the registered locator/identity "
                        "separation component, with its adverse case "
                        "executed as a negative test.",
        "independent_semantics": _SEMANTICS[dem],
        "algorithm": f"tools/full_math/implementation/intake_ref.py "
                     f"{_ENTRY[dem]} computes the intermediate result from "
                     f"structured input; intake_check.check_{dem} "
                     f"re-derives the contract independently.",
        "observation_contract": "Inputs are the declared tables (scope/"
                                "paragraphs, route table, binding table, "
                                "per-defendant maps, registry snapshot, "
                                "rules, court table, claim rows); outputs "
                                "are exactly the contract quantities "
                                "(topics/residual/objects, route+facts, "
                                "binding+typed key, per-defendant "
                                "correctness and swap detection, canonical "
                                "keys, edges and merge decisions, court "
                                "and jurisdiction status, claim records "
                                "with party-pair amount keys).",
        "external_assumptions": "Truth of external facts, natural-language "
                                "intake coverage and misclassification "
                                "rates remain external validation "
                                "obligations, not part of this "
                                "registration.",
        "proof_sources": [
            "proofs/lean/juris_lean/JurisLean/FullMath/Contracts.lean",
            "proofs/lean/juris_lean/JurisLean/FullMath/Acceptance.lean",
        ],
        "implementation_sources": [
            "tools/full_math/implementation/intake_ref.py",
            "tools/full_math/implementation/intake_check.py",
        ],
        "test_ids": [
            "tools/full_math/implementation_tests::test_intake_group01.py::"
            f"test_demand_positive[{dem}]",
            "tools/full_math/implementation_tests::test_intake_group01.py::"
            f"test_demand_counterexample[{dem}]",
            "tools/full_math/implementation_tests::test_intake_group01.py::"
            "test_downstream_pipeline_consumes_intake",
        ],
        "negative_test_ids": [
            "tools/full_math/implementation_tests::test_intake_group01.py::"
            f"test_checker_rejects_tampered[{dem}]",
        ],
        "semantic_links": ["JurisLean.FullMath.Core.locator_not_identity"],
    }


@pytest.mark.parametrize("dem", DEMANDS)
def test_b01_binding_receipt(dem):
    """Synthetic receipt: the binding row for DEMAND:D00X passes
    completion.validate_binding against the real repository files."""
    required = _REQUIREMENTS[f"DEMAND:{dem}"]
    C.validate_binding(_binding_row(dem, required), required, repo=REPO)


@pytest.mark.parametrize("dem", DEMANDS)
def test_b01_binding_receipt_negative(dem):
    """A tampered receipt (swapped theorem) is rejected."""
    required = _REQUIREMENTS[f"DEMAND:{dem}"]
    row = dict(_binding_row(dem, required))
    row["theorem"] = "JurisLean.FullMath.Acceptance.nonexistent_demand"
    with pytest.raises(C.EvidenceError):
        C.validate_binding(row, required, repo=REPO)
