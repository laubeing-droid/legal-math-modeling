"""W4 behavior batch (T116-T121) downstream consumption tests.

Consumes the EXISTING public process entries — ``step_event`` / ``run_trace``
/ ``outstanding_of`` / ``gross_of`` / ``visible_evidence`` — without touching
pipeline.py or case.py (分包 O 纪律：不改 pipeline.py/case.py).

T121 at the process layer: an actual event updates the effect/observation
layers and the SAME evaluation rule (outstanding = titles − satisfied) is
re-evaluated on the new state: an effective award raises the outstanding, a
payment lowers it, a revocation supersedes the title without erasing the
payment history (§9.1/§9.2/§9.4: 事件→效力/观察→同一规则重新评价；撤销不令
已付消失).

T119 at the process layer: one ACTUAL history read through three same-path
projections — the ledger reading (gross receipts), the legal reading
(outstanding), and the visibility reading (evidence known by a day) give
different answers about the same events (认识/现实分离: a payment can be
physically received before it is legally satisfiable, and before evidence of
it is visible).
"""

from fractions import Fraction as Q

import pytest

from theory.spec.canonical_v2.case import (
    CaseEvent,
    ProcessState,
)
from theory.spec.canonical_v2.kernel import NormState

from unified.process import (
    LegalEventKind,
    ProcessEvent,
    gross_of,
    outstanding_of,
    run_trace,
    step_event,
)


def _event(eid, kind_value, occurred=5, observed=6, obj="loan"):
    return CaseEvent(
        event_id=eid, event_type=kind_value,
        occurred_at=occurred, observed_at=observed, object_ref=obj,
    )


def _state(day=10):
    return ProcessState(
        r=NormState(relations=()),
        environment_id="env",
        target_day=day,
        as_of_day=day,
    )


def _award(amount=Q(100)):
    return ProcessEvent(
        event=_event("t1", "award"),
        kind=LegalEventKind.AWARD_EFFECTIVE,
        basis_key="loan",
        amount=amount,
        authority_ref="court:2026-1",
    )


def _pay(amount, eid="p1"):
    return ProcessEvent(
        event=_event(eid, "payment"),
        kind=LegalEventKind.PAYMENT_PERFORMED,
        basis_key="loan",
        amount=amount,
        debt_order=("loan",),
    )


def test_process_backflow_same_rule_reeval():
    """T121 下游（§9.1/§9.4）：实际事件逐个施加，同一 outstanding 规则在
    每个新状态上重评——判前 0 → 判后 100 → 支付后 40；撤销判决 → 0 而已付
    60 保留（gross 不清零）。"""
    state0 = _state()
    assert outstanding_of(state0, "loan") == 0

    state1 = step_event(state0, _award()).next_state
    assert outstanding_of(state1, "loan") == 100  # 同一规则重评：判后

    state2 = step_event(state1, _pay(Q(60))).next_state
    assert outstanding_of(state2, "loan") == 40  # 同一规则重评：付后
    assert gross_of(state2, "loan") == 60

    revoke = ProcessEvent(
        event=_event("t2", "revoke"),
        kind=LegalEventKind.AWARD_REVOKED,
        basis_key="loan",
        authority_ref="court:2026-1",
    )
    state3 = step_event(state2, revoke).next_state
    assert outstanding_of(state3, "loan") == 0  # 效力层更新：标题被取代
    assert gross_of(state3, "loan") == 60  # 已付不清零（§9.2）


def test_run_trace_folds_prefix_consistently():
    """run_trace 折叠与逐步 step_event 一致：每步只见其前驱（§9.1）。"""
    events = [_award(), _pay(Q(60)), _pay(Q(10), "p2")]
    folded, notes = run_trace(_state(), events)
    assert outstanding_of(folded, "loan") == 30
    assert gross_of(folded, "loan") == 70
    assert len(folded.events) == 3
    assert isinstance(notes, tuple)

    manual = _state()
    for ev in events:
        manual = step_event(manual, ev).next_state
    assert outstanding_of(manual, "loan") == outstanding_of(folded, "loan")


def test_oversupply_never_negative():
    """同一规则良态：超额支付不产生负 outstanding（§6.1 账层）。"""
    state = step_event(step_event(_state(), _award(Q(10))).next_state,
                       _pay(Q(60))).next_state
    assert outstanding_of(state, "loan") == 0
    assert gross_of(state, "loan") == 60  # 实收轨迹全额保留


def test_process_layer_three_readings_of_one_history():
    """T119 下游：同一段实际历史的三种读数不同——物理收付 60、法律未清 40、
    证据可见时点分立（known_at > occurred_at 时裁判尚未可见）。"""
    state = step_event(step_event(_state(), _award()).next_state,
                       _pay(Q(60))).next_state
    causal_like = gross_of(state, "loan")          # 物理层：实际收付
    legal_like = outstanding_of(state, "loan")     # 法律层：未清余额
    assert causal_like == 60 and legal_like == 40
    assert causal_like != legal_like  # 同一历史，两种读数不同

    late_evidence = ProcessEvent(
        event=_event("e1", "evidence", occurred=1, observed=100),
        kind=LegalEventKind.EVIDENCE_SUBMITTED,
    )
    state2 = step_event(state, late_evidence).next_state
    early = state2.visible_evidence(6)   # 裁判时点未见的证据
    late = state2.visible_evidence(100)  # 其后可见
    assert len(early) == 0 and len(late) == 1  # 认识/现实分离


def test_downstream_step_failures_are_fail_fast():
    """无权限的生效事件在下游同样 fail-fast（与构造门同纪律）。"""
    with pytest.raises(ValueError, match="authority"):
        step_event(_state(), ProcessEvent(
            event=_event("t-bad", "award"),
            kind=LegalEventKind.AWARD_EFFECTIVE,
            basis_key="loan",
            amount=Q(100),
        ))
