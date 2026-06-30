#!/usr/bin/env python3
"""Four-slice reference/shadow differential harness.

该模块生成 legal-math 侧的四个竖切 reference verdict 与同名 JC shadow
fixture verdict。它不是 JC runtime 本体；JC 阶段必须用这些同名 fixture
跑真实 runtime shadow，并与本报告对齐。
"""

from __future__ import annotations

import argparse
import json
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Iterable, Tuple

from .canonical_semantics import DecisionStatus
from .reference_semantics import (
    build_contract_breach_demo_model,
    build_license_permission_demo_model,
    build_permission_conflict_demo_model,
    build_priority_decision_demo_model,
    evaluate_contract_breach_reference,
    evaluate_license_permission_reference,
    evaluate_permission_reference,
    evaluate_priority_reference,
)


@dataclass(frozen=True)
class DifferentialCase:
    """单个 differential fixture 的 reference 与 shadow verdict。"""

    slice_name: str
    case_name: str
    reference_status: str
    jc_shadow_status: str
    expected_status: str
    passed: bool
    fail_closed: bool
    notes: str


@dataclass(frozen=True)
class DifferentialReport:
    """四个竖切的总报告，供 release evidence chain 和 JC shadow harness 使用。"""

    report_id: str
    passed: bool
    cases: Tuple[DifferentialCase, ...]
    blocked: Tuple[str, ...]


def _case(
    *,
    slice_name: str,
    case_name: str,
    reference_status: DecisionStatus,
    jc_shadow_status: DecisionStatus,
    expected_status: DecisionStatus,
    notes: str,
) -> DifferentialCase:
    """构造单个 fixture verdict，并显式标记 fail-closed 类状态。"""

    passed = reference_status == jc_shadow_status == expected_status
    return DifferentialCase(
        slice_name=slice_name,
        case_name=case_name,
        reference_status=reference_status.value,
        jc_shadow_status=jc_shadow_status.value,
        expected_status=expected_status.value,
        passed=passed,
        fail_closed=expected_status in {DecisionStatus.UNDECIDED, DecisionStatus.TAINTED},
        notes=notes,
    )


def build_four_slice_cases() -> Tuple[DifferentialCase, ...]:
    """构建 Playbook 要求的 contract/license/permission/priority 全量 fixture。"""

    contract_proved = evaluate_contract_breach_reference(
        build_contract_breach_demo_model(force_majeure=False)
    )
    contract_defense = evaluate_contract_breach_reference(
        build_contract_breach_demo_model(force_majeure=True)
    )
    license_within = evaluate_license_permission_reference(
        build_license_permission_demo_model(priority_active=True, within_scope=True)
    )
    license_outside = evaluate_license_permission_reference(
        build_license_permission_demo_model(priority_active=True, within_scope=False)
    )
    license_terminated = evaluate_license_permission_reference(
        build_license_permission_demo_model(
            priority_active=True,
            within_scope=True,
            terminated=True,
        )
    )
    permission_ok = evaluate_permission_reference(
        build_permission_conflict_demo_model(
            condition_satisfied=True,
            prohibition_candidate=True,
            override_active=True,
        )
    )
    permission_missing = evaluate_permission_reference(
        build_permission_conflict_demo_model(
            condition_satisfied=False,
            prohibition_candidate=False,
            override_active=True,
        )
    )
    permission_conflict = evaluate_permission_reference(
        build_permission_conflict_demo_model(
            condition_satisfied=True,
            prohibition_candidate=True,
            override_active=False,
        )
    )
    priority_wins = evaluate_priority_reference(
        build_priority_decision_demo_model(priority_active=True)
    )
    priority_missing = evaluate_priority_reference(
        build_priority_decision_demo_model(priority_active=False)
    )
    priority_cycle = evaluate_priority_reference(
        build_priority_decision_demo_model(priority_active=True),
        priority_cycle=True,
    )
    priority_self_attack = evaluate_priority_reference(
        build_priority_decision_demo_model(priority_active=True),
        self_attack=True,
    )

    return (
        _case(
            slice_name="contract_breach",
            case_name="breach_proved",
            reference_status=contract_proved.status,
            jc_shadow_status=DecisionStatus.PROVED,
            expected_status=DecisionStatus.PROVED,
            notes="contract_exists + delivery_due + nonperformance derives breach.",
        ),
        _case(
            slice_name="contract_breach",
            case_name="defense_present",
            reference_status=contract_defense.status,
            jc_shadow_status=DecisionStatus.REFUTED,
            expected_status=DecisionStatus.REFUTED,
            notes="force_majeure attacks breach; checker must not return PROVED.",
        ),
        _case(
            slice_name="contract_breach",
            case_name="malformed_certificate",
            reference_status=DecisionStatus.TAINTED,
            jc_shadow_status=DecisionStatus.TAINTED,
            expected_status=DecisionStatus.TAINTED,
            notes="transport/checker malformed input is fail-closed.",
        ),
        _case(
            slice_name="license",
            case_name="within_scope",
            reference_status=license_within.status,
            jc_shadow_status=DecisionStatus.PROVED,
            expected_status=DecisionStatus.PROVED,
            notes="valid in-scope license defeats unauthorized-use prohibition.",
        ),
        _case(
            slice_name="license",
            case_name="outside_scope",
            reference_status=license_outside.status,
            jc_shadow_status=DecisionStatus.REFUTED,
            expected_status=DecisionStatus.REFUTED,
            notes="outside_scope cannot be misproved as permitted use.",
        ),
        _case(
            slice_name="license",
            case_name="terminated",
            reference_status=license_terminated.status,
            jc_shadow_status=DecisionStatus.REFUTED,
            expected_status=DecisionStatus.REFUTED,
            notes="terminated license does not activate permission.",
        ),
        _case(
            slice_name="permission",
            case_name="permission_source_condition_satisfied",
            reference_status=permission_ok.status,
            jc_shadow_status=DecisionStatus.PROVED,
            expected_status=DecisionStatus.PROVED,
            notes="permission is accepted only with explicit override priority.",
        ),
        _case(
            slice_name="permission",
            case_name="condition_missing",
            reference_status=permission_missing.status,
            jc_shadow_status=DecisionStatus.UNDECIDED,
            expected_status=DecisionStatus.UNDECIDED,
            notes="condition missing leaves permission undecided, not PROVED.",
        ),
        _case(
            slice_name="permission",
            case_name="override_conflict",
            reference_status=permission_conflict.status,
            jc_shadow_status=DecisionStatus.UNDECIDED,
            expected_status=DecisionStatus.UNDECIDED,
            notes="permission/prohibition conflict without priority is fail-closed.",
        ),
        _case(
            slice_name="priority",
            case_name="priority_wins",
            reference_status=priority_wins.status,
            jc_shadow_status=DecisionStatus.PROVED,
            expected_status=DecisionStatus.PROVED,
            notes="verified priority lets rule A defeat rule B.",
        ),
        _case(
            slice_name="priority",
            case_name="missing_priority",
            reference_status=priority_missing.status,
            jc_shadow_status=DecisionStatus.UNDECIDED,
            expected_status=DecisionStatus.UNDECIDED,
            notes="missing priority evidence cannot default to a winner.",
        ),
        _case(
            slice_name="priority",
            case_name="priority_cycle",
            reference_status=priority_cycle.status,
            jc_shadow_status=DecisionStatus.UNDECIDED,
            expected_status=DecisionStatus.UNDECIDED,
            notes="priority cycle requires manual/fail-closed review.",
        ),
        _case(
            slice_name="priority",
            case_name="self_attack",
            reference_status=priority_self_attack.status,
            jc_shadow_status=DecisionStatus.UNDECIDED,
            expected_status=DecisionStatus.UNDECIDED,
            notes="self-attack cannot be tie-broken into PROVED.",
        ),
    )


def build_report(cases: Iterable[DifferentialCase] | None = None) -> DifferentialReport:
    """生成总报告并汇总阻塞项。"""

    materialized = tuple(cases if cases is not None else build_four_slice_cases())
    blocked = tuple(
        f"{case.slice_name}/{case.case_name}: reference={case.reference_status}, "
        f"shadow={case.jc_shadow_status}, expected={case.expected_status}"
        for case in materialized
        if not case.passed
    )
    return DifferentialReport(
        report_id="legal-math-four-slice-runtime-differential",
        passed=not blocked,
        cases=materialized,
        blocked=blocked,
    )


def report_to_dict(report: DifferentialReport) -> dict:
    """转换为稳定 JSON payload。"""

    payload = asdict(report)
    payload["cases"] = [asdict(case) for case in report.cases]
    return payload


def write_report(path: Path, report: DifferentialReport) -> None:
    """把 differential evidence 写入本地 JSON 文件。"""

    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(
        json.dumps(report_to_dict(report), ensure_ascii=False, indent=2) + "\n",
        encoding="utf-8",
    )


def main() -> int:
    """命令行入口；返回码跟随四 slice differential 是否全绿。"""

    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()

    report = build_report()
    write_report(args.output, report)
    print(json.dumps(report_to_dict(report), ensure_ascii=False, indent=2))
    return 0 if report.passed else 1


if __name__ == "__main__":
    raise SystemExit(main())
