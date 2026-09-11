"""ROOT01–ROOT06 construction witness over the locked synthetic reference.

Runs the retained reference implementation and produces one evidence JSON with:

* ROOT02 — host-side I0 custody (the host stores the snapshot at selection;
  producers can read it back, never choose or replace it) and the same-version
  parameter-change rejection;
* ROOT03 — three independent scenario enumerations (solver stack machine,
  checker bitmask, brute-force product) agreeing, and the guard machine equal
  to the structural denotation on every scenario;
* ROOT04 — the frozen overpay sample (E[C]=60, E[U]=80, E[R]=-20, and the
  threshold-0 event distinction P(C>=0)=1 vs P(R>=0)=3/5) and the main sample
  (E[C]=880, event 3/5, interval [790,930], eligible grid {850});
* ROOT05 — actual two-artifact write/read and the tamper matrix (JSON wrong
  while text right, text wrong while JSON right, same-version model swap,
  pending fake-completeness, mixed source snapshots);
* ROOT01/ROOT06 — the cross-check constants pinned by
  ``JurisLean/BusinessRoot/Root.lean`` so both sides assert the same values.

Guarantee level: CROSS_CHECK_MIRRORED_SEMANTICS. The Lean module is
kernel-checked about its own mirrored definitions; the byte-level lexing and
the Python↔Lean correspondence are engineering cross-checks, NOT kernel
refinement. No legal, empirical or production claim is made.
"""
from __future__ import annotations

from dataclasses import replace
from fractions import Fraction as Q
from hashlib import sha256
from itertools import product
import json
import sys
import tempfile
from pathlib import Path
from typing import Any, Callable

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'reference'))

from business import (  # noqa: E402
    DecisionInputs, Outcome, PrincipalSpec, Result,
    check, check_analytics, compile_formula, denote, derive_analytics,
    demo_spec, render, solve,
    solver_worlds, checker_worlds,
)
from business import execute as run_stack_program  # noqa: E402
from delivery_bundle import (  # noqa: E402
    FILES, InputSnapshot, check_business_bundle, read_artifacts,
    render_calculation_json, snapshot_inputs,
)


def require(ok: bool, message: str) -> None:
    if not ok:
        raise RuntimeError(message)


# --------------------------------------------------------------------------
# ROOT02 — host-side I0 custody.
# --------------------------------------------------------------------------

class HostInputStore:
    """Task-confirmed I0 storage outside the submitted certificate.

    The host saves the snapshot when the request is selected. Producers may
    read the stored snapshot back but can never choose, replace or re-label
    the expected input; binding is by full content, not by an ID.
    """

    def __init__(self) -> None:
        self._stored: dict[str, InputSnapshot] = {}

    @staticmethod
    def locator(snapshot: InputSnapshot) -> str:
        return sha256(snapshot.exact_inputs.encode('utf-8')).hexdigest()

    def confirm(self, spec: PrincipalSpec, model: DecisionInputs) -> InputSnapshot:
        snapshot = snapshot_inputs(spec, model)
        self._stored[self.locator(snapshot)] = snapshot
        return snapshot

    def selected(self, snapshot: InputSnapshot) -> InputSnapshot:
        stored = self._stored.get(self.locator(snapshot))
        if stored is None or stored != snapshot:
            raise ValueError('SELECTED_INPUT_NOT_FROM_HOST')
        return stored


def frozen_main_case() -> tuple[PrincipalSpec, DecisionInputs]:
    """The frozen main I0: P=1000, q=300, p=2/5, threshold 800."""
    spec = demo_spec()
    world_true = (('payment_recognized', True),)
    world_false = (('payment_recognized', False),)
    model = DecisionInputs(
        spec.context,
        ((world_true, Q(2, 5)), (world_false, Q(3, 5))),
        Q(800), (Q(100), Q(60), Q(10), Q(10)),
        (Q(600), Q(850), Q(1100)))
    return spec, model


def frozen_overpay_case() -> tuple[PrincipalSpec, DecisionInputs]:
    """The frozen overpay I0: P=100, q=300, p=2/5, threshold 0."""
    spec = demo_spec(principal=Q(100))
    world_true = (('payment_recognized', True),)
    world_false = (('payment_recognized', False),)
    model = DecisionInputs(
        spec.context,
        ((world_true, Q(2, 5)), (world_false, Q(3, 5))),
        Q(0), (Q(0), Q(0), Q(0), Q(0)),
        (Q(0),))
    return spec, model


def root02_checks() -> dict[str, Any]:
    store = HostInputStore()
    spec, model = frozen_main_case()
    selected = store.confirm(spec, model)
    require(store.selected(selected) == selected,
            'ROOT02_STORED_SNAPSHOT_MISMATCH')

    # Same version, changed parameter: different content, refused as this I0.
    changed_model = replace(model, threshold=Q(700))
    changed_snapshot = snapshot_inputs(spec, changed_model)
    require(changed_snapshot != selected, 'ROOT02_PARAMETER_CHANGE_UNDETECTED')
    try:
        store.selected(changed_snapshot)
        raise RuntimeError('ROOT02_ACCEPTED_UNSTORED_INPUT')
    except ValueError:
        pass
    result_changed = solve(spec)
    analytics_changed = derive_analytics(spec, result_changed, changed_model)
    bundle = check_business_bundle(
        selected, spec, result_changed, changed_model, analytics_changed, {})
    require(not bundle.accepted and bundle.reason == 'SELECTED_INPUTS_CHANGED',
            'ROOT02_CHANGED_PARAMETER_NOT_REFUSED: ' + bundle.reason)

    # A legitimate new input is a NEW task, not a rejection of existence.
    new_selected = store.confirm(spec, changed_model)
    require(new_selected != selected, 'ROOT02_NEW_TASK_NOT_DISTINCT')
    require(store.selected(new_selected) == new_selected,
            'ROOT02_NEW_TASK_NOT_STORED')

    return {
        'status': 'PASS',
        'checks': [
            'host_confirm_then_readback_identical',
            'same_version_parameter_change_rejected',
            'changed_content_not_in_host_store',
            'legitimate_new_task_stored_as_new_input',
        ],
    }


# --------------------------------------------------------------------------
# ROOT03 — independent enumeration coverage and guard machine reflection.
# --------------------------------------------------------------------------

def root03_checks() -> dict[str, Any]:
    spec, _ = frozen_main_case()

    solver = sorted(solver_worlds(spec))
    checker = sorted(checker_worlds(spec))
    # Third, deliberately naive enumeration over the full boolean product.
    keys = [k for k, _ in spec.facts]
    fixed = {k: v for k, v in spec.facts if v is not None}
    brute = sorted(
        tuple(zip(keys, values))
        for values in product((False, True), repeat=len(keys))
        if denote(spec.constraint, tuple(zip(keys, values)))
        and all(dict(dict(zip(keys, values))).get(k) is v
                for k, v in fixed.items()))
    require(solver == checker == brute, 'ROOT03_ENUMERATIONS_DISAGREE')

    program = compile_formula(spec.constraint)
    for world in checker:
        machine_value = run_stack_program(program, world)
        require(machine_value == denote(spec.constraint, world),
                'ROOT03_MACHINE_DENOTATION_MISMATCH')
        require(len(world) == len(spec.facts), 'ROOT03_WORLD_SHAPE')
    return {
        'status': 'PASS',
        'scenario_count': len(checker),
        'checks': [
            'solver_stack_machine_enumeration',
            'checker_bitmask_enumeration',
            'brute_force_product_enumeration',
            'all_three_agree',
            'compiled_stack_program_equals_denotation_on_every_scenario',
        ],
    }


# --------------------------------------------------------------------------
# ROOT04 — frozen numeric samples (must mirror Root.lean exactly).
# --------------------------------------------------------------------------

CROSS_CHECK_CONSTANTS: dict[str, Any] = {
    'overpay': {
        'principal': '100', 'payment': '300', 'p_true': '2/5',
        'expected_balance': '60', 'expected_overpay': '80',
        'expected_raw_residual': '-20',
        'event_c_threshold_0': '1', 'event_r_threshold_0': '3/5',
    },
    'main': {
        'principal': '1000', 'payment': '300', 'p_true': '2/5',
        'threshold': '800',
        'expected_balance': '880', 'expected_overpay': '0',
        'event_at_threshold': '3/5',
        'lower': '790', 'upper': '930',
        'eligible': ['850'], 'selected': '850',
        'interval_point_860_not_in_grid': True,
    },
}


def _weighted_overpay(result: Result, model: DecisionInputs,
                      pick: Callable[[Outcome], Q]) -> Q:
    table = {o.world: pick(o) for o in result.outcomes}
    return sum((p * table[w] for w, p in model.weights), Q(0))


def _p_true(model: DecisionInputs) -> Q:
    """Recognition-branch probability of the frozen single-atom task."""
    return next(p for w, p in model.weights
                if dict(w)['payment_recognized'] is True)


def root04_checks() -> dict[str, Any]:
    spec, model = frozen_overpay_case()
    result = solve(spec)
    analytics = derive_analytics(spec, result, model)
    overpay = {
        'principal': str(spec.principal),
        'payment': str(spec.payments[0].amount),
        'p_true': str(_p_true(model)),
        'expected_balance': str(analytics.expected),
        'expected_overpay': str(_weighted_overpay(
            result, model, lambda o: o.overpayment_residual)),
        'expected_raw_residual': str(_weighted_overpay(
            result, model, lambda o: o.principal_balance - o.overpayment_residual)),
        'event_c_threshold_0': str(sum(
            (p for w, p in model.weights
             if next(o.principal_balance for o in result.outcomes if o.world == w) >= Q(0)),
            Q(0))),
        'event_r_threshold_0': str(sum(
            (p for w, p in model.weights
             if next(o.principal_balance - o.overpayment_residual
                     for o in result.outcomes if o.world == w) >= Q(0)),
            Q(0))),
    }

    spec_m, model_m = frozen_main_case()
    result_m = solve(spec_m)
    require(check(spec_m, result_m), 'ROOT04_MAIN_RESULT_CHECK')
    analytics_m = derive_analytics(spec_m, result_m, model_m)
    require(check_analytics(spec_m, result_m, model_m, analytics_m),
            'ROOT04_MAIN_ANALYTICS_CHECK')
    main = {
        'principal': str(spec_m.principal),
        'payment': str(spec_m.payments[0].amount),
        'p_true': str(_p_true(model_m)),
        'threshold': str(model_m.threshold),
        'expected_balance': str(analytics_m.expected),
        'expected_overpay': str(_weighted_overpay(
            result_m, model_m, lambda o: o.overpayment_residual)),
        'event_at_threshold': str(analytics_m.event_probability),
        'lower': str(analytics_m.lower),
        'upper': str(analytics_m.upper),
        'eligible': [str(x) for x in analytics_m.mutually_acceptable],
        'selected': None if analytics_m.selected is None else str(analytics_m.selected),
        'interval_point_860_not_in_grid': bool(
            analytics_m.lower <= Q(860) <= analytics_m.upper
            and Q(860) not in set(model_m.legal_options)),
    }

    for key, value in CROSS_CHECK_CONSTANTS['overpay'].items():
        require(str(overpay[key]) == str(value),
                'ROOT04_OVERPAY_CROSS_CHECK_MISMATCH_' + key)
    for key, value in CROSS_CHECK_CONSTANTS['main'].items():
        require(str(main[key]) == str(value),
                'ROOT04_MAIN_CROSS_CHECK_MISMATCH_' + key)
    return {'status': 'PASS', 'overpay': overpay, 'main': main}


# --------------------------------------------------------------------------
# ROOT05 — real two-file delivery and the tamper matrix.
# --------------------------------------------------------------------------

def _artifacts(spec: PrincipalSpec, result: Result, model: DecisionInputs,
               analytics) -> dict[str, bytes]:
    return {FILES[0]: render(spec, result).encode('utf-8'),
            FILES[1]: render_calculation_json(spec, result, model, analytics).encode('utf-8')}


def _edit_json(payload: bytes, mutate: Callable[[dict], None]) -> bytes:
    obj = json.loads(payload.decode('utf-8'))
    mutate(obj)
    return json.dumps(obj, ensure_ascii=False).encode('utf-8')


def root05_checks(workdir: Path) -> dict[str, Any]:
    store = HostInputStore()
    spec, model = frozen_main_case()
    selected = store.confirm(spec, model)
    result = solve(spec)
    analytics = derive_analytics(spec, result, model)
    good = _artifacts(spec, result, model, analytics)

    out = workdir / 'artifacts'
    out.mkdir(parents=True, exist_ok=True)
    for name, payload in good.items():
        (out / name).write_bytes(payload)
    reread = read_artifacts(out)
    require(reread == good, 'ROOT05_FILE_REREAD_MISMATCH')

    verdict = check_business_bundle(selected, spec, result, model, analytics, reread)
    require(verdict.accepted, 'ROOT05_CLEAN_BUNDLE_REJECTED: ' + verdict.reason)
    digests = {name: sha256(payload).hexdigest()
               for name, payload in sorted(reread.items())}
    require(dict(verdict.checked_artifacts) == digests, 'ROOT05_DIGEST_MISMATCH')

    # 1. JSON probability wrong while text correct.
    def set_bad_probability(obj: dict) -> None:
        obj['decision_inputs']['weights'][0]['probability'] = '1/2'
    v = check_business_bundle(
        selected, spec, result, model, analytics,
        {**good, FILES[1]: _edit_json(good[FILES[1]], set_bad_probability)})
    require(not v.accepted, 'ROOT05_JSON_TAMPER_ACCEPTED')

    # 2. JSON carries a dropped/renamed condition while the text is correct.
    def add_fake_atom(obj: dict) -> None:
        row = obj['result']['outcomes'][0]['world']
        row.append(['payment_skipped', row[0][1]])
    v = check_business_bundle(
        selected, spec, result, model, analytics,
        {**good, FILES[1]: _edit_json(good[FILES[1]], add_fake_atom)})
    require(not v.accepted, 'ROOT05_WORLD_TAMPER_ACCEPTED')

    # 3. Same-version model swapped wholesale: fully consistent artifacts of
    #    the swapped model are still not this selected input's delivery.
    model_swapped = replace(model, threshold=Q(700))
    result_swapped = solve(spec)
    analytics_swapped = derive_analytics(spec, result_swapped, model_swapped)
    v = check_business_bundle(selected, spec, result_swapped, model_swapped,
                              analytics_swapped,
                              _artifacts(spec, result_swapped, model_swapped,
                                         analytics_swapped))
    require(not v.accepted and v.reason == 'SELECTED_INPUTS_CHANGED',
            'ROOT05_WHOLESALE_SWAP_NOT_REJECTED: ' + v.reason)

    # 4. Pending fake-completeness: one scenario demoted, EXACT claim withdrawn.
    demoted = Outcome(spec.context, spec.relation_id, spec.creditor, spec.debtor,
                      spec.debt_id, tuple(s.source_id for s in spec.sources),
                      spec.asof_day, result.outcomes[0].world, Q(0), Q(0))
    partial = Result(spec.context, 'PARTIAL_SCENARIOS', (demoted,),
                     (result.outcomes[1].world,))
    v = check_business_bundle(selected, spec, partial, model, analytics, good)
    require(not v.accepted, 'ROOT05_PENDING_FAKE_COMPLETE_ACCEPTED')

    # 5. Mixed source snapshots: text from a P=1200 input, JSON from frozen.
    spec_alt = demo_spec(principal=Q(1200))
    result_alt = solve(spec_alt)
    analytics_alt = derive_analytics(spec_alt, result_alt, model)
    mixed = {FILES[0]: render(spec_alt, result_alt).encode('utf-8'),
             FILES[1]: good[FILES[1]]}
    v = check_business_bundle(snapshot_inputs(spec_alt, model), spec_alt,
                              result_alt, model, analytics_alt, mixed)
    require(not v.accepted, 'ROOT05_MIXED_SNAPSHOTS_ACCEPTED')

    return {
        'status': 'PASS',
        'artifact_sha256': digests,
        'checks': [
            'write_then_reread_identical',
            'clean_bundle_accepted_with_content_digests',
            'json_probability_tamper_rejected',
            'dropped_condition_tamper_rejected',
            'same_version_wholesale_swap_rejected',
            'pending_fake_complete_rejected',
            'mixed_source_snapshots_rejected',
        ],
    }


def main() -> int:
    import argparse
    parser = argparse.ArgumentParser()
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()

    report: dict[str, Any] = {
        'requirement': 'SYNTHETIC_EXACT_PRINCIPAL_ANALYTICS_TWO_FILES/1',
        'guarantee_level': 'CROSS_CHECK_MIRRORED_SEMANTICS_NOT_KERNEL_REFINED_PYTHON',
        'lean_side': 'proofs/lean/juris_lean/JurisLean/BusinessRoot/ (kernel-checked, CI only)',
        'legal_approval': 'NOT_PERFORMED',
        'empirical': 'NO_REAL_DATA_USED',
        'root06_kernel_evidence': 'PENDING_LEAN_CI',
    }
    try:
        report['root02'] = root02_checks()
        report['root03'] = root03_checks()
        report['root04'] = root04_checks()
        with tempfile.TemporaryDirectory(prefix='ulm-root-') as tmp:
            report['root05'] = root05_checks(Path(tmp))
        report['cross_check_constants'] = CROSS_CHECK_CONSTANTS
        report['status'] = 'PASS'
    except Exception as exc:  # noqa: BLE001
        report['status'] = 'FAIL'
        report['error'] = type(exc).__name__ + ': ' + str(exc)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, ensure_ascii=False, indent=2) + '\n',
                           encoding='utf-8')
    print(json.dumps({'status': report['status'], 'output': str(args.output)}))
    return 0 if report['status'] == 'PASS' else 1


if __name__ == '__main__':
    raise SystemExit(main())
