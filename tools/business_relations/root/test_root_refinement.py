"""ROOT01–ROOT06 unittest suite over the locked synthetic reference.

These tests complement (never replace) the retained suites under
``tools/business_relations/tests/``: they pin the ROOT construction contract —
host I0 custody, independent enumeration, the frozen numeric samples that
``JurisLean/BusinessRoot/Root.lean`` also pins, and the two-artifact tamper
matrix. Run via ``tools/ulm_consolidation/scripts/run_root.py``.
"""
from __future__ import annotations

from dataclasses import replace
from fractions import Fraction as Q
import json
import sys
import tempfile
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'reference'))
sys.path.insert(0, str(ROOT / 'root'))

from business import (  # noqa: E402
    check, derive_analytics, solve,
)
from delivery_bundle import (  # noqa: E402
    check_business_bundle, snapshot_inputs,
)
import root_witness as rw  # noqa: E402


class Root02HostCustodyTests(unittest.TestCase):
    def test_confirm_then_readback(self):
        store = rw.HostInputStore()
        spec, model = rw.frozen_main_case()
        selected = store.confirm(spec, model)
        self.assertEqual(store.selected(selected), selected)

    def test_same_version_parameter_change_rejected(self):
        store = rw.HostInputStore()
        spec, model = rw.frozen_main_case()
        selected = store.confirm(spec, model)
        changed = snapshot_inputs(spec, replace(model, threshold=Q(700)))
        self.assertNotEqual(changed, selected)
        with self.assertRaises(ValueError):
            store.selected(changed)
        bundle = check_business_bundle(
            selected, spec, solve(spec), replace(model, threshold=Q(700)),
            derive_analytics(spec, solve(spec), replace(model, threshold=Q(700))), {})
        self.assertFalse(bundle.accepted)
        self.assertEqual(bundle.reason, 'SELECTED_INPUTS_CHANGED')

    def test_legitimate_new_task_is_a_new_input(self):
        store = rw.HostInputStore()
        spec, model = rw.frozen_main_case()
        first = store.confirm(spec, model)
        second = store.confirm(spec, replace(model, threshold=Q(700)))
        self.assertNotEqual(first, second)
        self.assertEqual(store.selected(second), second)


class Root03EnumerationTests(unittest.TestCase):
    def test_three_enumerations_agree_and_machine_reflects(self):
        report = rw.root03_checks()
        self.assertEqual(report['status'], 'PASS')
        self.assertEqual(report['scenario_count'], 2)


class Root04FrozenSamplesTests(unittest.TestCase):
    """These constants are pinned identically in JurisLean BusinessRoot Root.lean
    (overpay_sample / main_sample); both sides must assert the same values."""

    def test_overpay_sample_matches_lean_pins(self):
        report = rw.root04_checks()
        overpay = report['overpay']
        self.assertEqual(overpay['expected_balance'], '60')
        self.assertEqual(overpay['expected_overpay'], '80')
        self.assertEqual(overpay['expected_raw_residual'], '-20')
        self.assertEqual(overpay['event_c_threshold_0'], '1')
        self.assertEqual(overpay['event_r_threshold_0'], '3/5')

    def test_main_sample_matches_lean_pins(self):
        report = rw.root04_checks()
        main = report['main']
        self.assertEqual(main['expected_balance'], '880')
        self.assertEqual(main['expected_overpay'], '0')
        self.assertEqual(main['event_at_threshold'], '3/5')
        self.assertEqual(main['lower'], '790')
        self.assertEqual(main['upper'], '930')
        self.assertEqual(main['eligible'], ['850'])
        self.assertEqual(main['selected'], '850')
        self.assertTrue(main['interval_point_860_not_in_grid'])

    def test_threshold_zero_distinguishes_c_from_raw_residual(self):
        spec, model = rw.frozen_overpay_case()
        result = solve(spec)
        analytics = derive_analytics(spec, result, model)
        # P(C >= 0) = 1 but P(R >= 0) = 3/5: the clipped event and the raw
        # residual event are different objects.
        self.assertEqual(analytics.event_probability, Q(1))
        raw_event = sum(
            (p for w, p in model.weights
             if next(o.principal_balance - o.overpayment_residual
                     for o in result.outcomes if o.world == w) >= Q(0)), Q(0))
        self.assertEqual(raw_event, Q(3, 5))


class Root05TamperMatrixTests(unittest.TestCase):
    def setUp(self):
        self._tmp = tempfile.TemporaryDirectory(prefix='ulm-root-test-')
        self.addCleanup(self._tmp.cleanup)
        self.report = rw.root05_checks(Path(self._tmp.name))
        self.assertEqual(self.report['status'], 'PASS')

    def test_clean_bundle_accepted_with_digests(self):
        self.assertIn('clean_bundle_accepted_with_content_digests',
                      self.report['checks'])
        self.assertEqual(len(self.report['artifact_sha256']), 2)

    def test_all_tamper_variants_rejected(self):
        for marker in ('json_probability_tamper_rejected',
                       'dropped_condition_tamper_rejected',
                       'same_version_wholesale_swap_rejected',
                       'pending_fake_complete_rejected',
                       'mixed_source_snapshots_rejected'):
            self.assertIn(marker, self.report['checks'])


class Root01JointSemanticsTests(unittest.TestCase):
    def test_every_scenario_carries_conservation_and_complementarity(self):
        spec, model = rw.frozen_main_case()
        result = solve(spec)
        self.assertTrue(check(spec, result))
        seen = set()
        for outcome in result.outcomes:
            c = outcome.principal_balance
            u = outcome.overpayment_residual
            residual = spec.principal - sum(
                (p.amount for p in spec.payments
                 if dict(outcome.world)[p.recognition_atom]), Q(0))
            self.assertGreaterEqual(c, 0)
            self.assertGreaterEqual(u, 0)
            self.assertEqual(c * u, 0)
            self.assertEqual(c - u, residual)
            seen.add(outcome.world)
        all_worlds = {o.world for o in result.outcomes}
        self.assertEqual(seen, all_worlds)

    def test_weights_cover_exactly_the_scenarios(self):
        spec, model = rw.frozen_main_case()
        result = solve(spec)
        worlds = {o.world for o in result.outcomes}
        self.assertEqual(set(dict(model.weights)), worlds)
        self.assertEqual(sum((p for _, p in model.weights), Q(0)), Q(1))


if __name__ == '__main__':
    unittest.main()
