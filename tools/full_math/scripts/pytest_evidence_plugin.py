"""Capture actual pytest item results, never treating xfail/skip as proof coverage.
Loaded only by the full-plan runner. This plugin produces test evidence, not proofs.
"""
import json
from pathlib import Path
import pytest


def pytest_addoption(parser):
    parser.addoption('--math-evidence-output', action='store', default=None)


def pytest_configure(config):
    config._math_results = {}
    config._math_collection_errors = []


@pytest.hookimpl(hookwrapper=True)
def pytest_runtest_makereport(item, call):
    outcome = yield
    report = outcome.get_result()
    data = item.config._math_results
    if report.when == 'setup':
        data.setdefault(report.nodeid, {'id': report.nodeid, 'status': 'NOT_EXECUTED'})
    if report.failed:
        data[report.nodeid] = {'id': report.nodeid, 'status': 'FAIL',
                              'phase': report.when, 'message': str(report.longrepr)}
    elif report.skipped:
        data[report.nodeid] = {'id': report.nodeid,
                              'status': 'XFAIL_NOT_COMPLETE' if hasattr(report, 'wasxfail') else 'SKIP',
                              'phase': report.when, 'message': str(report.longrepr)}
    elif report.when == 'call':
        status = 'XPASS_NOT_COMPLETE' if hasattr(report, 'wasxfail') else 'PASS'
        if data.get(report.nodeid, {}).get('status') in ('NOT_EXECUTED', None):
            data[report.nodeid] = {'id': report.nodeid, 'status': status}


@pytest.hookimpl(hookwrapper=True)
def pytest_make_collect_report(collector):
    outcome = yield
    report = outcome.get_result()
    if report.failed:
        collector.config._math_collection_errors.append(str(report.longrepr))


def pytest_sessionfinish(session, exitstatus):
    dest = session.config.getoption('--math-evidence-output')
    if dest is None:
        return
    rows = [session.config._math_results[k] for k in sorted(session.config._math_results)]
    errors = session.config._math_collection_errors
    data = {'count': session.testscollected, 'tests': rows, 'exitstatus': int(exitstatus),
            'collection_errors': errors,
            'status': 'PASS' if int(exitstatus) == 0 and rows and not errors
                      and len(rows) == session.testscollected
                      and all(r['status'] == 'PASS' for r in rows) else 'FAIL'}
    path = Path(dest)
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(data, ensure_ascii=False, indent=2)+'\n', encoding='utf-8')
