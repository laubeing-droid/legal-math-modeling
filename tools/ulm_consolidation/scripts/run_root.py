#!/usr/bin/env python3
"""Run the ROOT refinement Python cross-checks in isolated processes.

Executes the root witness generator and the root unittest suite against the
locked reference implementation and writes one evidence report.
Lean/Lake/Elan are never run here; the kernel-checked Lean side compiles only
on GitHub CI (``proofs/lean/juris_lean/JurisLean/BusinessRoot/``). This script
does not prove the root — it produces the Python-side cross-check evidence.
"""
from pathlib import Path
import argparse
import datetime
import json
import os
import platform
import subprocess
import sys
import uuid

REPO = Path(__file__).resolve().parents[3]
BR_ROOT = REPO / 'tools' / 'business_relations'


def run(cmd, log_path, cwd):
    log_path.parent.mkdir(parents=True, exist_ok=True)
    with log_path.open('w', encoding='utf-8') as stream:
        proc = subprocess.run(
            cmd, cwd=cwd, stdout=stream, stderr=subprocess.STDOUT,
            env={**os.environ, 'PYTHONDONTWRITEBYTECODE': '1', 'PYTHONUTF8': '1'})
    if proc.returncode:
        raise RuntimeError('Command failed, see ' + str(log_path))


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    out = args.output.resolve()
    out.mkdir(parents=True, exist_ok=True)

    report = {
        'status': 'FAIL',
        'scope': 'ROOT_REFINEMENT_PYTHON_CROSS_CHECK_ONLY',
        'run_id': uuid.uuid4().hex,
        'python': platform.python_version(),
        'time_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
        'requirement': 'SYNTHETIC_EXACT_PRINCIPAL_ANALYTICS_TWO_FILES/1',
        'guarantee_level': 'CROSS_CHECK_MIRRORED_SEMANTICS_NOT_KERNEL_REFINED_PYTHON',
        'lean_kernel_evidence': 'SEE_GITHUB_CI_BUSINESS_ROOT_JOB_NOT_THIS_REPORT',
        'legal_approval': 'NOT_PERFORMED',
        'empirical': 'NO_REAL_DATA_USED',
    }
    try:
        run([sys.executable, '-B', str(BR_ROOT / 'root' / 'root_witness.py'),
             '--output', str(out / 'root-witness.json')],
            out / 'root-witness.log', REPO)
        report['witness'] = json.loads(
            (out / 'root-witness.json').read_text(encoding='utf-8'))
        run([sys.executable, '-B', '-m', 'unittest', 'discover',
             '-s', str(BR_ROOT / 'root'), '-p', 'test_*.py', '-v'],
            out / 'root-tests.log', REPO)
        log_text = (out / 'root-tests.log').read_text(encoding='utf-8')
        if not log_text.rstrip().endswith('OK'):
            raise RuntimeError('Root unittest suite did not end OK')
        report['root_tests'] = 'OK (see root-tests.log)'
        report['status'] = 'PASS'
    except Exception as exc:  # noqa: BLE001
        report['status'] = 'FAIL'
        report['error'] = str(exc)
    (out / 'root-python.json').write_text(
        json.dumps(report, ensure_ascii=False, indent=2) + '\n', encoding='utf-8')
    print(json.dumps({'status': report['status']}))
    return 0 if report['status'] == 'PASS' else 1


if __name__ == '__main__':
    raise SystemExit(main())
