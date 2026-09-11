#!/usr/bin/env python3
"""Verify the compiled environment report of the JurisLean BusinessRoot module.

Only a real GitHub CI ``lake build`` + ``lake env lean RootAudit.lean`` can
create this log. The audit checks: exactly one environment report, every record
named under ``JurisLean.BusinessRoot.``, only the three permitted mathlib
axioms, and presence of the pinned root-theorem declarations. It never proves
the Python implementation, legal applicability, or any empirical property.
"""
import argparse
import json
from pathlib import Path

PREFIX = 'ROOT_COMPILED_ENV_JSON='
NAME_PREFIX = 'JurisLean.BusinessRoot.'
ALLOWED_AXIOMS = {'propext', 'Classical.choice', 'Quot.sound'}

REQUIRED_DECLARATIONS = [
    'JurisLean.BusinessRoot.business_root_two_files',
    'JurisLean.BusinessRoot.readBoth_returns_expected',
    'JurisLean.BusinessRoot.root_bundle_accepts_real',
    'JurisLean.BusinessRoot.root_worlds_match',
    'JurisLean.BusinessRoot.root_joint_sem',
    'JurisLean.BusinessRoot.root_task_sat',
    'JurisLean.BusinessRoot.root_wf',
    'JurisLean.BusinessRoot.root_binding_accepts_selected',
    'JurisLean.BusinessRoot.root_binding_refuses_change',
    'JurisLean.BusinessRoot.tampered_text_rejected',
    'JurisLean.BusinessRoot.tampered_json_rejected',
    'JurisLean.BusinessRoot.mixed_snapshots_rejected',
    'JurisLean.BusinessRoot.wholesale_swap_rejected',
    'JurisLean.BusinessRoot.overpay_sample',
    'JurisLean.BusinessRoot.main_sample',
    'JurisLean.BusinessRoot.CU_expectation_conservation',
    'JurisLean.BusinessRoot.decomposition_unique',
    'JurisLean.BusinessRoot.domain_pair_exact',
    'JurisLean.BusinessRoot.machine_reflection',
    'JurisLean.BusinessRoot.codec_roundtrip',
    'JurisLean.BusinessRoot.doc_roundtrip',
    'JurisLean.BusinessRoot.json_roundtrip',
    'JurisLean.BusinessRoot.duplicate_key_rejected',
    'JurisLean.BusinessRoot.threshold_zero_distinction',
]


def verify_log(text: str) -> dict:
    lines = [line[len(PREFIX):] for line in text.splitlines()
             if line.startswith(PREFIX)]
    if len(lines) != 1:
        raise ValueError('Exactly one compiled root environment required')
    rows = json.loads(lines[0])
    if type(rows) is not list or not rows:
        raise ValueError('Empty root inventory')
    names = set()
    for row in rows:
        if type(row) is not dict:
            raise ValueError('Bad root record')
        name = row.get('name')
        axioms = row.get('axioms')
        deps = row.get('proof_dependencies')
        if type(name) is not str or not name.startswith(NAME_PREFIX) or name in names:
            raise ValueError('Foreign/duplicate root declaration ' + repr(name))
        if type(axioms) is not list or any(type(x) is not str for x in axioms):
            raise ValueError('Bad root axiom data')
        forbidden = set(axioms) - ALLOWED_AXIOMS
        if forbidden:
            raise ValueError('Forbidden axiom ' + repr(forbidden))
        if type(deps) is not list or any(type(x) is not str for x in deps):
            raise ValueError('Missing root proof dependency list')
        names.add(name)
    missing = [n for n in REQUIRED_DECLARATIONS if n not in names]
    if missing:
        raise ValueError('Uncompiled root declarations ' + repr(missing))
    return {
        'status': 'PASS',
        'scope': 'COMPILED_FINITE_SYNTHETIC_BUSINESS_ROOT_ONLY',
        'theorem_count': len(names),
        'required_count': len(REQUIRED_DECLARATIONS),
        'records': rows,
        'python_refinement': 'NOT_ESTABLISHED_BY_THIS_INVENTORY',
        'production_integration': 'NOT_ESTABLISHED',
        'legal_approval': 'NOT_ESTABLISHED',
        'empirical': 'NOT_ESTABLISHED',
        'D001_D134': 'NOT_ESTABLISHED',
    }


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--log', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    try:
        result = verify_log(args.log.read_text(encoding='utf-8'))
    except (ValueError, TypeError, KeyError, OSError) as exc:
        result = {'status': 'FAIL', 'error': str(exc)}
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, ensure_ascii=False, indent=2) + '\n',
                           encoding='utf-8')
    print(json.dumps({'status': result['status']}))
    return 0 if result['status'] == 'PASS' else 1


if __name__ == '__main__':
    raise SystemExit(main())
