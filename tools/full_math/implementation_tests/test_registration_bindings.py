"""Per-registration binding tests: each of the 217 mandatory registrations
is checked positively (spec row, mapped module theorem, generated contract
and acceptance lines all consistent) and adversely (a tampered registration
is rejected by the evidence validator)."""
import json
import re
import sys
from pathlib import Path

import pytest

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[2]
SPEC = REPO / 'tools/full_math/spec'
WORK = REPO / 'work/full-math'
sys.path.insert(0, str(SPEC.parents[1] / 'full_math'))
import completion as C  # noqa: E402

REQS = json.loads((SPEC / 'REQUIREMENTS.json').read_text(encoding='utf-8'))
MAP = json.loads((WORK / 'registration_map.json').read_text(encoding='utf-8'))
INV = {r['name'] for r in json.loads((WORK / 'theorem_inventory.json').read_text(encoding='utf-8'))}
CONTRACTS_TXT = (REPO / 'proofs/lean/juris_lean/JurisLean/FullMath/Contracts.lean').read_text(encoding='utf-8')
ACCEPT_TXT = (REPO / 'proofs/lean/juris_lean/JurisLean/FullMath/Acceptance.lean').read_text(encoding='utf-8')
BY_LOCAL = {r['theorem'].split('.')[-1]: r for r in REQS}
NAMES = sorted(BY_LOCAL)


def _module_file(thm):
    return json.loads((WORK / 'theorem_inventory.json').read_text(encoding='utf-8'))


@pytest.mark.parametrize('name', NAMES)
def test_binding_positive(name):
    row = BY_LOCAL[name]
    assert row['theorem'] == 'JurisLean.FullMath.Acceptance.' + name
    assert row['contract'] == 'JurisLean.FullMath.Contracts.' + name
    mapped = MAP[name]
    assert mapped in INV, mapped
    assert re.search(r'^def %s : Prop :=' % re.escape(name), CONTRACTS_TXT, re.M)
    assert re.search(r'^theorem %s : Contracts\.%s :=' % (re.escape(name), re.escape(name)), ACCEPT_TXT, re.M)
    line = re.search(r'^theorem %s : Contracts\.%s :=.*$' % (re.escape(name), re.escape(name)),
                     ACCEPT_TXT, re.M).group(0)
    assert mapped in line


def _required(name):
    return BY_LOCAL[name]


@pytest.mark.parametrize('name', NAMES)
def test_binding_negative(name):
    row = dict(_required(name))
    row['theorem'] = 'JurisLean.FullMath.Acceptance.nonexistent_name'
    with pytest.raises(C.EvidenceError):
        C.validate_binding(row, _required(name))


@pytest.mark.parametrize('name', NAMES)
def test_binding_negative_mode(name):
    row = dict(_required(name))
    row['proof_mode'] = 'FIXED_EXAMPLE_NOT_PROOF'
    with pytest.raises(C.EvidenceError):
        C.validate_binding(row, _required(name))


def test_scope_integrity():
    scope, reqs = C.requirements(SPEC)
    assert len(reqs) == 217
    assert scope['terminal_state'] == 'MATH_BUILD_COMPLETE'


def test_c07_closure_witness():
    txt = ACCEPT_TXT
    for root in ['root_GENERIC_FINITE', 'root_SYMBOLIC_EXACT', 'root_STATISTICAL_COMPOSITION',
                 'root_CIVIL', 'root_CRIMINAL', 'root_ADMINISTRATIVE', 'root_DOCUMENT_DELIVERY']:
        line = re.search(r'^theorem target_C07 :.*$', txt, re.M).group(0)
        assert root in line


def test_ext09_three_domains():
    mapped = MAP['target_EXT09']
    assert mapped.endswith('ext09_domainComposition')
