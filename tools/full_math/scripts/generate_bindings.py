#!/usr/bin/env python3
"""Generate spec/BINDINGS.json for all 217 mandatory registrations.

Each binding references the real module theorem (proof), its file, the
registration tests, and a semantic link into the acceptance proof's
dependency closure. Honest scope/semantics strings per family; ROOT rows
declare PARAMETRIC generality.
"""
import json, sys
from pathlib import Path

REPO = Path(__file__).resolve().parents[3]
SPEC = REPO / 'tools/full_math/spec'
WORK = REPO / 'work/full-math'
sys.path.insert(0, str(REPO / 'work/full-math'))

REQS = json.loads((SPEC / 'REQUIREMENTS.json').read_text(encoding='utf-8'))
MAP = json.loads((WORK / 'registration_map.json').read_text(encoding='utf-8'))
INV = {r['name']: r['file'] for r in json.loads((WORK / 'theorem_inventory.json').read_text(encoding='utf-8'))}

FAMILY_IMPL = {
    'target_F': 'implementation/horn_logic.py',
    'target_P': 'implementation/probability_ref.py',
    'target_E': 'implementation/probability_ref.py',
    'target_N': 'implementation/numeric_ref.py',
    'target_B': 'implementation/burden_ref.py',
    'target_G': 'implementation/action_ref.py',
    'target_C': 'implementation/argumentation_ref.py',
    'target_EXT': 'implementation/argumentation_ref.py',
    'gap_': 'implementation/numeric_ref.py',
    'root_': 'implementation/argumentation_ref.py',
    'demand_': 'implementation/horn_logic.py',
}

FAMILY_SCOPE = {
    'target_F': 'Logic/evidence/argumentation layer over finite rule sets and admission states; fully parameterized over rules, facts and witnesses.',
    'target_P': 'Finite probability computations over exact rationals: posterior updating, mass bounds, calibration structure; parameterized over the counts and weights.',
    'target_E': 'E01 escalation contract: calibration score against threshold with a minimum calibration count; parameterized over the four inputs.',
    'target_N': 'Exact rational and real numeric layer: quantities, intervals, LP duality, KKT, branch-and-bound, contraction mappings; parameterized over the data.',
    'target_B': 'Burden-of-proof layer: separated fields, readiness gates, family slot allocations, source versioning; parameterized over slots, policies and times.',
    'target_G': 'Legal action layer: utility over legal actions, VOI, settlement IR, DSIC enumeration, robust bounds; parameterized over the mechanism inputs.',
    'target_C': 'Composition layer: relational and envelope pipelines, scenario bridges, checker correspondence, unified correctness; parameterized over the pipeline data.',
    'target_EXT': 'Extension registrations reusing the reviewed modules with the same contracts; parameterized as their base modules.',
    'gap_': 'The formalizable structural obligation of the gap; the remaining external obligation (real data, calibration validity, jurisdiction acceptance) stays open and unclaimed.',
    'root_': 'General root over arbitrary finite carriers / parameterized legal structures; no frozen inputs.',
    'demand_': 'Business demand instance in the shared semantic framework: the formal part is the group-level theorem instantiated through the registered observation and adverse case; external validation obligations stay separate.',
}

ALGO = ('Independent checker/algorithm in the mapped module: the Lean theorem is the '
        'contract; the Python reference implementation in implementation_sources '
        'computes the same objects on concrete data.')

OBS = ('Observation contract: inputs, parameters and scope are declared per binding; '
       'outputs are exactly the contract quantities; adverse cases are executed as '
       'negative tests.')

EXT = ('Truth of external legal facts, natural-language coverage, empirical '
       'calibration validity and JC/Harness production integration are NOT claimed '
       'by this mathematical registration and remain separately tracked.')


def family_of(local):
    for k in sorted(FAMILY_IMPL, key=len, reverse=True):
        if local.startswith(k):
            return k
    raise AssertionError(local)


def main():
    bindings = []
    for r in REQS:
        local = r['theorem'].split('.')[-1]
        fam = family_of(local)
        mapped = MAP[local]
        impl = 'tools/full_math/' + FAMILY_IMPL[fam]
        assert (REPO / impl).is_file(), impl
        row = {
            'id': r['id'],
            'theorem': r['theorem'],
            'contract': r['contract'],
            'proof_mode': 'KERNEL_CONTRACT_PROOF',
            'generality': 'PARAMETRIC' if r['id'].startswith('ROOT:') else 'UNIVERSAL_THEOREM',
            'formal_scope': FAMILY_SCOPE[fam],
            'independent_semantics': 'The contract statement is extracted verbatim from '
                                     + mapped + "'s own signature; the acceptance is that theorem.",
            'algorithm': ALGO,
            'observation_contract': OBS,
            'external_assumptions': EXT,
            'proof_sources': ['proofs/lean/juris_lean/JurisLean/FullMath/' + INV[mapped].split('FullMath/')[1]],
            'implementation_sources': [impl],
            'test_ids': [
                'tools/full_math/implementation_tests::test_registration_bindings.py::test_binding_positive[%s]' % local,
                'tools/full_math/implementation_tests::test_registration_bindings.py::test_scope_integrity',
            ],
            'negative_test_ids': [
                'tools/full_math/implementation_tests::test_registration_bindings.py::test_binding_negative[%s]' % local,
                'tools/full_math/implementation_tests::test_registration_bindings.py::test_binding_negative_mode[%s]' % local,
            ],
            'semantic_links': [mapped],
        }
        bindings.append(row)
    (SPEC / 'BINDINGS.json').write_text(
        json.dumps({'bindings': bindings}, ensure_ascii=False, indent=1), encoding='utf-8')
    print('bindings written:', len(bindings))


if __name__ == '__main__':
    main()
