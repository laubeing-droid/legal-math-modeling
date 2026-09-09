"""One-run test/report evidence and ACTUAL two-file reference-bundle readback.
No Lean, JC, model API, legal approval or empirical validation is performed.
"""
from pathlib import Path
from dataclasses import asdict
import io,json,sys,unittest,uuid
root=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(root/'reference'))
from business import demo_spec,solve,render,DecisionInputs,derive_analytics,Q
from delivery_bundle import (snapshot_inputs,render_calculation_json,
                             check_business_bundle,read_artifacts)

def require(ok, message):
    if not ok: raise RuntimeError(message)

run_id=str(uuid.uuid4())
evidence=root/'evidence';evidence.mkdir(exist_ok=True)
original=json.loads((root/'data/requirements134_original.json').read_text(encoding='utf-8'))
current=json.loads((root/'data/relations134_obligations.json').read_text(encoding='utf-8'))
expected={f'D{i:03d}' for i in range(1,135)}
require(len(current)==134 and {r['requirement_id'] for r in current}==expected,'REQUIREMENTS_IDS')
require({r['requirement_id']:r['practice_question'] for r in current}==
        {r['requirement_id']:r['practice_question'] for r in original},'REQUIREMENTS_CHANGED')
require(all(len(r['seven_axis_obligations'])==7 and
            r['status']=='OBLIGATIONS_INSTANTIATION_PENDING_NOT_PROVED' for r in current),
        'REQUIREMENTS_STATUS_CHANGED')
suite=unittest.defaultTestLoader.discover(str(root/'tests'))
stream=io.StringIO();stream.write(f'reference_run_id={run_id}\n')
result=unittest.TextTestRunner(stream=stream,verbosity=2).run(suite)
log=stream.getvalue()
(evidence/'python_tests.log').write_text(log,encoding='utf-8')
report={'reference_run_id':run_id,'python_version':sys.version.split()[0],
        'tests':result.testsRun,'failures':len(result.failures),'errors':len(result.errors),
        'skips':len(result.skipped),'requirements':len(current),
        'requirement_mapping':'COUNTS_AND_IDENTITY_ONLY_134_NOT_PROVED',
        'lean':'SOURCE_DRAFT_CI_NOT_RUN','jc':'NOT_INTEGRATED',
        'external_model_approval':'NOT_CLAIMED_SYNTHETIC_INPUT_SELECTION_ONLY',
        'real_forecast_validation':'NOT_RUN','delivery_root':'NOT_RUN',
        'scope':'Finite synthetic principal plus analytics; closed UTF-8 and JSON file snapshots.'}
try:
    require(result.wasSuccessful() and not result.skipped,'REFERENCE_TEST_FAILURE_OR_SKIP')
    s=demo_spec()
    # Model selected and snapshotted BEFORE solver/producer execution.
    m=DecisionInputs(s.context,(((('payment_recognized',False),),Q(3,5)),
                               ((('payment_recognized',True),),Q(2,5))),
                     Q(800),(Q(100),Q(60),Q(10),Q(10)),(Q(600),Q(850),Q(1100)))
    selected=snapshot_inputs(s,m)
    (evidence/'selected_inputs.json').write_text(json.dumps(asdict(selected),ensure_ascii=False,indent=2),encoding='utf-8')
    r=solve(s);a=derive_analytics(s,r,m)
    examples=root/'examples';examples.mkdir(exist_ok=True)
    (examples/'conditional_principal.txt').write_text(render(s,r),encoding='utf-8')
    (examples/'calculation.json').write_text(render_calculation_json(s,r,m,a),encoding='utf-8')
    verdict=check_business_bundle(selected,s,r,m,a,read_artifacts(examples))
    (evidence/'bundle_verdict.json').write_text(json.dumps(asdict(verdict),ensure_ascii=False,indent=2),encoding='utf-8')
    require(verdict.accepted,'ACTUAL_ARTIFACT_READBACK_FAILED')
    report['delivery_root']=verdict.status
except Exception as error:
    report['delivery_root']='REFERENCE_RUN_FAILED'
    report['error']=str(error)
finally:
    (evidence/'reference_result.json').write_text(json.dumps(report,ensure_ascii=False,indent=2),encoding='utf-8')
    (evidence/'reference_run.log').write_text(log+'\n'+json.dumps(report,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
print(json.dumps(report,ensure_ascii=False,indent=2))
if report['delivery_root']!='ACCEPT_REFERENCE_TWO_FILE_REQUIREMENT': sys.exit(1)
