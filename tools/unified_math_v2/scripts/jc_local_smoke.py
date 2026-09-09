#!/usr/bin/env python3
"""Exercise the real frozen JC public local surface, not a fake V2.1 adapter.
GitHub CI Python 3.12 only in the supplied workflow. Source sample is TEST law.
"""
import argparse,json,runpy,sys,tempfile,subprocess
from pathlib import Path

def run(root,expected):
    actual=subprocess.check_output(['git','-C',str(root),'rev-parse','HEAD'],text=True).strip()
    if actual!=expected:raise ValueError('JC checkout identity mismatch')
    sys.path.insert(0,str(root))
    sample=runpy.run_path(str(root/'examples/harness/sample_local.py'),run_name='ulm_jc_sample_material')
    from compiler_core.client import create_local_client
    with tempfile.TemporaryDirectory(prefix='ulm-jc-smoke-') as t:
        base=Path(t);rules=base/'rules';rules.mkdir()
        (rules/'jc-local-pack.json').write_text(json.dumps(sample['RULE_PACK'],ensure_ascii=False),encoding='utf-8')
        client=create_local_client(base/'state',rules)
        claims={r['rule_id']:r['claim'] for r in client.local_pack()['rules']}
        qs=[{'issue_id':q['issue_id'],'claim':claims[q['claim']],'profile':q['profile']} for q in sample['QUERIES']]
        bundle=client.local_case_bundle(case_id='ulm-keyless-smoke',decision_time='2026-09-01T00:00:00Z',
            facts=[{'fact_key':'sample.contract-signed'},{'fact_key':'sample.statute-exception'}],queries=qs)
        result=client.evaluate_harness_bundle(bundle,case_id='ulm-keyless-smoke',issue_queries=qs)
        expected_fields={'harness_contract_version':'jc-harness-local/1','execution_mode':'local',
                         'signature_status':'not_used','evaluation_count':1,'run_status':'success',
                         'decision_status':'accepted_formal_result'}
        if any(result.get(k)!=v for k,v in expected_fields.items()):raise ValueError('Public response mismatch')
        record=client.local_read_run(result['run_identity_ref'])
        if record['signature_status']!='not_used':raise ValueError('Local record is not keyless')
        return {'status':'PASS','jc_commit':actual,'scope':'EXISTING_PUBLIC_TRANSPORT_SMOKE_ONLY',
            'v21_runtime_refinement':'NOT_ESTABLISHED','law_rules':'ENGINEERING_TEST_ONLY',
            'observed_fields':{k:result[k] for k in expected_fields},'new_key_material':False}
def main():
    p=argparse.ArgumentParser();p.add_argument('--jc-root',type=Path,required=True)
    p.add_argument('--expected-jc-sha',required=True);p.add_argument('--output',type=Path,required=True);a=p.parse_args()
    a.output.parent.mkdir(parents=True,exist_ok=True)
    try:r=run(a.jc_root.resolve(),a.expected_jc_sha)
    except Exception as ex:r={'status':'FAIL','error':str(ex),'scope':'EXISTING_PUBLIC_TRANSPORT_SMOKE_ONLY'}
    a.output.write_text(json.dumps(r,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
    if r['status']!='PASS':raise SystemExit(1)
if __name__=='__main__':main()
