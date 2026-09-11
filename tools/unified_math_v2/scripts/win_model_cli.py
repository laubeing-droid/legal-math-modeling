#!/usr/bin/env python3
"""Fit, calibrate, test and predict from a supplied versioned cohort.

Use private CI for real case rows. --synthetic-example never claims validation.
No LLM/API key or external data service is needed to run the example.
"""
from pathlib import Path
import argparse,sys,json,hashlib
from dataclasses import asdict
from fractions import Fraction
ROOT=Path(__file__).resolve().parents[1];sys.path.insert(0,str(ROOT))
from unified.win_model import Row,train_evaluate,latent_rate_interval

def examples():
    rows=[]
    for split,month in [('train','01'),('calibration','03'),('test','05')]:
        for group,labels in [('low_support',[0,0,0,1]),('high_support',[1,1,1,0])]:
            for i,label in enumerate(labels):
                identity=f'{split}:{group}:{i}'
                rows.append(Row(identity,identity,'claimant:first_instance:money_at_least_50pct:at_judgment',group,split,
                    f'2025-{month}-02',f'2025-{month}-01',f'2025-{month}-20',label,'SYNTHETIC_DEMONSTRATION',True))
    return rows

def main():
    p=argparse.ArgumentParser();g=p.add_mutually_exclusive_group(required=True)
    g.add_argument('--data',type=Path);g.add_argument('--synthetic-example',action='store_true')
    p.add_argument('--group',default='high_support');p.add_argument('--output',type=Path,required=True)
    a=p.parse_args()
    try:
        if a.synthetic_example:rows=examples();data=[asdict(r) for r in rows]
        else:
            data=json.loads(a.data.read_text(encoding='utf-8'))
            if type(data) is not list:raise ValueError('Dataset must be a list of rows')
            rows=[Row(**r) for r in data]
        model,cal,report=train_evaluate(rows)
        raw=model.predict(a.group)
        output={'objective':model.objective,'group':a.group,'raw_predictive_probability':str(raw),
          'calibrated_predictive_probability':str(cal.predict(raw)),
          'raw_latent_rate_credible_enclosure':latent_rate_interval(model,a.group),
          'evaluation':report,'normative_effect':'none','fact_admission_changes':0,
          'dataset_sha256':hashlib.sha256(json.dumps(data,sort_keys=True).encode()).hexdigest(),
          'model':asdict(model),'calibrator':asdict(cal),'version':'ulm-v2-win-reference-1'}
        a.output.parent.mkdir(parents=True,exist_ok=True)
        a.output.write_text(json.dumps(output,ensure_ascii=False,indent=2,default=str)+'\n',encoding='utf-8')
        print('Prediction artifact written; '+report['empirical_status']);return 0
    except (ValueError,TypeError,KeyError) as exc:
        print(f'Invalid dataset/model: {exc}',file=sys.stderr);return 2
if __name__=='__main__':raise SystemExit(main())
