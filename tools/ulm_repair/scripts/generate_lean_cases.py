#!/usr/bin/env python3
"""Generate typed fixtures from actual output bytes. Does NOT execute Lean.

The translation is cross-check evidence, not a verified Python compiler. CI
regenerates the committed fixtures and demands no drift before building them.
"""
from pathlib import Path
import argparse,copy,json,sys,tempfile
from fractions import Fraction
sys.path.insert(0,str(Path(__file__).resolve().parents[1]))
import projection_reference as P


def string(x):return json.dumps(x,ensure_ascii=False)
def rat(x):
    q=Fraction(x)
    if q.denominator==1:return f'({q.numerator} : ℚ)'
    return '{ num := '+str(q.numerator)+', den := '+str(q.denominator)+' }'
def arr(x,emit):return '['+', '.join(emit(v) for v in x)+']'
def world(x):return arr(x,lambda p:'('+string(p[0])+', '+str(p[1]).lower()+')')
def rows(x):return arr(x,lambda r:'('+world(r[0])+', '+rat(r[1])+', '+rat(r[2])+')')
def weights(x):return arr(x,lambda p:'('+world(p[0])+', '+rat(p[1])+')')
def struct(d,emitters):return '{ '+', '.join(k+' := '+e(v) for k,v,e in emitters(d))+' }'

def ctx(x):
    return '{ '+', '.join(k+' := '+(arr(v,string) if k=='assumptions' else str(v) if k=='max_depth' else string(v)) for k,v in sorted(x.items()))+' }'

def dmeta(m):
    mapping=[('caseId','case',string),('issue','issue',string),('creditor','creditor',string),
      ('debtor','debtor',string),('debtId','debt',string),('sourceIds','source_ids',lambda x:arr(x,string)),
      ('dueDay','due',string),('asOfDay','asof',string),('assumptions','assumptions',lambda x:arr(x,string)),('context','context',ctx)]
    return '{ '+', '.join(a+' := '+f(m[b]) for a,b,f in mapping)+' }'

def src(v):return '⟨'+', '.join([string(v['source_id']),string(v['version']),str(v['start']),str(v['end']),string(v['quoted'])])+'⟩'
def rel(v):return '⟨'+', '.join([string(v['relation_id']),string(v['creditor']),string(v['debtor']),string(v['debt_id']),rat(v['principal']),string(v['due_day']),string(v['asof_day'])])+'⟩'

def jmeta(m):
    d=m['decision_inputs']; w=[(x['world'],x['probability']) for x in d['weights']]
    w.sort(key=lambda x:tuple(map(tuple,x[0])),reverse=True)
    parts={'schema':string(m['schema']),'requirement':string(m['requirement']),
      'scope':string(m['scope']),'warning':string(m['warning']),'principalDocument':string(m['principal_document']),
      'context':ctx(m['context']),'sources':arr(m['basis'],src),'relation':rel(m['relation']),
      'modelVersion':string(d['model_version']),'modelBasis':string(d['basis']),
      'weights':weights(w),'threshold':rat(d['threshold']),'costs':arr(d['costs'],rat),'options':arr(d['legal_options'],rat)}
    return '{ '+', '.join(k+' := '+v for k,v in parts.items())+' }'

def payload(a):
    parts={'requirement':string(a['requirement']),'principal':rat(a['principal']),
       'rows':rows(a['rows']),'pending':'[]','weights':weights(a['weights']),
       **{k:rat(a[k]) for k in ['expectedC','expectedU','eventProbability','lower','upper']},
       'eligible':arr(a['eligible'],rat),'selected':'none' if a['selected'] is None else 'some '+rat(a['selected']),
       'notice':string(a['notice'])}
    return '{ '+', '.join(k+' := '+v for k,v in parts.items())+' }'

def generate():
    s,m=P.main_fixture();r=P.solve(s);a=P.derive_analytics(s,r,m)
    data={P.FILES[0]:P.render(s,r).encode(),P.FILES[1]:P.render_calculation_json(s,r,m,a).encode()}
    obs=P.normalized_observations(s,m,r,a,data)
    text='''import JurisLean.BusinessRoot.SevenAxis

/- Generated from actual parsed Python fixture bytes. Not an independent legal
source or a verified byte-to-Lean compiler. Never generated from checker PASS
labels. Regenerate and diff in CI before this module is compiled. -/
set_option maxRecDepth 100000
namespace JurisLean.BusinessRoot.SevenAxis.Cases
open JurisLean.BusinessRoot.SevenAxis
'''
    text+='\ndef observedDoc : DocValue :=\n  { metaData := '+dmeta(obs['doc_metadata'])+'\n    mode := "EXACT_FINITE_SCENARIOS", rows := '+rows(obs['doc_rows'])+', pending := [] }\n'
    text+='\ndef observedCalculation : CalculationValue :=\n  { metaData := '+jmeta(obs['json_metadata'])+'\n    mode := "EXACT_FINITE_SCENARIOS", values := '+payload(obs['json_values'])+' }\n'
    text+='''
theorem actual_doc_normalization_matches : observedDoc = expectedDoc := rfl
theorem actual_json_normalization_matches : observedCalculation = expectedCalculation := rfl
theorem actual_bytes_typed_observations_accepted :
    checkSevenAxisBundle selectedInput selectedInput
      (writeDoc observedDoc) (writeCalculation observedCalculation) = true := by
  rw [actual_doc_normalization_matches, actual_json_normalization_matches]
  exact full_projection_accepts_normal
'''
    # Shared mutation IDs mirror Python mutation tests, no semantic change to root.
    mutations=[('caseId','"OTHER-CASE"'),('issue','"OTHER-ISSUE"'),('creditor','"其他权利人"'),('debtor','"丙公司"'),('debtId','"OTHER-DEBT"'),('sourceIds','["OTHER-SOURCE"]'),('dueDay','"2099-01-01"'),('asOfDay','"2099-01-02"'),('assumptions','["UNSUPPORTED-ASSUMPTION"]')]
    for name,value in mutations:
        text+=f'''\ntheorem reject_doc_{name} :
    checkSevenAxisBundle selectedInput selectedInput
      (writeDoc {{ expectedDoc with metaData := {{ expectedDoc.metaData with {name} := {value} }} }})
      (writeCalculation expectedCalculation) = false := by
  apply changed_doc_metadata_rejected
  intro h
  have hf := congrArg DocMeta.{name} h
  simp [expectedDoc, expectedDocMeta, selectedInput, selectedContext] at hf
'''
    for k in sorted(obs['doc_metadata']['context']):
        value='["OTHER-ASSUMPTION"]' if k=='assumptions' else '999' if k=='max_depth' else '"OTHER-VALUE"'
        text+=f'''\ntheorem reject_context_{k} :
    checkSevenAxisBundle selectedInput selectedInput
      (writeDoc {{ expectedDoc with metaData := {{ expectedDoc.metaData with
        context := {{ selectedContext with {k} := {value} }} }} }})
      (writeCalculation expectedCalculation) = false := by
  apply changed_doc_metadata_rejected
  intro h
  have hf := congrArg (fun m : DocMeta => m.context.{k}) h
  simp [expectedDoc, expectedDocMeta, selectedInput, selectedContext] at hf
'''
    text+='\nend JurisLean.BusinessRoot.SevenAxis.Cases\n'
    return text,obs


def main():
    p=argparse.ArgumentParser();p.add_argument('--output',type=Path,required=True);p.add_argument('--observations',type=Path)
    a=p.parse_args();text,obs=generate();a.output.parent.mkdir(parents=True,exist_ok=True);a.output.write_text(text,encoding='utf-8')
    if a.observations:a.observations.parent.mkdir(parents=True,exist_ok=True);a.observations.write_text(json.dumps(obs,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
    print(json.dumps({'fixture_written':str(a.output),'lean':'NOT_RUN'}))
if __name__=='__main__':main()
