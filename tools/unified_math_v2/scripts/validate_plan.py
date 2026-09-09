#!/usr/bin/env python3
"""Validate plan coverage; NOT a substitute for proof/implementation acceptance."""
import json
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
def validate():
 m=ROOT/'manifests'
 tasks=json.loads((m/'tasks.json').read_text())['tasks']
 goals=json.loads((m/'proof_targets.json').read_text())
 tids={t['id'] for t in tasks};gids={g['id'] for g in goals}
 if len(tasks)!=len(tids) or len(goals)!=len(gids):raise ValueError('Repeated IDs')
 if not {f'T{i:02}' for i in range(25)}<=tids:raise ValueError('Original tasks omitted')
 if not {f'REV{i:02}' for i in range(1,10)}<=tids:raise ValueError('Review revisions omitted')
 if len(goals)!=57:raise ValueError('Original target inventory changed without migration')
 for entries,key in ((tasks,'id'),(goals,'id')):
  table={x[key]:x for x in entries};done=set();active=set()
  def visit(n):
   if n not in table:raise ValueError('Unknown dependency '+n)
   if n in active:raise ValueError('Dependency cycle '+n)
   if n in done:return
   active.add(n)
   for dep in table[n].get('depends_on',[]):visit(dep)
   active.remove(n);done.add(n)
  for n in table:visit(n)
 req=json.loads((m/'requirements.json').read_text())
 if len(req)!=26:raise ValueError('Original requirements missing')
 for r in req:
  if not r.get('tasks') or not set(r['tasks'])<=tids or not set(r.get('proof_targets',[]))<=gids:raise ValueError('Unmapped requirement '+r['id'])
 for t in tasks:
  if not set(t.get('proof_targets',[]))<=gids:raise ValueError('Missing target')
 sourceids={s['id'] for s in json.loads((m/'sources.json').read_text())['sources']}
 from sys import path
 path.insert(0,str(ROOT))
 from v21.law_slices import SLICES
 for s in SLICES:
  if s.source_id not in sourceids:raise ValueError('Unregistered law slice source')
 c07=next(g for g in goals if g['id']=='C07')
 if 'E01' in c07.get('depends_on',[]):raise ValueError('Empirical data wrongly blocks all math')
 return {'status':'PASS','scope':'TASK_AND_SOURCE_ID_COVERAGE_ONLY','tasks':len(tasks),'targets':len(goals),
         'legal_families':len(json.loads((m/'legal_families.json').read_text())['families'])}
if __name__=='__main__':print(json.dumps(validate(),ensure_ascii=False,indent=2))
