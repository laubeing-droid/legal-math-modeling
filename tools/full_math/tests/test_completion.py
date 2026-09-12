"""Gate protocol tests use simulated receipts, never claim those are Lean proofs."""
import unittest,sys,json,tempfile,copy
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1];sys.path.insert(0,str(ROOT))
import completion as C

class CompletionProtocolTests(unittest.TestCase):
 def setUp(self):
  self.tmp=tempfile.TemporaryDirectory();self.addCleanup(self.tmp.cleanup);self.p=Path(self.tmp.name)
  self.scope,self.reqs=C.requirements();self.bindings=self.p/'bindings.json'
  self.subject={k:'test-only-'+k for k in ['commit','tree','repository','run_id','attempt','lean_toolchain_sha256','lake_manifest_sha256']}
 def simulated(self):
  b=[];r=[];t=[]
  for req in self.reqs:
   bid=req['id'];name=req['theorem'];pos=bid+':normal';neg=bid+':counterexample'
   b.append({**req,'proof_mode':'KERNEL_CONTRACT_PROOF','generality':'PARAMETRIC',
    'formal_scope':'Simulation of gate protocol only; not mathematical evidence',
    'independent_semantics':'explicit spec','algorithm':'separate implementation','observation_contract':'input-output relation',
    'external_assumptions':'none in this simulated protocol fixture',
    'proof_sources':['proof.lean'],'implementation_sources':['impl.py'],
    'test_ids':[pos],'negative_test_ids':[neg],'semantic_links':['JurisLean.FullMath.Core.component']})
   r.append({'name':name,'kind':'theorem','type':req['contract'],'axioms':[],
    'dependencies':['JurisLean.FullMath.Core.component'],'contract':req['contract'],
    'typecheck':'LEAN_ASSIGNMENT_ELABORATED'})
   t.extend([{'id':pos,'status':'PASS'},{'id':neg,'status':'PASS'}])
  # Explicit connections in this simulated protocol, not real Lean evidence.
  root_names=[x['theorem'] for x in self.reqs if x['id'].startswith('ROOT:')]
  for row in r:
   if row['name']=='JurisLean.FullMath.Acceptance.target_C07':row['dependencies']+=root_names
   if row['name']=='JurisLean.FullMath.Acceptance.target_EXT09':row['dependencies'] += ['JurisLean.FullMath.Acceptance.root_'+n for n in ('CIVIL','CRIMINAL','ADMINISTRATIVE')]
  C.dump(self.bindings,{'bindings':b})
  comp={'subject':self.subject.copy(),'log':C.PREFIX+json.dumps(r)}
  tests={'subject':self.subject.copy(),'status':'PASS','tests':t}
  return comp,tests,[{'path':'proof.lean','sha256':'test'},{'path':'impl.py','sha256':'test'}]
 def verdict(self,co,ts,sr):return C.evaluate_full_plan(C.SPEC,self.bindings,co,ts,sr,self.subject)
 def test_exact_scope_217(self):self.assertEqual(len(self.reqs),217)
 def test_no_bindings_not_done(self):
  v=C.evaluate_full_plan(C.SPEC,self.bindings,{}, {},[],self.subject);self.assertEqual(v['status'],'INCOMPLETE');self.assertEqual(len(v['missing_bindings']),217)
 def test_simulated_full_protocol_success(self):self.assertEqual(self.verdict(*self.simulated())['status'],'MATH_BUILD_COMPLETE')
 def test_one_demonstration_not_done(self):
  co,ts,sr=self.simulated();x=C.read(self.bindings);x['bindings']=x['bindings'][:1];C.dump(self.bindings,x)
  self.assertEqual(self.verdict(co,ts,sr)['status'],'INCOMPLETE')
 def test_56_targets_not_all(self):
  co,ts,sr=self.simulated();x=C.read(self.bindings);x['bindings']=[r for r in x['bindings'] if r['id']!='TARGET:E01'];C.dump(self.bindings,x)
  self.assertIn('TARGET:E01',self.verdict(co,ts,sr)['missing_bindings'])
 def test_133_demands_not_all(self):
  co,ts,sr=self.simulated();x=C.read(self.bindings);x['bindings']=[r for r in x['bindings'] if r['id']!='DEMAND:D134'];C.dump(self.bindings,x)
  self.assertIn('DEMAND:D134',self.verdict(co,ts,sr)['missing_bindings'])
 def test_no_criminal_root_not_all(self):
  co,ts,sr=self.simulated();x=C.read(self.bindings);x['bindings']=[r for r in x['bindings'] if r['id']!='ROOT:CRIMINAL'];C.dump(self.bindings,x)
  self.assertEqual(self.verdict(co,ts,sr)['status'],'INCOMPLETE')
 def test_frozen_generic_root_rejected(self):
  co,ts,sr=self.simulated();x=C.read(self.bindings);x['bindings'][-1]['scope_restriction']='FROZEN_INPUT';C.dump(self.bindings,x)
  self.assertEqual(self.verdict(co,ts,sr)['status'],'INCOMPLETE')
 def test_type_not_elaborated(self):
  co,ts,sr=self.simulated();rows=C.parse_compiled(co['log']);rows[self.reqs[0]['theorem']]['typecheck']='NAME_EXISTS';co['log']=C.PREFIX+json.dumps(list(rows.values()))
  self.assertEqual(self.verdict(co,ts,sr)['status'],'INCOMPLETE')
 def test_sorry_axiom_rejected(self):
  co,ts,sr=self.simulated();rows=list(C.parse_compiled(co['log']).values());rows[0]['axioms']=['sorryAx'];co['log']=C.PREFIX+json.dumps(rows)
  with self.assertRaises(C.EvidenceError):self.verdict(co,ts,sr)
 def test_native_axiom_rejected(self):
  co,ts,sr=self.simulated();rows=list(C.parse_compiled(co['log']).values());rows[0]['axioms']=['Lean.ofReduceBool'];co['log']=C.PREFIX+json.dumps(rows)
  with self.assertRaises(C.EvidenceError):self.verdict(co,ts,sr)
 def test_cross_run_rejected(self):
  co,ts,sr=self.simulated();co['subject']['run_id']='different'
  with self.assertRaises(C.EvidenceError):self.verdict(co,ts,sr)
 def test_failed_test_rejected(self):
  co,ts,sr=self.simulated();ts['tests'][0]['status']='FAIL'
  with self.assertRaises(C.EvidenceError):self.verdict(co,ts,sr)
 def test_skipped_test_rejected(self):
  co,ts,sr=self.simulated();ts['tests'][0]['status']='SKIP'
  with self.assertRaises(C.EvidenceError):self.verdict(co,ts,sr)
 def test_no_adverse_test_rejected(self):
  co,ts,sr=self.simulated();ts['tests']=ts['tests'][:-1];self.assertEqual(self.verdict(co,ts,sr)['status'],'INCOMPLETE')
 def test_disconnected_component(self):
  co,ts,sr=self.simulated();rows=list(C.parse_compiled(co['log']).values());rows[0]['dependencies']=[];co['log']=C.PREFIX+json.dumps(rows)
  self.assertEqual(self.verdict(co,ts,sr)['status'],'INCOMPLETE')
 def test_missing_source_record(self):
  co,ts,sr=self.simulated();self.assertEqual(self.verdict(co,ts,sr[:1])['status'],'INCOMPLETE')
 def test_bad_json_duplicate(self):
  with self.assertRaises(C.EvidenceError):C.loads('{"a":1,"a":2}')
 def test_duplicate_audit_record(self):
  co,ts,sr=self.simulated();co['log']+='\n'+co['log']
  with self.assertRaises(C.EvidenceError):self.verdict(co,ts,sr)
 def test_fixed_root_signature(self):
  co,ts,sr=self.simulated();rows=list(C.parse_compiled(co['log']).values());rows[-1]['type']='selectedInput = selectedInput';co['log']=C.PREFIX+json.dumps(rows)
  self.assertEqual(self.verdict(co,ts,sr)['status'],'INCOMPLETE')
 def test_producer_cannot_self_claim_pass(self):
  C.dump(self.bindings,{'status':'MATH_BUILD_COMPLETE','bindings':[]})
  self.assertEqual(C.evaluate_full_plan(C.SPEC,self.bindings,{}, {},[],self.subject)['status'],'INCOMPLETE')
 def test_scope_id_replacement_rejected(self):
  d=self.p/'spec';d.mkdir()
  sc=copy.deepcopy(self.scope);rs=copy.deepcopy(self.reqs);rs[0]['id']='TARGET:F99'
  C.dump(d/'SCOPE.json',sc);C.dump(d/'REQUIREMENTS.json',rs)
  with self.assertRaises(C.EvidenceError):C.requirements(d)
 def test_safe_path(self):
  (self.p/'x').write_text('ok')
  self.assertEqual(C.safe_file(self.p,'x'),self.p/'x')
  with self.assertRaises(C.EvidenceError):C.safe_file(self.p,'../x')
 def test_contract_alias_cannot_change(self):
  co,ts,sr=self.simulated();x=C.read(self.bindings);x['bindings'][0]['contract']='JurisLean.Trivial';C.dump(self.bindings,x)
  self.assertEqual(self.verdict(co,ts,sr)['status'],'INCOMPLETE')
 def test_all_root_files_without_joint_proof_rejected(self):
  co,ts,sr=self.simulated();rows=list(C.parse_compiled(co['log']).values())
  for row in rows:
   if row['name']=='JurisLean.FullMath.Acceptance.target_C07':row['dependencies']=['JurisLean.FullMath.Core.component']
  co['log']=C.PREFIX+json.dumps(rows);self.assertEqual(self.verdict(co,ts,sr)['status'],'INCOMPLETE')
 def test_three_domain_names_not_real_connection_rejected(self):
  co,ts,sr=self.simulated();rows=list(C.parse_compiled(co['log']).values())
  for row in rows:
   if row['name']=='JurisLean.FullMath.Acceptance.target_EXT09':row['dependencies']=['JurisLean.FullMath.Core.component']
  co['log']=C.PREFIX+json.dumps(rows);self.assertEqual(self.verdict(co,ts,sr)['status'],'INCOMPLETE')
if __name__=='__main__':unittest.main()
