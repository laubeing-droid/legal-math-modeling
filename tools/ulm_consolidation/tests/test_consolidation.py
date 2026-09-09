"""Tooling tests. Fake environment rows below test the log validator only,
not Lean compilation. New code does not reinterpret retained legal algorithms.
"""
from pathlib import Path
import copy,hashlib,importlib.util,json,sys,tempfile,unittest
R=Path(__file__).resolve().parents[1];sys.path.insert(0,str(R/'scripts'))
import validate_plan as vp
import audit_compiled as ac
import ci_receipt as cr
sp=importlib.util.spec_from_file_location('installer',R/'install_overlay.py');ins=importlib.util.module_from_spec(sp);sp.loader.exec_module(ins)

class PlanTests(unittest.TestCase):
    def test_full_preservation(self):self.assertEqual(vp.validate(R/'plans')['requirements'],134)
    def test_unknown_dependency(self):
        with self.assertRaises(ValueError):vp.check_dag([{'id':'a','depends_on':['missing']}])
    def test_cycle(self):
        with self.assertRaises(ValueError):vp.check_dag([{'id':'a','depends_on':['b']},{'id':'b','depends_on':['a']}])
    def test_duplicate_task(self):
        with self.assertRaises(ValueError):vp.check_dag([{'id':'a'},{'id':'a'}])
    def test_root_not_blocked_on_real_data(self):
        roots=json.loads((R/'plans/ROOT_TASKS.json').read_text());self.assertNotIn('T15',[d for t in roots for d in t['depends_on']])
    def test_nonempty_root_gap(self):
        tasks=json.loads((R/'plans/ROOT_TASKS.json').read_text());self.assertTrue(all(t['status']=='PENDING_CONCRETE_IMPLEMENTATION_OR_PROOF' for t in tasks))

class AuditTests(unittest.TestCase):
    def fixture(self):
        expected={'declarations':[{'name':'JurisLean.BusinessRelations.demo'}]}
        row={'name':'JurisLean.BusinessRelations.demo','axioms':['propext'],'proof_dependencies':[]}
        return expected,row
    def test_valid_validator_fixture_not_compiler_result(self):
        e,r=self.fixture();self.assertEqual(ac.verify_log(ac.PREFIX+json.dumps([r]),e)['scope'],'COMPILED_RETAINED_SEEDS_ONLY')
    def test_missing_declaration(self):
        e,r=self.fixture();e['declarations'].append({'name':'JurisLean.BusinessRelations.missing'})
        with self.assertRaises(ValueError):ac.verify_log(ac.PREFIX+json.dumps([r]),e)
    def test_sorry_axiom_rejected(self):
        e,r=self.fixture();r['axioms']=['sorryAx']
        with self.assertRaises(ValueError):ac.verify_log(ac.PREFIX+json.dumps([r]),e)
    def test_duplicate_report(self):
        e,r=self.fixture();t=ac.PREFIX+json.dumps([r])
        with self.assertRaises(ValueError):ac.verify_log(t+'\n'+t,e)
    def test_duplicate_declaration(self):
        e,r=self.fixture()
        with self.assertRaises(ValueError):ac.verify_log(ac.PREFIX+json.dumps([r,r]),e)
    def test_foreign_namespace(self):
        e,r=self.fixture();r['name']='Unrelated.fake'
        with self.assertRaises(ValueError):ac.verify_log(ac.PREFIX+json.dumps([r]),e)

class InstallTests(unittest.TestCase):
    def setUp(self):
        self.tmp=tempfile.TemporaryDirectory();self.root=Path(self.tmp.name);self.pkg=self.root/'pkg';self.repo=self.root/'repo';self.repo.mkdir();(self.pkg/'overlays/lmm/a').mkdir(parents=True)
        (self.pkg/'overlays/lmm/a/b.txt').write_bytes(b'new')
        self.m={'roles':{'lmm':[{'path':'a/b.txt','sha256':ins.digest(b'new'),'reviewed_overwrite_sha256':[ins.digest(b'old')]}]}}
        (self.pkg/'PAYLOAD_MANIFEST.json').write_text(json.dumps(self.m))
    def tearDown(self):self.tmp.cleanup()
    def test_preview_no_write(self):
        x=ins.install(self.pkg,self.repo,'lmm');self.assertEqual(x['mode'],'PREVIEW_NO_WRITES');self.assertFalse((self.repo/'a').exists())
    def test_apply_idempotent(self):
        ins.install(self.pkg,self.repo,'lmm',True);self.assertEqual(ins.plan(self.pkg,self.repo,'lmm')[0]['action'],'unchanged')
    def test_reviewed_old_content_backup(self):
        (self.repo/'a').mkdir();(self.repo/'a/b.txt').write_bytes(b'old');v=ins.install(self.pkg,self.repo,'lmm',True)
        self.assertEqual((Path(v['backup'])/'before/a/b.txt').read_bytes(),b'old')
    def test_unknown_change_refused(self):
        (self.repo/'a').mkdir();(self.repo/'a/b.txt').write_bytes(b'user change')
        with self.assertRaises(ValueError):ins.install(self.pkg,self.repo,'lmm',True)
        self.assertEqual((self.repo/'a/b.txt').read_bytes(),b'user change')
    def test_payload_tamper_refused(self):
        (self.pkg/'overlays/lmm/a/b.txt').write_bytes(b'tamper')
        with self.assertRaises(ValueError):ins.plan(self.pkg,self.repo,'lmm')
    def test_traversal_refused(self):
        self.m['roles']['lmm'][0]['path']='../out';(self.pkg/'PAYLOAD_MANIFEST.json').write_text(json.dumps(self.m))
        with self.assertRaises(ValueError):ins.plan(self.pkg,self.repo,'lmm')
    def test_symlink_refused(self):
        elsewhere=self.root/'else';elsewhere.mkdir();(self.repo/'a').symlink_to(elsewhere,target_is_directory=True)
        with self.assertRaises(ValueError):ins.plan(self.pkg,self.repo,'lmm')
    def test_preflight_all_before_write(self):
        self.m['roles']['lmm'].append({'path':'missing','sha256':'0'*64});(self.pkg/'PAYLOAD_MANIFEST.json').write_text(json.dumps(self.m))
        with self.assertRaises(ValueError):ins.install(self.pkg,self.repo,'lmm',True)
        self.assertFalse((self.repo/'a').exists())

class ReceiptTests(unittest.TestCase):
    def files(self,root,binding):
        for n in ['consolidated-python.json','consolidated-lean.json','consolidated-jc.json']:
            (root/n).write_text(json.dumps({'status':'PASS','scope':'TEST_LOG_VALIDATOR_FIXTURE','ci_binding':binding}))
    def test_matching_log_fixture_stays_reference(self):
        with tempfile.TemporaryDirectory() as t:
            p=Path(t);self.files(p,{'a':1});r=cr.aggregate(p,{'a':1});self.assertEqual(r['root_refinement'],'NOT_CLOSED_BY_THIS_WORKFLOW')
    def test_stale_attempt_rejected(self):
        with tempfile.TemporaryDirectory() as t:
            p=Path(t);self.files(p,{'attempt':1})
            with self.assertRaises(ValueError):cr.aggregate(p,{'attempt':2})
    def test_duplicate_artifact_rejected(self):
        with tempfile.TemporaryDirectory() as t:
            p=Path(t);self.files(p,{});(p/'dup').mkdir();(p/'dup/consolidated-python.json').write_text((p/'consolidated-python.json').read_text())
            with self.assertRaises(ValueError):cr.aggregate(p,{})
    def test_nonpass_rejected(self):
        with tempfile.TemporaryDirectory() as t:
            p=Path(t);self.files(p,{});(p/'consolidated-lean.json').write_text(json.dumps({'status':'NOT_RUN','ci_binding':{}}))
            with self.assertRaises(ValueError):cr.aggregate(p,{})
if __name__=='__main__':unittest.main()
