import copy,importlib.util,json,os,subprocess,sys,tempfile,unittest
from pathlib import Path
sys.path.insert(0,str(Path(__file__).resolve().parents[1]))
import ci_evidence as E
BASE=Path(__file__).resolve().parents[3]
sp=importlib.util.spec_from_file_location('changed_modules_candidate',BASE/'scripts/ci/changed_lean_modules.py')
M=importlib.util.module_from_spec(sp);sp.loader.exec_module(M)

class ModulePlannerTests(unittest.TestCase):
    def test_qualified_module(self):
        self.assertEqual(M.module_of('proofs/lean/juris_lean/JurisLean/BusinessRoot/Root.lean'),'JurisLean.BusinessRoot.Root')
    def test_root_module(self):
        self.assertEqual(M.module_of('proofs/lean/juris_lean/JurisLean.lean'),'JurisLean')
    def test_same_basename(self):
        self.assertNotEqual(M.module_of('proofs/lean/juris_lean/JurisLean/A/All.lean'),M.module_of('proofs/lean/juris_lean/JurisLean/B/All.lean'))
    def test_import_comments(self):
        text='/- import JurisLean.False\n /- import JurisLean.Nested -/ -/\nimport JurisLean.A.B\n-- import JurisLean.X\ndef s := "import JurisLean.Y"\npublic import JurisLean.C.D Mathlib'
        self.assertEqual(M.imports(text),{'JurisLean.A.B','JurisLean.C.D'})
    def test_unclosed_comment_is_not_empty_success(self):
        with self.assertRaises(ValueError):M.imports('/- unclosed')
    def test_reverse_transitive(self):
        g=M.reverse_graph({'JurisLean.B':'import JurisLean.A','JurisLean.C':'import JurisLean.B'})
        self.assertEqual(M.affected({'JurisLean.A'},g),{'JurisLean.A','JurisLean.B','JurisLean.C'})
    def test_all_recursive(self):
        with tempfile.TemporaryDirectory() as d:
            p=Path(d)/M.LEAN_BASE/'JurisLean/Deep/Root.lean';p.parent.mkdir(parents=True);p.write_text('import Mathlib')
            result=M.plan(Path(d),all_modules=True)
            self.assertEqual(result['include'][0]['target'],'JurisLean.Deep.Root')
    def test_unknown_explicit_target(self):
        with tempfile.TemporaryDirectory() as d:
            with self.assertRaises(ValueError):M.plan(Path(d),explicit='Missing')
    def test_deleted_reverse_dependents_real_git(self):
        with tempfile.TemporaryDirectory() as d:
            r=Path(d)
            def git(*args):return subprocess.run(['git',*args],cwd=r,check=True,stdout=subprocess.PIPE,stderr=subprocess.PIPE).stdout
            git('init');git('config','user.name','Synthetic Test');git('config','user.email','synthetic@example.invalid')
            x=r/M.LEAN_BASE/'JurisLean/Deep';x.mkdir(parents=True)
            (x/'Gone.lean').write_text('import Mathlib\n')
            (x/'Keep.lean').write_text('import JurisLean.Deep.Gone\n')
            root=r/M.LEAN_BASE/'JurisLean.lean';root.write_text('import JurisLean.Deep.Keep\n')
            git('add','.');git('commit','-m','base');base=git('rev-parse','HEAD').decode().strip()
            (x/'Gone.lean').unlink();git('add','-A');git('commit','-m','deleted')
            got=M.plan(r,base=base)
            self.assertIn('JurisLean.Deep.Gone',got['removed_modules'])
            self.assertEqual({x['target'] for x in got['include']},{'JurisLean.Deep.Keep','JurisLean'})
    def test_bad_base_not_empty_matrix(self):
        with tempfile.TemporaryDirectory() as d:
            subprocess.run(['git','init'],cwd=d,check=True,capture_output=True)
            with self.assertRaises(subprocess.CalledProcessError):M.plan(Path(d),base='NONEXISTENT')

class EvidenceTests(unittest.TestCase):
    def setUp(self):
        self.tmp=tempfile.TemporaryDirectory();self.r=Path(self.tmp.name)
        (self.r/'actual.log').write_text('SYNTHETIC_TEST_LOG')
        self.s={k:'test-'+k for k in E.IDENTITY_FIELDS}
        self.receipt=E.bundle_receipt(self.r,self.s,'seven-axis')
    def tearDown(self):self.tmp.cleanup()
    def test_normal(self):E.verify_receipt(self.r,self.receipt,self.s,'seven-axis')
    def test_tampered_file(self):
        (self.r/'actual.log').write_text('TAMPERED')
        with self.assertRaises(ValueError):E.verify_receipt(self.r,self.receipt,self.s,'seven-axis')
    def test_unlisted_file(self):
        (self.r/'unlisted').write_text('extra')
        with self.assertRaises(ValueError):E.verify_receipt(self.r,self.receipt,self.s,'seven-axis')
    def test_missing_file(self):
        (self.r/'actual.log').unlink()
        with self.assertRaises(ValueError):E.verify_receipt(self.r,self.receipt,self.s,'seven-axis')
    def test_bad_kind(self):
        with self.assertRaises(ValueError):E.verify_receipt(self.r,self.receipt,self.s,'other')
    def test_path_escape(self):
        a=copy.deepcopy(self.receipt);a['files'][0]['path']='../secret'
        with self.assertRaises(ValueError):E.verify_receipt(self.r,a,self.s,'seven-axis')
    def test_gate_requires_jobs(self):
        with self.assertRaises(ValueError):E.verify_jobs({'old':{'result':'success'}},{'old','new'})
    def test_gate_cancel_not_success(self):
        with self.assertRaises(ValueError):E.verify_jobs({'new':{'result':'cancelled'}},{'new'})
    def test_gate_skipped_not_success(self):
        with self.assertRaises(ValueError):E.verify_jobs({'new':{'result':'skipped'}},{'new'})
    def test_gate_pass(self):E.verify_jobs({'new':{'result':'success'}},{'new'})
    def test_flatten_rejects_different_bytes(self):
        src=self.r/'src';(src/'one').mkdir(parents=True);(src/'two').mkdir()
        (src/'one/receipt.json').write_text('one');(src/'two/receipt.json').write_text('two')
        with self.assertRaises(ValueError):E.flatten_without_overwrite(src,self.r/'flat')
    def test_flatten_same_bytes(self):
        src=self.r/'src';(src/'one').mkdir(parents=True);(src/'two').mkdir()
        (src/'one/x').write_text('same');(src/'two/x').write_text('same')
        E.flatten_without_overwrite(src,self.r/'flat');self.assertEqual((self.r/'flat/x').read_text(),'same')
    def envlog(self):
        deps=['JurisLean.BusinessRoot.root_worlds_match','JurisLean.BusinessRoot.root_joint_sem','JurisLean.BusinessRoot.root_task_sat']
        rows=[{'name':E.PREFIX+n,'axioms':['propext'],'proof_dependencies':deps if n=='seven_axis_business_root' else []} for n in E.REQUIRED]
        return rows
    def test_environment_synthetic_shape_only(self):
        rows=self.envlog();r=E.verify_environment('SEVEN_AXIS_COMPILED_ENV_JSON='+json.dumps(rows));self.assertEqual(r['status'],'PASS')
    def test_environment_missing_root(self):
        rows=[x for x in self.envlog() if not x['name'].endswith('.seven_axis_business_root')]
        with self.assertRaises(ValueError):E.verify_environment('SEVEN_AXIS_COMPILED_ENV_JSON='+json.dumps(rows))
    def test_environment_sorry_axiom(self):
        rows=self.envlog();rows[0]['axioms']=['sorryAx']
        with self.assertRaises(ValueError):E.verify_environment('SEVEN_AXIS_COMPILED_ENV_JSON='+json.dumps(rows))
    def test_environment_disconnected(self):
        rows=self.envlog()
        for row in rows:row['proof_dependencies']=[]
        with self.assertRaises(ValueError):E.verify_environment('SEVEN_AXIS_COMPILED_ENV_JSON='+json.dumps(rows))
    def test_environment_duplicate_report(self):
        line='SEVEN_AXIS_COMPILED_ENV_JSON='+json.dumps(self.envlog())
        with self.assertRaises(ValueError):E.verify_environment(line+'\n'+line)

for key in E.IDENTITY_FIELDS:
    def make_test(self,key=key):
        s=dict(self.s);s[key]+='-CHANGED'
        with self.assertRaises(ValueError):E.verify_receipt(self.r,self.receipt,s,'seven-axis')
    setattr(EvidenceTests,'test_identity_'+key,make_test)

if __name__=='__main__':unittest.main()
