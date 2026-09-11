from __future__ import annotations
import copy,dataclasses,json,sys,tempfile,unittest
from fractions import Fraction as Q
from pathlib import Path
sys.path.insert(0,str(Path(__file__).resolve().parents[1]))
import projection_reference as P


class ProjectionTests(unittest.TestCase):
    def setUp(self):
        self.s,self.m=P.main_fixture();self.r=P.solve(self.s)
        self.a=P.derive_analytics(self.s,self.r,self.m)
        self.selected=P.snapshot_inputs(self.s,self.m)
        self.raw={P.FILES[0]:P.render(self.s,self.r).encode(),
          P.FILES[1]:P.render_calculation_json(self.s,self.r,self.m,self.a).encode()}
    def verdict(self,raw=None,m=None,a=None,s=None,r=None):
        return P.verify_full_observations(self.selected,s or self.s,r or self.r,
            m or self.m,a or self.a,self.raw if raw is None else raw)
    def test_normal_actual_files(self):
        with tempfile.TemporaryDirectory() as d:
            self.assertTrue(P.materialize(Path(d))['accepted'])
    def test_selected_whole_model_swap(self):
        m=dataclasses.replace(self.m,threshold=Q(700),costs=(Q(0),)*4,legal_options=(Q(880),))
        a=P.derive_analytics(self.s,self.r,m)
        raw={P.FILES[0]:P.render(self.s,self.r).encode(),P.FILES[1]:P.render_calculation_json(self.s,self.r,m,a).encode()}
        self.assertEqual(self.verdict(raw,m=m,a=a).reason,'SELECTED_INPUTS_CHANGED')
    def test_legitimate_new_input_not_forbidden(self):
        m=dataclasses.replace(self.m,threshold=Q(700))
        a=P.derive_analytics(self.s,self.r,m)
        raw={P.FILES[0]:P.render(self.s,self.r).encode(),P.FILES[1]:P.render_calculation_json(self.s,self.r,m,a).encode()}
        new=P.snapshot_inputs(self.s,m)
        self.assertTrue(P.verify_full_observations(new,self.s,self.r,m,a,raw).accepted)
    def test_overpay_semantics(self):
        s=P.demo_spec(principal=Q(100));r=P.solve(s)
        m=dataclasses.replace(self.m,context=s.context,threshold=Q(0),costs=(Q(0),)*4,legal_options=(Q(60),))
        a=P.derive_analytics(s,r,m)
        table={o.world:o for o in r.outcomes}
        u=sum((p*table[w].overpayment_residual for w,p in m.weights),Q(0))
        self.assertEqual((a.expected,u,a.expected-u,a.event_probability),(Q(60),Q(80),Q(-20),Q(1)))
    def test_json_duplicate_key(self):
        raw=dict(self.raw);t=raw[P.FILES[1]].decode();raw[P.FILES[1]]=('{"schema":"evil",'+t[1:]).encode()
        self.assertFalse(self.verdict(raw).accepted)
    def test_extra_file(self):
        raw={**self.raw,'extra.json':b'{}'};self.assertFalse(self.verdict(raw).accepted)
    def test_missing_file(self):
        self.assertFalse(self.verdict({P.FILES[0]:self.raw[P.FILES[0]]}).accepted)
    def test_unjustified_paragraph(self):
        raw=dict(self.raw);raw[P.FILES[0]]+= '因此必胜。\n'.encode();self.assertFalse(self.verdict(raw).accepted)
    def test_row_order_normalization(self):
        raw=dict(self.raw);lines=raw[P.FILES[0]].decode().splitlines();lines[13:15]=reversed(lines[13:15]);raw[P.FILES[0]]=('\n'.join(lines)+'\n').encode()
        self.assertTrue(self.verdict(raw).accepted)
        obs=P.normalized_observations(self.s,self.m,self.r,self.a,raw)
        self.assertEqual(obs['doc_rows'][0][0],[('payment_recognized',True)])
    def test_no_implicit_full_model_witness_from_output(self):
        obj=P.parse_json(self.raw[P.FILES[1]].decode());obj['decision_inputs']['threshold']='9999';obj['analytics']['event_probability']='3/5'
        raw=dict(self.raw);raw[P.FILES[1]]=json.dumps(obj,ensure_ascii=False).encode()
        self.assertFalse(self.verdict(raw).accepted)
    def test_selected_860_not_legal(self):
        obj=P.parse_json(self.raw[P.FILES[1]].decode());obj['analytics']['selected']='860'
        raw=dict(self.raw);raw[P.FILES[1]]=json.dumps(obj,ensure_ascii=False).encode()
        self.assertFalse(self.verdict(raw).accepted)
    def test_pending_cannot_inherit_exact(self):
        r=P.solve(self.s,budget=1)
        self.assertNotEqual(r.mode,'EXACT_FINITE_SCENARIOS')
        self.assertFalse(self.verdict(r=r).accepted)
    def test_i0_full_source_body_is_bound(self):
        src=self.s.sources[0];newbody=src.body+'；附记'
        ns=dataclasses.replace(src,body=newbody)
        s=dataclasses.replace(self.s,sources=(ns,))
        self.assertFalse(self.verdict(s=s).accepted)


# Separate generated test methods: report actual executions, never multiply one
# test by internal assertions to claim thousands of independent legal examples.
def leaves(x,path=()):
    if isinstance(x,dict):
        for k,v in x.items():yield from leaves(v,path+(k,))
    elif isinstance(x,list):
        if not x:yield path,x
        else:
            for k,v in enumerate(x):yield from leaves(v,path+(k,))
    else:yield path,x

def replace_at(root,path,new):
    node=root
    for k in path[:-1]:node=node[k]
    node[path[-1]]=new

def other(v):
    if type(v) is bool:return not v
    if type(v) is int:return v+1
    if v is None:return '0'
    if type(v) is list:return [['unknown',True]]
    try:return str(Q(v)+1)
    except (ValueError,TypeError,ZeroDivisionError):return str(v)+'__CHANGED'

_s,_m=P.main_fixture();_r=P.solve(_s);_a=P.derive_analytics(_s,_r,_m)
_j=P.parse_json(P.render_calculation_json(_s,_r,_m,_a))
for idx,(path,value) in enumerate(leaves(_j)):
    def test(self,path=path,value=value):
        obj=P.parse_json(self.raw[P.FILES[1]].decode());replace_at(obj,path,other(value))
        raw=dict(self.raw);raw[P.FILES[1]]=json.dumps(obj,ensure_ascii=False).encode()
        self.assertFalse(self.verdict(raw).accepted,msg=str(path))
    test.__doc__='Reject JSON leaf mutation at '+str(path)
    setattr(ProjectionTests,'test_json_leaf_'+str(idx).zfill(3),test)

_context=json.loads(_s.context.canonical_json())
for key,value in _context.items():
    def test(self,key=key,value=value):
        lines=self.raw[P.FILES[0]].decode().splitlines()
        c=P.parse_json(lines[11].split('：',1)[1]);c[key]=other(value)
        lines[11]='共同语境：'+json.dumps(c,ensure_ascii=False)
        raw=dict(self.raw);raw[P.FILES[0]]=('\n'.join(lines)+'\n').encode()
        self.assertFalse(self.verdict(raw).accepted)
    setattr(ProjectionTests,'test_doc_context_'+key,test)

for line_index in list(range(0,11))+[12]:
    def test(self,line_index=line_index):
        lines=self.raw[P.FILES[0]].decode().splitlines()
        if line_index in (0,1):lines[line_index]+='修改'
        elif line_index in (8,9):lines[line_index]=lines[line_index].split('：')[0]+'：2099-01-01'
        elif line_index==12:lines[line_index]='结论状态：PARTIAL_SCENARIOS'
        else:
            label,value=lines[line_index].split('：',1)
            old=P.parse_json(value);value=old+['无依据'] if type(old) is list else str(old)+'修改'
            lines[line_index]=label+'：'+json.dumps(value,ensure_ascii=False)
        raw=dict(self.raw);raw[P.FILES[0]]=('\n'.join(lines)+'\n').encode()
        self.assertFalse(self.verdict(raw).accepted)
    setattr(ProjectionTests,'test_doc_header_'+str(line_index),test)

if __name__=='__main__':unittest.main()
