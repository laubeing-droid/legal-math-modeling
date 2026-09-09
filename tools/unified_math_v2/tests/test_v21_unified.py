from dataclasses import replace
from fractions import Fraction as Q
import unittest, json
from v21.context import *
from v21.checker import *
from v21.authority import *
from v21.model_binding import *
from v21.bridge import *
from v21.claims import *
from v21.argument_mapping import *
from v21.law_slices import *
from v21.demo import main_demo
from v21.joint import JointInput,evaluate_joint,check_joint
from unified.arguments import Argument,Leaf,Rule,generate
from reference.core import Node

class IdentityTests(unittest.TestCase):
    def test_roundtrip(self):
        c=synthetic_context(request='案:一',assumptions=('b','a'))
        self.assertEqual(ContextKey.from_json(c.canonical_json()),c)
    def test_no_delimiter_collision(self):
        a=synthetic_context(request='a:b',scenario='c');b=synthetic_context(request='a',scenario='b:c')
        self.assertNotEqual(a.structural_key(),b.structural_key())
    def test_every_semantic_field_matters(self):
        c=synthetic_context()
        from dataclasses import fields
        for f in fields(c):
            if f.name in {'assumptions','max_depth'}:continue
            with self.subTest(f=f.name),self.assertRaises(ValueError):
                require_same_context(c,replace(c,**{f.name:getattr(c,f.name)+'-other'}))
    def test_depth_matters(self):
        with self.assertRaises(ValueError):require_same_context(synthetic_context(),synthetic_context(max_depth=3))
    def test_unknown_json_field(self):
        o=json.loads(synthetic_context().canonical_json());o['forged']='x'
        with self.assertRaises(ValueError):ContextKey.from_json(json.dumps(o))
    def test_duplicate_json_field(self):
        with self.assertRaises(ValueError):ContextKey.from_json('{"request":"a","request":"b"}')
    def test_duplicate_assumption(self):
        with self.assertRaises(ValueError):synthetic_context(assumptions=('x','x'))

class CheckerTests(unittest.TestCase):
    def setUp(self):self.c=synthetic_context();self.p=AffineIntegerProblem(0,8,Q(2),Q(1),Q(8))
    def test_exact(self):
        cert=solve(self.c,self.p)
        self.assertTrue(check_partition(self.c,self.p,cert));self.assertEqual(cert.found,frozenset(range(4,9)))
    def test_partial(self):
        cert=solve(self.c,self.p,5)
        self.assertTrue(check_partition(self.c,self.p,cert));self.assertFalse(cert.complete)
    def test_wrong_solver_cannot_validate_itself(self):
        cert=PartitionCertificate(self.c,self.p,frozenset(range(9)),frozenset(),frozenset(),True)
        self.assertFalse(check_partition(self.c,self.p,cert))
    def test_fake_complete(self):
        self.assertFalse(check_partition(self.c,self.p,replace(solve(self.c,self.p,0),complete=True)))
    def test_missing_candidate(self):
        cert=solve(self.c,self.p)
        self.assertFalse(check_partition(self.c,self.p,replace(cert,found=cert.found-{8})))
    def test_wrong_context(self):
        self.assertFalse(check_partition(replace(self.c,model_version='other'),self.p,solve(self.c,self.p)))
    def test_custom_checker_id(self):
        self.assertFalse(check_partition(self.c,self.p,replace(solve(self.c,self.p),checker_id='my-own')))
    def test_unknown_problem(self):
        with self.assertRaises(TypeError):candidate_domain(lambda x:True)
    def test_no_callback_in_certificate(self):
        from dataclasses import fields
        self.assertNotIn('predicate',{f.name for f in fields(PartitionCertificate)})
    def test_empty_extension_family(self):
        p=DungProblem(('a','b','c'),frozenset({('a','b'),('b','c'),('c','a')}),'stable')
        cert=solve(self.c,p);self.assertEqual(cert.found,frozenset())
        self.assertTrue(check_partition(self.c,p,cert))
    def test_family_containing_empty_extension(self):
        p=DungProblem((),frozenset(),'stable');cert=solve(self.c,p)
        self.assertEqual(cert.found,frozenset({frozenset()}));self.assertTrue(check_partition(self.c,p,cert))
    def test_incomplete_universal_unknown(self):
        p=DungProblem(('a','b'),frozenset({('a','b'),('b','a')}),'stable')
        cert=solve(self.c,p,0)
        self.assertIsNone(checked_query(self.c,p,cert,('a',))['common'])
    def test_prefix_maximality_not_enough(self):
        p=DungProblem(('a','b'),frozenset(),'preferred')
        bad=PartitionCertificate(self.c,p,frozenset({frozenset({'a'})}),frozenset(),
            frozenset({frozenset(),frozenset({'b'}),frozenset({'a','b'})}),False)
        self.assertFalse(check_partition(self.c,p,bad))
    def test_all_512_three_node_graphs_independent_stable_and_grounded(self):
        names=('a','b','c');pairs=[(a,b) for a in names for b in names]
        for mask in range(512):
            edges=frozenset(p for i,p in enumerate(pairs) if mask>>i&1)
            for profile in ('grounded','stable','complete','preferred'):
                p=DungProblem(names,edges,profile)
                self.assertTrue(check_partition(self.c,p,solve(self.c,p)),(mask,profile))

class RepresentationTests(unittest.TestCase):
    def setUp(self):self.c=synthetic_context();self.p=IntervalProblem((Q(0),),(Q(1),))
    def test_real_interval_exact(self):self.assertTrue(check_interval_exact(self.c,self.c,self.p,IntervalRep(0,1)))
    def test_endpoints_not_exact(self):self.assertFalse(check_interval_exact(self.c,self.c,self.p,EnumRep(frozenset({0,1}))))
    def test_too_wide_not_exact(self):self.assertFalse(check_interval_exact(self.c,self.c,self.p,IntervalRep(-1,2)))
    def test_empty(self):self.assertTrue(check_interval_exact(self.c,self.c,IntervalProblem((2,),(1,)),EmptyRep()))
    def test_degenerate_not_empty(self):self.assertFalse(check_interval_exact(self.c,self.c,IntervalProblem((1,),(1,)),EmptyRep()))
    def test_positive_scaled_polyhedron(self):
        p=Polyhedron(((1,),(-1,)),(1,0));r=Polyhedron(((2,),(-3,)),(2,0))
        self.assertTrue(check_polyhedral_exact(p,r,((2,0),(0,3)),((Q(1,2),0),(0,Q(1,3)))))
    def test_negative_multiplier_rejected(self):
        p=Polyhedron(((1,),),(1,));r=Polyhedron(((-1,),),(-1,))
        self.assertFalse(check_polyhedral_inclusion(p,r,((-1,),)))
    def test_missing_reverse_inclusion(self):
        p=Polyhedron(((1,),),(1,));r=Polyhedron(((1,),),(2,))
        self.assertFalse(check_polyhedral_exact(p,r,((1,),),((1,),)))

class AuthorizationTests(unittest.TestCase):
    def setUp(self):self.c=synthetic_context()
    def record(self,**changes):
        r=AuthorityRecord('r',self.c,'trusted-source','institutional_finding','content',
                          '2026-01-01','2026-12-31','institutional_source_verified')
        return replace(r,**changes)
    def test_local_no_keys(self):self.assertEqual(local_analysis_projection(self.c,self.c.assumptions)['signature_status'],'not_used')
    def test_role_string_does_not_issue(self):
        r=institutional_projection(ExistingHostRecords(),context=self.c,record_id='court',content_ref='self-authored',at_date='2026-09-09')
        self.assertEqual(r['status'],'pending_institutional_verification')
    def test_trusted_matching_record(self):
        self.assertTrue(ExistingHostRecords((self.record(),)).authorizes('r',self.c,'institutional_finding','content','2026-09-09'))
    def test_local_record_not_external(self):self.assertFalse(ExistingHostRecords((self.record(evidence_class='local_record'),)).authorizes('r',self.c,'institutional_finding','content','2026-09-09'))
    def test_revoked(self):self.assertFalse(ExistingHostRecords((self.record(revoked=True),)).authorizes('r',self.c,'institutional_finding','content','2026-09-09'))
    def test_expired(self):self.assertFalse(ExistingHostRecords((self.record(),)).authorizes('r',self.c,'institutional_finding','content','2027-01-01'))
    def test_wrong_issue(self):self.assertFalse(ExistingHostRecords((self.record(),)).authorizes('r',replace(self.c,issue='other'),'institutional_finding','content','2026-09-09'))
    def test_wrong_content(self):self.assertFalse(ExistingHostRecords((self.record(),)).authorizes('r',self.c,'institutional_finding','altered','2026-09-09'))

class ModelTests(unittest.TestCase):
    def setUp(self):
        self.c=synthetic_context();self.nodes=(Node('R',('yes','no'),(),{():(Q(1,2),Q(1,2))}),
          Node('E',('yes','no'),('R',),{('yes',):(Q(4,5),Q(1,5)),('no',):(Q(1,5),Q(4,5))}))
        self.m=bind_synthetic_model(self.c,self.nodes)
    def obs(self,**changes):
        return replace(BoundObservation(self.c,'o','source','snap','E','yes'),**changes)
    def test_material_changes_forecast(self):
        yes=outcome_forecast(self.m,'R',(self.obs(),))['probabilities']['yes']
        no=outcome_forecast(self.m,'R',(self.obs(value='no'),))['probabilities']['yes']
        self.assertEqual((yes,no),(Q(4,5),Q(1,5)))
    def test_mismatched_actual_cpt(self):
        with self.assertRaises(ValueError):replace(self.m,parameters=(replace(self.m.parameters[0],value=Q(1,3)),)+self.m.parameters[1:])
    def test_missing_binding(self):
        with self.assertRaises(ValueError):replace(self.m,parameters=self.m.parameters[1:])
    def test_duplicate_binding(self):
        with self.assertRaises(ValueError):replace(self.m,parameters=self.m.parameters+(self.m.parameters[0],))
    def test_copied_evidence_not_double_counted(self):
        one=outcome_forecast(self.m,'R',(self.obs(),))
        two=outcome_forecast(self.m,'R',(self.obs(),self.obs(observation_id='copy')))
        self.assertEqual(one['probabilities'],two['probabilities'])
    def test_correlated_source_requires_joint_model(self):
        with self.assertRaises(ValueError):validate_observations(self.m,(self.obs(),self.obs(observation_id='other',variable='R')))
    def test_foreign_context(self):
        with self.assertRaises(ValueError):outcome_forecast(self.m,'R',(self.obs(context=replace(self.c,evidence_version='other')),))

class BridgeTests(unittest.TestCase):
    def setUp(self):
        self.c=synthetic_context()
        self.x=SettlementInput(self.c,100,30,Q(1,2),Q(1,2),5,5,0,0,(0,80,85,90,100),'stipulated',80)
    def test_shared_dependency_chain(self):
        r=solve_settlement(self.x);self.assertTrue(check_settlement(self.c,self.x,r));self.assertEqual(r['ir_lower'],80)
    def test_arbitrary_lo_rejected(self):
        r=solve_settlement(self.x);r['ir_lower']=10**9
        self.assertFalse(check_settlement(self.c,self.x,r))
    def test_disconnected_lawful_set_no_midpoint(self):
        x=replace(self.x,due=Q(10),paid=Q(10),lawful_candidates=(Q(0),Q(10)),claimant_litigation_cost=Q(20),defendant_litigation_cost=Q(20))
        r=solve_settlement(x);self.assertIn(r['selected'],(0,10));r['selected']=Q(5)
        self.assertFalse(check_settlement(self.c,x,r))
    def test_nonempty_lawful_set_empty_intersection(self):
        x=replace(self.x,lawful_candidates=(Q(0),Q(10)))
        r=solve_settlement(x);self.assertIsNone(r['selected']);self.assertTrue(check_settlement(self.c,x,r))
    def test_two_party_beliefs(self):
        x=replace(self.x,defendant_probability_recognized=Q(1))
        r=solve_settlement(x);self.assertNotEqual(r['claimant_expectation'],r['defendant_expectation'])
    def test_preserve_overpayment(self):
        x=replace(self.x,paid=Q(200));self.assertEqual(solve_settlement(x)['branches'][0][1],-100)
    def test_no_empirical_upgrade(self):
        r=solve_settlement(self.x);r['empirical_status']='VALIDATED'
        self.assertFalse(check_settlement(self.c,self.x,r))
    def test_demo(self):self.assertEqual(main_demo()['bridge']['fact_promotions'],0)

class ArgumentTests(unittest.TestCase):
    def test_occurrences_preserve_repeated_atom(self):
        args=generate('ctx',(Leaf('a','a'),),(Rule('r1',('a',),'b'),Rule('r2',('b',),'a')),2)
        root=next(x for x in args if x.head=='a' and x.depth==2)
        self.assertTrue(occurrence_graph_well_founded(to_occurrence_graph(root)))
        with self.assertRaises(ValueError):legacy_projection(root)
    def test_acyclic_projection(self):
        root=next(x for x in generate('ctx',(Leaf('a','a'),),(Rule('r1',('a',),'b'),),1) if x.head=='b')
        self.assertEqual(legacy_projection(root)['assurance'],'acyclic_projection_only_not_full_refinement')
    def test_unbounded_claim_refused(self):
        with self.assertRaises(ValueError):require_declared_scope(synthetic_context(),requested_unbounded=True)
    def test_deeper_attacker_changes_shallow_grounded(self):
        a=DungProblem(('a',),frozenset(),'grounded');b=DungProblem(('a','b'),frozenset({('b','a')}),'grounded')
        self.assertIn(frozenset({'a'}),solve(synthetic_context(),a).found)
        self.assertNotIn(frozenset({'a'}),solve(synthetic_context(),b).found)

class LawAndClaimsTests(unittest.TestCase):
    def test_every_slice_requires_actual_conditions(self):
        for s in SLICES:
            c=synthetic_context(issue=s.identity)
            yes=evaluate_slice(c,s.identity,{k:'true' for k in s.required})
            self.assertEqual(yes['status'],'conditional_consequence')
            for k in s.required:
                f={x:'true' for x in s.required};f[k]='unknown'
                self.assertEqual(evaluate_slice(c,s.identity,f)['status'],'pending')
    def test_criminal_not_money(self):
        r=evaluate_slice(synthetic_context(),'criminal-200-3',{k:'true' for k in SLICES[1].required})
        self.assertEqual(r['consequence'],'conditional_evidence_insufficient_acquittal')
    def test_plain_probability_not_finding(self):
        with self.assertRaises(ValueError):evaluate_slice(synthetic_context(),'labor-evidence-6',{'rule_applicable':0.99})
    def test_mathematics_not_waiting_for_empirical_data(self):
        ev={k:{'status':'PASS','subject':'s'} for k in REQUIRED['lean_specification']}
        self.assertTrue(claim_check('lean_specification','s',ev)['accepted'])
        self.assertFalse(claim_check('externally_validated_forecast','s',ev)['accepted'])
    def test_skip_is_not_pass(self):
        self.assertFalse(claim_check('reference_model_result','s',{'reference_checks':{'status':'SKIP','subject':'s'}})['accepted'])
    def test_wrong_subject_evidence(self):
        self.assertFalse(claim_check('reference_model_result','s',{'reference_checks':{'status':'PASS','subject':'other'}})['accepted'])

class JointTests(ModelTests):
    def joint(self):
        p=DungProblem(('entitlement',),frozenset(),'grounded')
        return JointInput(self.c,p,frozenset({'entitlement'}),self.m,(self.obs(),),'R','yes',
                          (Q(100),Q(40),Q(5),Q(4),Q(1,2),Q(1,2),Q(80)),
                          (Q(64),Q(66),Q(68),Q(70)),'stipulated-lawful-grid')
    def test_complete_concrete_joint(self):
        x=self.joint();self.assertTrue(check_joint(x,evaluate_joint(x)))
    def test_changed_forecast_breaks_joint(self):
        x=self.joint();r=evaluate_joint(x);r['recognition_probability']=Q(1,3)
        self.assertFalse(check_joint(x,r))
    def test_both_probability_and_money_forged_break_joint(self):
        x=self.joint();r=evaluate_joint(x);r['recognition_probability']=Q(1,3)
        r['settlement']['claimant_expectation']=Q(260,3)
        self.assertFalse(check_joint(x,r))
    def test_unresolved_norm_cannot_issue_strategy(self):
        x=self.joint();p=DungProblem(('entitlement','attack'),frozenset({('attack','entitlement')}),'grounded')
        x=replace(x,normative=p);r=evaluate_joint(x)
        self.assertTrue(check_joint(x,r));r['settlement']={}
        self.assertFalse(check_joint(x,r))

if __name__=='__main__':unittest.main()
