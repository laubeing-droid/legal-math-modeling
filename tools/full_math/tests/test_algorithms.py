import unittest,sys,itertools,random
from pathlib import Path
from fractions import Fraction as Q
sys.path.insert(0,str(Path(__file__).resolve().parents[1]))
from reference.extended_algorithms import *

class HornTests(unittest.TestCase):
 def setUp(self):self.atoms=frozenset('abc');self.rules=(HornRule('r1',frozenset('a'),'b'),HornRule('r2',frozenset('b'),'c'))
 def test_closure(self):self.assertEqual(horn_closure(self.atoms,frozenset('a'),self.rules),self.atoms)
 def test_unrooted_cycle(self):
  r=(HornRule('x',frozenset('a'),'b'),HornRule('y',frozenset('b'),'a'))
  self.assertEqual(horn_supports(self.atoms,frozenset(),frozenset(),r)['a'],frozenset())
 def test_rooted_cycle(self):
  r=(HornRule('x',frozenset('a'),'b'),HornRule('y',frozenset('b'),'a'))
  self.assertEqual(horn_supports(self.atoms,frozenset(),frozenset('a'),r)['b'],frozenset({frozenset('a')}))
 def test_empty_rule(self):
  r=(HornRule('x',frozenset(),'c'),)
  self.assertEqual(horn_supports(self.atoms,frozenset(),frozenset(),r)['c'],frozenset({frozenset()}))
 def test_alternative_support(self):
  r=(HornRule('x',frozenset('a'),'c'),HornRule('y',frozenset('b'),'c'))
  labels=horn_supports(self.atoms,frozenset(),frozenset('ab'),r)['c']
  self.assertTrue(verify_supports(self.atoms,frozenset(),frozenset('ab'),r,'c',labels))
  self.assertEqual(labels,frozenset({frozenset('a'),frozenset('b')}))
 def test_missing_support_rejected(self):
  r=(HornRule('x',frozenset('a'),'c'),HornRule('y',frozenset('b'),'c'))
  self.assertFalse(verify_supports(self.atoms,frozenset(),frozenset('ab'),r,'c',[frozenset('a')]))
 def test_absorption(self):self.assertEqual(antichain_minimal([{'a'},{'a','b'},{'a'}]),frozenset({frozenset('a')}))
 def test_full_oracle_random_finite(self):
  rng=random.Random(1)
  for _ in range(30):
   r=tuple(HornRule(str(i),frozenset(x for x in 'abc' if rng.randrange(2)),rng.choice('abc')) for i in range(3))
   labels=horn_supports(self.atoms,frozenset(),frozenset('ab'),r)
   for a in 'abc':self.assertTrue(verify_supports(self.atoms,frozenset(),frozenset('ab'),r,a,labels[a]))
 def test_bad_carrier(self):
  with self.assertRaises(ModelError):horn_closure(frozenset('ab'),frozenset('a'),self.rules)
 def test_same_rule_id(self):
  with self.assertRaises(ModelError):horn_closure(self.atoms,frozenset(),(self.rules[0],self.rules[0]))
 def test_shared_event_not_independent(self):
  joint={w:Q(1,8) for w in powerset('xyz')}
  p=event_probability([frozenset('xy'),frozenset('xz')],joint)
  self.assertEqual(p,Q(3,8));self.assertNotEqual(p,1-(1-Q(1,4))**2)
 def test_duplicate_support_no_increment(self):
  joint={frozenset():Q(1,2),frozenset('x'):Q(1,2)}
  self.assertEqual(event_probability([frozenset('x')]*2,joint),Q(1,2))
 def test_bad_pmf(self):
  with self.assertRaises(ModelError):event_probability([frozenset('x')],{frozenset('x'):Q(2)})

class ReductionTests(unittest.TestCase):
 def test_common_variable(self):
  old=RelationBox(frozenset({(0,1),(1,0)}),(frozenset({0,1}),frozenset({0,1})))
  self.assertTrue(verify_reduction(old,old.reduce()));self.assertEqual({sum(w) for w in old.denotation()},{1})
 def test_tighten(self):
  old=RelationBox(frozenset({(0,1),(1,0)}),(frozenset({1}),frozenset({0,1})))
  self.assertEqual(old.reduce().components[1],frozenset({0}));self.assertTrue(verify_reduction(old,old.reduce()))
 def test_gamma_change_not_reduction(self):
  x=RelationBox(frozenset({(0,1),(1,0)}),(frozenset({0,1}),frozenset({0,1})))
  y=RelationBox(frozenset({(1,0)}),x.components);self.assertFalse(verify_reduction(x,y))
 def test_impossible_relation(self):
  x=RelationBox(frozenset({(0,1)}),(frozenset({1}),frozenset({1})));self.assertEqual(x.reduce().denotation(),frozenset())
 def test_dimension(self):
  with self.assertRaises(ModelError):RelationBox(frozenset({(0,1)}),(frozenset({0}),)).denotation()

class StatisticsTests(unittest.TestCase):
 def test_infinity_quantile(self):self.assertIsNone(conformal_cutoff([1,2,3],Q(1,100)))
 def test_empty_calibration_infinity(self):self.assertIsNone(conformal_cutoff([],Q(1,10)))
 def test_quantile(self):self.assertEqual(conformal_cutoff([1,2,3],Q(1,4)),Q(3))
 def test_ties_conservative(self):self.assertEqual(conformal_set([1,1,1],Q(1,4),{'x':1,'y':2}),frozenset({'x'}))
 def test_exchangeable_rank_enumeration(self):
  perms=list(itertools.permutations(range(4)));covered=0
  for xs in perms:
   q=conformal_cutoff(xs[:-1],Q(1,4));covered+=q is None or xs[-1]<=q
  self.assertEqual(Q(covered,len(perms)),Q(3,4))
 def test_union_not_product(self):self.assertEqual(union_coverage_lower([Q(1,10)]*2),Q(4,5))
 def test_union_clamped(self):self.assertEqual(union_coverage_lower([Q(4,5)]*2),0)
 def test_invalid_alpha(self):
  with self.assertRaises(ModelError):conformal_cutoff([1],Q(0))
 def test_bets_exact(self):self.assertEqual(betting_path([0,1],Q(1,2),[1,1]),(Q(1),Q(1,2),Q(3,4)))
 def test_invalid_bets(self):
  with self.assertRaises(ModelError):betting_path([1],Q(1,2),[3])
 def test_pav_basic(self):self.assertEqual(pav([3,1,2],[1,1,1]),(Q(2),Q(2),Q(2)))
 def test_pav_weighted(self):self.assertEqual(pav([3,1],[1,3]),(Q(3,2),Q(3,2)))
 def test_pav_already_sorted(self):self.assertEqual(pav([1,2,3],[1,2,3]),(Q(1),Q(2),Q(3)))
 def test_pav_kkt(self):
  for y in itertools.product(range(3),repeat=4):
   for w in [(1,1,1,1),(1,2,3,4)]:self.assertTrue(verify_pav(y,w,pav(y,w)))
 def test_wrong_monotone_not_optimal(self):self.assertFalse(verify_pav([1,2],[1,1],[10,11]))
 def test_pav_wrong_weights(self):
  with self.assertRaises(ModelError):pav([1,2],[1,0])
 def test_no_float(self):
  with self.assertRaises(ModelError):exact(0.5)

class DecisionTests(unittest.TestCase):
 def model(self):return FiniteMDP(('a','b'),{'a':('wait','jump'),'b':('stay',)},
  {('a','wait'):(('a',Q(1)),),('a','jump'):(('b',Q(1)),),('b','stay'):(('b',Q(1)),)},
  {('a','wait'):Q(1),('a','jump'):Q(0),('b','stay'):Q(5)}, {'a':Q(0),'b':Q(0)})
 def test_backward_induction(self):
  v,pi=finite_horizon(self.model(),2);self.assertEqual(v[-1]['a'],5);self.assertEqual(pi[-1]['a'],'jump')
 def test_bellman_independent_check(self):
  v,pi=finite_horizon(self.model(),3);self.assertTrue(verify_bellman(self.model(),v,pi))
 def test_bad_value_rejected(self):
  v,pi=finite_horizon(self.model(),2);v[2]['a']=9;self.assertFalse(verify_bellman(self.model(),v,pi))
 def test_bad_action_rejected(self):
  v,pi=finite_horizon(self.model(),2);pi[0]['a']='illegal';self.assertFalse(verify_bellman(self.model(),v,pi))
 def test_empty_action_rejected(self):
  m=self.model();m.actions['a']=()
  with self.assertRaises(ModelError):finite_horizon(m,1)
 def test_zero_horizon(self):self.assertTrue(verify_bellman(self.model(),*finite_horizon(self.model(),0)))
 def test_shared_parameter(self):
  val,pol=persistent_model_value({'fixed':{'t0':1,'t1':1}},['t0','t1']);self.assertEqual(val,1)
  self.assertNotEqual(val,min(0,1)+min(1,0))
 def test_missing_model(self):
  with self.assertRaises(ModelError):persistent_model_value({'p':{'t0':1}},['t0','t1'])
 def test_regret(self):
  acts=[(0,1),(0,1)];pay={x:(int(x[0]==x[1]),int(x[0]==x[1])) for x in itertools.product(*acts)}
  self.assertEqual(finite_regret(pay,(0,0),acts),(0,0));self.assertEqual(finite_regret(pay,(0,1),acts),(1,1))
 def test_dsic_vickrey(self):
  ty=[(0,1,2),(0,1,2)];ps=list(itertools.product(*ty));u={}
  for th,r in itertools.product(ps,ps):
   win=0 if r[0]>=r[1] else 1;v=[0,0];v[win]=th[win]-r[1-win];u[th,r]=tuple(v)
  self.assertTrue(verify_dsic(ty,u))
 def test_dsic_missing_reports(self):
  with self.assertRaises(ModelError):verify_dsic([(0,1)],{})

class CausalTests(unittest.TestCase):
 def models(self):return (BinarySCM('causal',(Q(1,2),Q(1,2)),(False,True),((False,True),(False,True))),BinarySCM('confounded',(Q(1,2),Q(1,2)),(False,True),((False,False),(True,True))))
 def test_observational_equivalence(self):a,b=self.models();self.assertEqual(a.observations(),b.observations())
 def test_interventions_differ(self):a,b=self.models();self.assertEqual(a.ate(),1);self.assertEqual(b.ate(),0)
 def test_identified_set(self):m=self.models();r=identify_finite(m,m[0].observations());self.assertEqual(r['values'],frozenset({Q(0),Q(1)}));self.assertEqual(r['status'],'EXACT_FINITE_MODEL_CLASS')
 def test_empty_is_incompatible(self):m=self.models();self.assertEqual(identify_finite([],m[0].observations())['status'],'INCOMPATIBLE_DECLARED_MODEL_CLASS')
 def test_bad_model_identity_rejected(self):
  m=self.models()
  with self.assertRaises(ModelError):identify_finite([m[0],m[0]],m[0].observations())
if __name__=='__main__':unittest.main()
