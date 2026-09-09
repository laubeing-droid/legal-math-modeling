import unittest
from fractions import Fraction as Q
from unified.win_model import Hyper,fit,latent_rate_interval
from test_v2_contract_and_models import dataset,S
from unified.model_basis import ParameterBasis,ModelBasis,require_compatible_evidence_models
class IntervalTests(unittest.TestCase):
    def test_exact_latent_credible_interval(self):
        m=fit([r for r in dataset() if r.split=='train'])
        v=latent_rate_interval(m,'strong',steps=12)
        self.assertEqual(v['method'],'exact_beta_mixture_outward_bisection')
        self.assertLess(v['lo'],v['hi']);self.assertEqual(v['mass_at_least'],Q(19,20))
    def test_noninteger_shapes_fallback(self):
        m=fit([r for r in dataset() if r.split=='train'],(Hyper(Q(1,4),Q(2),Q(1)),))
        v=latent_rate_interval(m,'strong')
        self.assertEqual(v['method'],'posterior_chebyshev_outward_sqrt')
        self.assertLessEqual(v['lo'],m.predict('strong'));self.assertGreaterEqual(v['hi'],m.predict('strong'))
    def test_wider_mass_not_narrower_interval(self):
        m=fit([r for r in dataset() if r.split=='train'])
        a=latent_rate_interval(m,'strong',Q(1,10),10)
        b=latent_rate_interval(m,'strong',Q(1,20),10)
        self.assertLessEqual(b['lo'],a['lo']);self.assertGreaterEqual(b['hi'],a['hi'])
    def test_missing_parameter_provenance_rejected(self):
        with self.assertRaises(ValueError):ParameterBasis('prior','learned',(),'training cohort')
    def test_residual_hypothesis_record_required(self):
        p=ParameterBasis('prior','elicited',('review',),'scenario only')
        with self.assertRaises(ValueError):ModelBasis(S,('h1',),'lawyer',('h2',),'','reviewed',(p,),'evidence_analysis')
    def test_zero_likelihood_not_silently_removed(self):
        v=require_compatible_evidence_models({'a':Q(1,2),'b':Q(0)})
        self.assertFalse(v['robust_all_models_available']);self.assertEqual(v['incompatible'],('b',))
