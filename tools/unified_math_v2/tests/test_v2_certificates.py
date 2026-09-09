import unittest
from fractions import Fraction as Q
from dataclasses import replace
from unified.precision import verify_min_lp_optimum,verify_ldl_psd
from unified.win_model import validate_splits,fit
from test_v2_contract_and_models import dataset
class ConvexCertificates(unittest.TestCase):
    def test_minimum_lp_certificate(self):
        self.assertEqual(verify_min_lp_optimum(((Q(1),),),(Q(2),),(Q(1),),(Q(2),),(Q(1),)),())
    def test_wrong_dual_cannot_certify_optimality(self):
        self.assertTrue(verify_min_lp_optimum(((Q(1),),),(Q(2),),(Q(1),),(Q(3),),(Q(1),)))
    def test_psd_matrix_certificate(self):
        self.assertTrue(verify_ldl_psd(((Q(2),Q(2)),(Q(2),Q(5))),((Q(1),Q(0)),(Q(1),Q(1))),(Q(2),Q(3))))
    def test_indefinite_matrix_rejected(self):
        self.assertFalse(verify_ldl_psd(((Q(1),Q(0)),(Q(0),Q(-1))),((Q(1),Q(0)),(Q(0),Q(1))),(Q(1),Q(-1))))
    def test_forged_psd_witness_rejected(self):
        self.assertFalse(verify_ldl_psd(((Q(1),Q(2)),(Q(0),Q(1))),((Q(1),Q(0)),(Q(0),Q(1))),(Q(1),Q(1))))
    def test_duplicate_cluster_within_train_rejected(self):
        rows=dataset();rows[1]=replace(rows[1],cluster=rows[0].cluster)
        with self.assertRaises(ValueError):validate_splits(rows)
        with self.assertRaises(ValueError):fit(rows[:8])
