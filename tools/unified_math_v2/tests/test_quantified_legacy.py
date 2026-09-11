import random
import unittest
from fractions import Fraction as Q
from itertools import product

from reference.core import (
    Assessment, BayesNet, Establishment as E, IncompatibleEvidence, Interval,
    ModelError, Node, Observation, PMF, QueryResult, burden_result, condition,
    dirichlet_predictive, exact_grid_range, expected_brier, fit_strength_grid,
    incentive_gap, information_value, mixture_query, nash_bargain, nash_regrets,
    normalize, payment_claim, rational, scenario_event_bounds, settlement_bounds,
    unfinished_posterior_bounds, verify_lp_optimum, verify_mechanism,
)


def payment_bn(sensitivity=Q(4, 5), false_positive=Q(1, 5)):
    return BayesNet("synthetic-payment", (
        Node("paid", ("no", "yes"), (), {(): (Q(1, 2), Q(1, 2))}),
        Node("record", ("absent", "present"), ("paid",), {
            ("no",): (1-false_positive, false_positive),
            ("yes",): (1-sensitivity, sensitivity),
        }),
    ))


class ProbabilityTests(unittest.TestCase):
    def test_exact_input_only(self):
        self.assertEqual(rational("0.1"), Q(1, 10))
        for x in (True, 0.1, "1/0"):
            with self.assertRaises(ModelError):
                rational(x)

    def test_pmf_rejects_wrong_sum_and_negative(self):
        for mass in ({}, {"a": Q(2)}, {"a": Q(-1), "b": Q(2)}, {"a": Q(1, 2)}):
            with self.assertRaises(ModelError):
                PMF(mass)

    def test_bayes_known_answer(self):
        p, z = condition(PMF({"paid": Q(1,2), "unpaid": Q(1,2)}),
                         {"paid": Q(4,5), "unpaid": Q(1,5)})
        self.assertEqual(p.mass["paid"], Q(4,5))
        self.assertEqual(z, Q(1,2))
        self.assertEqual(sum(p.mass.values()), 1)

    def test_zero_evidence_not_zero_probability(self):
        with self.assertRaises(IncompatibleEvidence):
            condition(PMF({"a": Q(1)}), {"a": Q(0)})

    def test_zero_prior_stays_zero(self):
        result, _ = condition(PMF({"a": Q(0), "b": Q(1)}), {"a": Q(1), "b": Q(1)})
        self.assertEqual(result.mass["a"], 0)

    def test_sequential_update(self):
        prior = PMF({0: Q(2,5), 1: Q(3,5)})
        first, second = {0: Q(2,3), 1: Q(1,4)}, {0: Q(1,7), 1: Q(3,4)}
        sequential = condition(condition(prior, first)[0], second)[0]
        combined = condition(prior, {k: first[k]*second[k] for k in first})[0]
        self.assertEqual(dict(sequential.mass), dict(combined.mass))

    def test_bn_enumeration_and_elimination(self):
        bn = payment_bn()
        evidence = (Observation("bank-record-1", "record", "present"),)
        enum, ve = bn.enumerate_query("paid", evidence), bn.eliminate_query("paid", evidence)
        self.assertEqual(enum, ve)
        self.assertEqual(enum.distribution.mass["yes"], Q(4,5))

    def test_bn_normalized_without_evidence(self):
        result = payment_bn().eliminate_query("paid")
        self.assertEqual(result.evidence_mass, 1)
        self.assertEqual(result.distribution.mass["yes"], Q(1,2))

    def test_query_itself_observed(self):
        result = payment_bn().eliminate_query("paid", (Observation("p1", "paid", "yes"),))
        self.assertEqual(result.distribution.mass["yes"], 1)
        self.assertEqual(result.evidence_mass, Q(1,2))

    def test_duplicate_observation_idempotent(self):
        bn = payment_bn()
        e = Observation("original-document", "record", "present")
        self.assertEqual(bn.eliminate_query("paid", (e,)), bn.eliminate_query("paid", (e,e,e)))

    def test_observation_id_collision(self):
        with self.assertRaises(ModelError):
            payment_bn().eliminate_query("paid", (
                Observation("same", "record", "present"), Observation("same", "record", "absent")))

    def test_invalid_network(self):
        with self.assertRaises(ModelError):
            payment_bn(Q(2), Q(1,5))
        with self.assertRaises(ModelError):
            BayesNet("missing", (Node("A", ("0","1"), ("B",), {}),))
        with self.assertRaises(ModelError):
            BayesNet("missing-row", (
                Node("A", ("0","1"), (), {(): (Q(1,2), Q(1,2))}),
                Node("B", ("0","1"), ("A",), {("0",): (Q(1,2), Q(1,2))}),
            ))

    def test_random_finite_network_differential(self):
        rng = random.Random(20260909)
        for trial in range(120):
            nodes = []
            for i in range(4):
                parents = tuple(f"x{j}" for j in range(i) if rng.random() < 0.5)
                rows = {}
                for key in product(("0", "1"), repeat=len(parents)):
                    p = Q(rng.randrange(1, 10), 10)
                    rows[key] = (1-p, p)
                nodes.append(Node(f"x{i}", ("0", "1"), parents, rows))
            bn = BayesNet(f"test-{trial}", nodes)
            observations = tuple(Observation(f"obs-{i}", f"x{i}", str(rng.randrange(2)))
                                 for i in range(4) if rng.random() < 0.4)
            with self.subTest(trial=trial):
                self.assertEqual(bn.enumerate_query("x0", observations), bn.eliminate_query("x0", observations))

    def test_dependent_evidence_cannot_be_naively_multiplied(self):
        single = condition(PMF({0: Q(1,2), 1: Q(1,2)}), {0: Q(1,5), 1: Q(4,5)})[0]
        falsely_repeated = condition(single, {0: Q(1,5), 1: Q(4,5)})[0]
        self.assertEqual(single.mass[1], Q(4,5))
        self.assertEqual(falsely_repeated.mass[1], Q(16,17))
        self.assertNotEqual(single.mass[1], falsely_repeated.mass[1])

    def test_dirichlet_actually_uses_data(self):
        prior = (Q(1), Q(1))
        self.assertEqual(dirichlet_predictive(prior, (0,0)), (Q(1,2),Q(1,2)))
        self.assertEqual(dirichlet_predictive(prior, (3,1)), (Q(2,3),Q(1,3)))
        self.assertNotEqual(dirichlet_predictive(prior, (1,3)), dirichlet_predictive(prior, (3,1)))

    def test_dirichlet_invalid_counts(self):
        for counts in ((True,1), (-1,2), (1,)):
            with self.assertRaises(ModelError):
                dirichlet_predictive((Q(1),Q(1)), counts)

    def test_hierarchical_grid_posterior_uses_observations(self):
        prior = PMF({Q(1):Q(1,2), Q(10):Q(1,2)})
        no_data = fit_strength_grid((Q(1,2),Q(1,2)), ((0,0),), prior)
        data = fit_strength_grid((Q(1,2),Q(1,2)), ((10,0),(0,10)), prior)
        self.assertEqual(dict(no_data.mass), dict(prior.mass))
        self.assertNotEqual(dict(data.mass), dict(prior.mass))
        self.assertGreater(data.mass[Q(1)], data.mass[Q(10)])

    def test_mixture_reweights_with_evidence(self):
        results = {
            "a": QueryResult(PMF({0:Q(0),1:Q(1)}), Q(9,10), "a"),
            "b": QueryResult(PMF({0:Q(1),1:Q(0)}), Q(1,10), "b"),
        }
        result = mixture_query(results, PMF({"a":Q(1,2),"b":Q(1,2)}))
        self.assertEqual(result.distribution.mass[1], Q(9,10))
        self.assertNotEqual(result.distribution.mass[1], Q(1,2))

    def test_scenario_bounds_not_uniform_branch_probability(self):
        bounds = scenario_event_bounds(PMF({"x":Q(1)}), {"x":frozenset({"win","lose"})}, lambda y:y=="win")
        self.assertEqual(bounds, (Q(0),Q(1)))
        with self.assertRaises(ModelError):
            scenario_event_bounds(PMF({"x":Q(1)}), {"x":frozenset()}, lambda y:True)

    def test_partial_enumeration_enclosure(self):
        a,b,r = Q(1,5),Q(1,10),Q(7,10)
        lo,hi = unfinished_posterior_bounds(a,b,r)
        for i in range(11):
            for j in range(11-i):
                u,v = r*Q(i,10),r*Q(j,10)
                value = (a+u)/(a+b+u+v)
                self.assertLessEqual(lo,value)
                self.assertLessEqual(value,hi)


class BurdenTests(unittest.TestCase):
    def assessment(self, state, complete=True, request="r1"):
        return Assessment(request,state,complete,"synthetic-reviewed-assessment")

    def test_undetermined_after_complete_assessment(self):
        a=self.assessment(E.UNDETERMINED)
        self.assertEqual(burden_result(a,stage_closed=True,authority_valid=True),"burden_failure")
        self.assertEqual(a.state,E.UNDETERMINED)  # Never becomes factual false.

    def test_incomplete_software_or_stage_never_burden_failure(self):
        a=self.assessment(E.UNDETERMINED,False)
        self.assertEqual(burden_result(a,stage_closed=True,authority_valid=True),"pending")
        self.assertEqual(burden_result(self.assessment(E.UNDETERMINED),stage_closed=False,authority_valid=True),"pending")

    def args(self):
        return dict(request_id="r1",relation=self.assessment(E.ESTABLISHED),maturity=self.assessment(E.ESTABLISHED),
                    payment=self.assessment(E.NOT_ESTABLISHED),stage_closed=True,authority_valid=True,
                    other_defence_applies=False,value=Q(100),established_payment_amount=Q(80))

    def test_payment_defence_and_relation_have_different_burdens(self):
        args=self.args()
        self.assertEqual(payment_claim(**args)["principal"],100)
        args["relation"]=self.assessment(E.NOT_ESTABLISHED)
        self.assertEqual(payment_claim(**args)["kind"],"claim_basis_not_established")

    def test_proven_partial_payment(self):
        args=self.args(); args["payment"]=self.assessment(E.ESTABLISHED)
        self.assertEqual(payment_claim(**args)["principal"],20)

    def test_overpayment_not_erased(self):
        args=self.args(); args.update(payment=self.assessment(E.ESTABLISHED),established_payment_amount=Q(120))
        result=payment_claim(**args)
        self.assertEqual((result["principal"],result["overpayment"]),(0,20))

    def test_no_probability_argument(self):
        args=self.args(); before=payment_claim(**args)
        for p in (Q(0),Q(1,2),Q(99,100),Q(1)):
            decorated={"normative":before,"probability":p}
            self.assertEqual(decorated["normative"],payment_claim(**args))
        with self.assertRaises(TypeError):
            payment_claim(**args,probability=Q(99,100))

    def test_scope_and_unknown_defence(self):
        args=self.args(); args["payment"]=self.assessment(E.ESTABLISHED,request="other")
        with self.assertRaises(ModelError): payment_claim(**args)
        args=self.args(); args["other_defence_applies"]=None
        self.assertEqual(payment_claim(**args)["kind"],"pending")


class NumericTests(unittest.TestCase):
    def test_interval_signs_and_division(self):
        a=Interval(Q(1),Q(3))
        self.assertEqual(a.scale(Q(-2)),Interval(Q(-6),Q(-2)))
        self.assertEqual(a.multiply(Interval(Q(-2),Q(4))),Interval(Q(-6),Q(12)))
        self.assertEqual(a.divide(Interval(Q(-4),Q(-2))),Interval(Q(-3,2),Q(-1,4)))
        with self.assertRaises(ModelError): a.divide(Interval(Q(-1),Q(1)))

    def test_interval_dependency_only_enclosure(self):
        a=Interval(Q(1),Q(3))
        self.assertEqual(a.subtract(a),Interval(Q(-2),Q(2)))
        self.assertNotEqual(a.subtract(a),Interval(Q(0),Q(0)))

    def test_exact_grid_preserves_gaps_and_endpoint_witness(self):
        result=exact_grid_range({"a":Q(0),"b":Q(5),"c":Q(10)},lambda k:k!="b")
        self.assertEqual(result["values"],(Q(0),Q(10)))
        self.assertEqual(result["lo_witnesses"],("a",))
        self.assertNotIn(Q(5),result["values"])

    def test_lp_certificate_and_tampering(self):
        self.assertEqual(verify_lp_optimum([[Q(1)]],[Q(3)],[Q(2)],[Q(3)],[Q(2)]),())
        self.assertIn("PRIMAL_INFEASIBLE",verify_lp_optimum([[Q(1)]],[Q(3)],[Q(2)],[Q(4)],[Q(2)]))
        self.assertIn("DUAL_INFEASIBLE",verify_lp_optimum([[Q(1)]],[Q(3)],[Q(2)],[Q(3)],[Q(1)]))


class StrategyTests(unittest.TestCase):
    def test_information_value_and_cost(self):
        joint=PMF({("good","signal-good"):Q(1,2),("bad","signal-bad"):Q(1,2)})
        utilities={"act":{"good":Q(10),"bad":Q(-10)},"stay":{"good":Q(0),"bad":Q(0)}}
        result=information_value(joint,utilities,Q(6))
        self.assertEqual((result["before"],result["after"],result["net_voi"]),(0,5,-1))

    def test_uninformative_evidence_has_zero_gross_value(self):
        joint=PMF({(y,z):Q(1,4) for y in (0,1) for z in (0,1)})
        result=information_value(joint,{"a":{0:Q(10),1:Q(-10)},"b":{0:Q(0),1:Q(0)}})
        self.assertEqual(result["gross_voi"],0)

    def test_settlement_different_beliefs_and_costs(self):
        result=settlement_bounds(Q(80),Q(70),Q(10),Q(15),Q(2),Q(3))
        self.assertEqual((result["lo"],result["hi"]),(72,82))
        self.assertEqual(nash_bargain(result["interval"],Q(1,2)),77)
        self.assertFalse(settlement_bounds(Q(100),Q(20),Q(1),Q(1))["feasible"])

    def test_incentive_limit(self):
        self.assertLess(incentive_gap(Q(10),Q(1,2),Q(12)),0)
        self.assertEqual(incentive_gap(Q(10),Q(1,2),Q(20)),0)

    def test_mixed_equilibrium_not_pure(self):
        u1=[[Q(1),Q(-1)],[Q(-1),Q(1)]]; u2=[[-x for x in row] for row in u1]
        self.assertEqual(nash_regrets(u1,u2,[Q(1,2)]*2,[Q(1,2)]*2),(0,0))
        self.assertGreater(max(nash_regrets(u1,u2,[Q(1),Q(0)],[Q(1),Q(0)])),0)

    def mechanism(self, price=Q(3)):
        t1,t2=("low","high"),("low","high")
        values,costs={"low":Q(2),"high":Q(4)},{"low":Q(1),"high":Q(5)}
        allocation={}
        for a,b in product(t1,t2):
            trade = values[a] >= price and costs[b] <= price
            allocation[a,b]=PMF({"trade":Q(int(trade)),"none":Q(int(not trade))})
        return dict(types1=t1,types2=t2,outcomes=("trade","none"),
                    prior=PMF({pair:Q(1,4) for pair in product(t1,t2)}),allocation=allocation,
                    utility1=lambda o,a,b:values[a]-price if o=="trade" else Q(0),
                    utility2=lambda o,a,b:price-costs[b] if o=="trade" else Q(0),
                    outside1={a:Q(0) for a in t1},outside2={b:Q(0) for b in t2},
                    legal_outcomes=frozenset({"trade","none"}),net_transfer={"trade":Q(0),"none":Q(0)})

    def test_posted_price_bic_ir_budget(self):
        report=verify_mechanism(**self.mechanism())
        self.assertTrue(report["accepted_on_declared_scope"])
        self.assertEqual(report["zero_prior_types_without_bic_guarantee"],())

    def test_profitable_misreport_detected(self):
        args=self.mechanism()
        args["allocation"][("low","low")]=PMF({"trade":Q(1),"none":Q(0)})
        args["allocation"][("high","low")]=PMF({"trade":Q(0),"none":Q(1)})
        report=verify_mechanism(**args)
        self.assertTrue(any(v["code"]=="BIC_1" for v in report["violations"]))

    def test_budget_and_legality_checked(self):
        args=self.mechanism(); args["net_transfer"]["trade"]=Q(1)
        self.assertTrue(any(v["code"]=="NOT_EX_POST_BALANCED" for v in verify_mechanism(**args)["violations"]))
        args=self.mechanism(); args["legal_outcomes"]=frozenset({"none"})
        self.assertTrue(any(v["code"]=="ILLEGAL_OUTCOME" for v in verify_mechanism(**args)["violations"]))

    def test_brier_proper_identity(self):
        for i,j in product(range(11),repeat=2):
            p,q=Q(i,10),Q(j,10)
            self.assertEqual(expected_brier(p,q)-expected_brier(p,p),(q-p)**2)


if __name__ == "__main__":
    unittest.main(verbosity=2)
