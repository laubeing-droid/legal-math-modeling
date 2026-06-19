#!/usr/bin/env python3
"""
#95: Judgment Deviation Checker
==============================

Computes a composite deviation score for a single case judgment,
using three independent dimensions:

  D_bayes:  Bayesian posterior deviation from domain baseline
  D_mdl:    MDL reasoning path deviation from domain average
  D_aaf:    AAF structural deviation from expected accepted/rejected

D_total = w1*D_bayes + w2*D_mdl_norm + w3*D_aaf_norm

Mathematical proofs: see jc-math-model-playbook.md §28
"""

from __future__ import annotations

import json
import math
import os
import sys
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any, Dict, List, Optional, Set, Tuple

_PROJECT_ROOT = Path(__file__).resolve().parent.parent
if str(_PROJECT_ROOT) not in sys.path:
    sys.path.insert(0, str(_PROJECT_ROOT))

from theory.argumentation_horn_unification import (
    HornRule,
    HornToDungBridge,
)
from theory.bayesian_legal_reasoning import BayesianReasoning, EvidenceItem
from theory.kolmogorov_mdl_rules import RuleComplexity


# ============================================================
# Domain baselines
# ============================================================

@dataclass
class DomainBaseline:
    domain: str
    mean_mdl: float
    std_mdl: float
    prior: float  # base rate of positive_control
    expected_accepted: int
    expected_rejected: int


_DEFAULT_BASELINES = {
    "civil_commercial": DomainBaseline("civil_commercial", 15.66, 5.77, 0.72, 2, 0),
    "contract": DomainBaseline("contract", 15.66, 5.77, 0.72, 2, 0),
    "criminal": DomainBaseline("criminal", 16.68, 4.01, 0.80, 1, 0),
    "administrative": DomainBaseline("administrative", 14.28, 5.26, 0.65, 1, 0),
    "environment": DomainBaseline("environment", 13.45, 5.26, 0.60, 1, 0),
    "ip": DomainBaseline("ip", 15.48, 5.42, 0.70, 1, 0),
    "enforcement": DomainBaseline("enforcement", 17.03, 4.82, 0.75, 1, 0),
    "foreign": DomainBaseline("foreign", 14.32, 4.40, 0.60, 1, 0),
    "supervision": DomainBaseline("supervision", 16.42, 5.02, 0.70, 1, 0),
    "tort": DomainBaseline("tort", 11.99, 6.19, 0.65, 1, 0),
    "data": DomainBaseline("data", 10.94, 4.23, 0.60, 1, 0),
    "corporate": DomainBaseline("corporate", 12.71, 4.61, 0.65, 1, 0),
}


# ============================================================
# Deviation computation
# ============================================================

@dataclass
class DeviationResult:
    deviation_score: float
    bayesian_deviation: float
    mdl_deviation: float
    mdl_deviation_normalized: float
    aaf_deviation: int
    aaf_deviation_normalized: float
    domain: str
    baseline: Dict[str, Any]
    flags: List[str]
    rule_count: int
    fact_count: int


def compute_deviation(
    facts: Set[str],
    rules: List[HornRule],
    domain: str,
    baselines: Optional[Dict[str, DomainBaseline]] = None,
    weights: Tuple[float, float, float] = (0.4, 0.35, 0.25),
) -> DeviationResult:
    """Compute deviation score for a single case judgment.

    Args:
        facts: Set of established facts.
        rules: List of applicable rules.
        domain: Legal domain (e.g., 'contract', 'criminal').
        baselines: Domain baselines (defaults to Supreme Court data).
        weights: (w_bayes, w_mdl, w_aaf) weights.

    Returns:
        DeviationResult with composite and component scores.
    """
    if baselines is None:
        baselines = _DEFAULT_BASELINES

    baseline = baselines.get(domain, _DEFAULT_BASELINES.get("civil_commercial"))
    w1, w2, w3 = weights

    # 1. Bayesian posterior deviation
    prior = baseline.prior
    br = BayesianReasoning("deviation", prior=prior)
    for rule in rules:
        lr = 2.0 if len(rule.premises) <= 2 else 1.5
        ev = EvidenceItem(
            name=rule.id,
            description=f"rule with {len(rule.premises)} premises",
            p_if_claim_true=lr * 0.5,
            p_if_claim_false=0.5,
        )
        try:
            br.update(ev)
        except ZeroDivisionError:
            pass
    posterior = br.current_posterior
    D_bayes = abs(posterior - prior)

    # 2. MDL deviation
    mdl_total = 0.0
    for rule in rules:
        rc = RuleComplexity(
            rule_id=rule.id,
            premise_count=len(rule.premises),
            exception_chain_depth=len(rule.exceptions),
            concept_count=len(rule.concepts),
            total_concepts=max(1, len(rule.concepts)),
        )
        mdl_total += rc.minimum_description_length()
    mean_mdl = baseline.mean_mdl
    std_mdl = baseline.std_mdl
    D_mdl = mdl_total - mean_mdl
    D_mdl_norm = D_mdl / std_mdl if std_mdl > 0 else 0.0

    # 3. AAF structural deviation
    bridge = HornToDungBridge(rules, facts)
    frame = bridge.construct_frame()
    accepted = len(frame.args)
    expected_acc = baseline.expected_accepted
    D_aaf = abs(accepted - expected_acc)
    D_aaf_norm = D_aaf / (2 * len(rules)) if len(rules) > 0 else 0.0

    # 4. Composite
    D_total = w1 * D_bayes + w2 * abs(D_mdl_norm) + w3 * D_aaf_norm

    # 5. Flags
    flags = _compute_flags(D_bayes, D_mdl_norm, D_aaf, domain, std_mdl)

    return DeviationResult(
        deviation_score=round(D_total, 4),
        bayesian_deviation=round(D_bayes, 4),
        mdl_deviation=round(D_mdl, 2),
        mdl_deviation_normalized=round(D_mdl_norm, 4),
        aaf_deviation=D_aaf,
        aaf_deviation_normalized=round(D_aaf_norm, 4),
        domain=domain,
        baseline={
            "mean_mdl": mean_mdl,
            "std_mdl": std_mdl,
            "prior": prior,
            "expected_accepted": expected_acc,
        },
        flags=flags,
        rule_count=len(rules),
        fact_count=len(facts),
    )


def _compute_flags(
    D_bayes: float, D_mdl_norm: float, D_aaf: int,
    domain: str, std_mdl: float,
) -> List[str]:
    flags = []
    if D_bayes > 0.3:
        flags.append("posterior_significantly偏离基准")
    if D_mdl_norm > 2.0:
        flags.append("推理路径异常复杂")
    if D_mdl_norm < -2.0:
        flags.append("推理路径异常简单")
    if D_aaf > 0:
        flags.append("判决结果与期望不符")
    if D_bayes > 0.5 and D_mdl_norm > 2.0:
        flags.append("高偏离+高复杂度=需要人工复核")
    return flags


# ============================================================
# CLI entry point
# ============================================================

def _demo():
    """Demo with a standard contract breach case."""
    rules = [
        HornRule(
            id="r1",
            premises=["contract_signed", "performance_due", "non_performance"],
            head="BREACH_ESTABLISHED",
            exceptions=[],
            namespace="cn_civil",
        ),
        HornRule(
            id="r2",
            premises=["BREACH_ESTABLISHED", "breach_notice_sent"],
            head="LIABILITY_GRANTED",
            exceptions=[],
            namespace="cn_civil",
        ),
    ]
    facts = {"contract_signed", "performance_due", "non_performance", "breach_notice_sent"}

    result = compute_deviation(facts, rules, "contract")

    print("=" * 60)
    print("Judgment Deviation Checker — Demo")
    print("=" * 60)
    print(f"Domain:          {result.domain}")
    print(f"Rules:           {result.rule_count}")
    print(f"Facts:           {result.fact_count}")
    print(f"D_total:         {result.deviation_score}")
    print(f"D_bayes:         {result.bayesian_deviation}")
    print(f"D_mdl:           {result.mdl_deviation} (norm: {result.mdl_deviation_normalized})")
    print(f"D_aaf:           {result.aaf_deviation} (norm: {result.aaf_deviation_normalized})")
    print(f"Flags:           {result.flags if result.flags else 'None'}")
    print(f"Baseline:        {result.baseline}")
    print("=" * 60)

    # Anomalous case: very complex reasoning
    rules_complex = [
        HornRule(id=f"r{i}", premises=[f"p{i}", f"q{i}"], head=f"C{i}",
                 exceptions=[f"r{i+1}"] if i < 5 else [], namespace="cn_civil")
        for i in range(6)
    ]
    facts_complex = {f"p{i}" for i in range(6)} | {f"q{i}" for i in range(6)}
    result_complex = compute_deviation(facts_complex, rules_complex, "contract")

    print(f"\nAnomalous case (6 rules with exception chain):")
    print(f"D_total:         {result_complex.deviation_score}")
    print(f"Flags:           {result_complex.flags}")
    print("=" * 60)


if __name__ == "__main__":
    _demo()
