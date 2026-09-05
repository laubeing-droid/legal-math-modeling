#!/usr/bin/env python3
"""
#95: Bayesian Confidence Calibration — Full Implementation
===========================================================

Loads structured claims, proof results, and AAF stability data to build
a proxy calibration model for juris-calculus confidence outputs.

Data sources:
  - data/cn_legal/*_claims.json (180 structured claims, 6 domains × 30)
  - proofs/engineering_proof_artifacts/proof_run_results.json (17 proof outcomes)
  - data/aaf_legal/aaf_validation_summary.json (18 AAF stability patterns)

Evidence level: PROXY_CALIBRATION — these are structured internal labels,
NOT real judicial outcome calibration.

NOTE (Codex audit): 180 claims are structured claim/control samples with
verification_status=VERIFIED. They are NOT real court outcomes. Conclusions
must be written as "internal label calibration" or "proxy calibration".
"""

from __future__ import annotations

import csv
import json
import math
import os
import sys
import time
from collections import Counter, defaultdict
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any, Dict, List, Optional, Tuple

import numpy as np

_PROJECT_ROOT = Path(__file__).resolve().parent.parent
if str(_PROJECT_ROOT) not in sys.path:
    sys.path.insert(0, str(_PROJECT_ROOT))

from theory.bayesian_legal_reasoning import (
    BayesianReasoning,
    BayesianUpdateRecord,
    EvidenceItem,
)


# ============================================================
# Data structures
# ============================================================

@dataclass
class StructuredClaim:
    claim_id: str
    jurisdiction: str
    domain: str
    fact_summary: str
    legal_question: str
    cn_claim: str
    claim_type: str
    legal_basis: str
    case_basis: str
    hard_case: bool
    hard_case_reason: str
    positive_control: bool
    primary_claim: str
    confidence_expected: str
    verification_status: str
    notes: str


@dataclass
class ProofOutcome:
    artifact_id: str
    name: str
    status: str  # PROVED / REFUTED / PENDING_TOOLCHAIN
    trust_label: str
    runtime_seconds: float
    checker_type: str
    is_correct: bool  # PROVED=True, REFUTED=False, PENDING=None


@dataclass
class AAFStabilityPattern:
    pattern_index: int
    dung_modelable: bool
    stability_comparison: str  # "Dung more stable", "equivalent", etc.
    conclusion: str


@dataclass
class CalibrationResult:
    domain: str
    n_total: int
    n_positive: int
    n_hard: int
    prior: float
    posterior: float
    lr_hard: float
    lr_easy: float
    bayesian_updates: List[Dict]
    credible_interval: Optional[Tuple[float, float]]


# ============================================================
# Data loading
# ============================================================

def load_claims(data_dir: Path) -> List[StructuredClaim]:
    """Load all *_claims.json files from data/cn_legal/."""
    claims = []
    cn_legal = data_dir / 'cn_legal'
    for fname in sorted(os.listdir(cn_legal)):
        if not fname.endswith('_claims.json'):
            continue
        domain = fname.replace('_claims.json', '')
        with open(cn_legal / fname, encoding='utf-8') as f:
            d = json.load(f)
        for c in d.get('claims', []):
            engine_out = c.get('expected_engine_output', {})
            claims.append(StructuredClaim(
                claim_id=c.get('claim_id', ''),
                jurisdiction=c.get('jurisdiction', 'CN'),
                domain=c.get('domain', domain),
                fact_summary=c.get('fact_summary', ''),
                legal_question=c.get('legal_question', ''),
                cn_claim=c.get('cn_claim', ''),
                claim_type=c.get('claim_type', ''),
                legal_basis=json.dumps(c.get('legal_basis', []), ensure_ascii=False)[:200],
                case_basis=json.dumps(c.get('case_basis', []), ensure_ascii=False)[:200],
                hard_case=c.get('hard_case', False),
                hard_case_reason=c.get('hard_case_reason', ''),
                positive_control=c.get('positive_control', False),
                primary_claim=engine_out.get('primary_claim', ''),
                confidence_expected=engine_out.get('confidence_expected', ''),
                verification_status=c.get('verification_status', ''),
                notes=c.get('notes', ''),
            ))
    return claims


def load_proof_outcomes(proof_path: Path) -> List[ProofOutcome]:
    """Load proof_run_results.json."""
    with open(proof_path, encoding='utf-8') as f:
        d = json.load(f)
    outcomes = []
    for r in d.get('results', []):
        is_correct = None
        if r['status'] == 'PROVED':
            is_correct = True
        elif r['status'] == 'REFUTED':
            is_correct = False
        outcomes.append(ProofOutcome(
            artifact_id=r.get('artifact_id', ''),
            name=r.get('name', ''),
            status=r['status'],
            trust_label=r.get('trust_label', ''),
            runtime_seconds=r.get('runtime_seconds', 0),
            checker_type=r.get('checker_type', ''),
            is_correct=is_correct,
        ))
    return outcomes


def load_aaf_stability(data_dir: Path) -> Dict[str, Any]:
    """Load aaf_validation_summary.json."""
    with open(data_dir / 'aaf_legal' / 'aaf_validation_summary.json', encoding='utf-8') as f:
        return json.load(f)


# ============================================================
# Bayesian calibration engine
# ============================================================

def calibrate_domain(claims: List[StructuredClaim], domain: str) -> CalibrationResult:
    """Calibrate confidence for a single domain using Bayesian updating."""
    domain_claims = [c for c in claims if c.domain == domain]
    n_total = len(domain_claims)
    if n_total == 0:
        return CalibrationResult(domain=domain, n_total=0, n_positive=0,
                                 n_hard=0, prior=0, posterior=0, lr_hard=1,
                                 lr_easy=1, bayesian_updates=[], credible_interval=None)

    n_positive = sum(1 for c in domain_claims if c.positive_control)
    n_hard = sum(1 for c in domain_claims if c.hard_case)

    # Prior: base rate of positive_control in this domain
    prior = n_positive / n_total

    # Likelihood ratios derived from hard_case status
    # Hard cases should have lower LR (more likely to be edge cases)
    # Easy cases should have higher LR
    n_hard_positive = sum(1 for c in domain_claims if c.hard_case and c.positive_control)
    n_hard_negative = sum(1 for c in domain_claims if c.hard_case and not c.positive_control)
    n_easy_positive = sum(1 for c in domain_claims if not c.hard_case and c.positive_control)
    n_easy_negative = sum(1 for c in domain_claims if not c.hard_case and not c.positive_control)

    # Empirical likelihood ratios with Laplace smoothing
    n_easy = n_total - n_hard
    lr_hard = ((n_hard_positive + 1) / (n_hard + 2)) / ((n_hard_negative + 1) / (n_hard + 2)) if n_hard > 0 else 1.0
    lr_easy = ((n_easy_positive + 1) / (n_easy + 2)) / ((n_easy_negative + 1) / (n_easy + 2)) if n_easy > 0 else 1.0

    # Bayesian updating: iterate through claims
    br = BayesianReasoning(f'calibration_{domain}', prior=prior)
    updates = []
    for c in domain_claims:
        lr = lr_hard if c.hard_case else lr_easy
        ev = EvidenceItem(
            name=c.claim_id,
            description=f'{c.claim_type}: {c.fact_summary[:80]}',
            p_if_claim_true=lr * 0.5,  # Scale to probability
            p_if_claim_false=0.5,       # Neutral base
        )
        try:
            rec = br.update(ev)
            updates.append({
                'claim_id': c.claim_id,
                'hard_case': c.hard_case,
                'positive_control': c.positive_control,
                'lr': lr,
                'prior': rec.prior,
                'posterior': rec.posterior,
            })
        except ZeroDivisionError:
            pass

    posterior = br.current_posterior

    # Bootstrap credible interval
    ci = _bootstrap_posterior(domain_claims, prior, lr_hard, lr_easy, n_boot=5000)

    return CalibrationResult(
        domain=domain,
        n_total=n_total,
        n_positive=n_positive,
        n_hard=n_hard,
        prior=prior,
        posterior=posterior,
        lr_hard=lr_hard,
        lr_easy=lr_easy,
        bayesian_updates=updates,
        credible_interval=ci,
    )


def _bootstrap_posterior(claims: List[StructuredClaim], prior: float,
                         lr_hard: float, lr_easy: float,
                         n_boot: int = 5000, seed: int = 42) -> Tuple[float, float]:
    """Bootstrap credible interval for posterior."""
    rng = np.random.RandomState(seed)
    posteriors = []
    for _ in range(n_boot):
        sample = rng.choice(claims, size=len(claims), replace=True)
        br = BayesianReasoning('boot', prior=prior)
        for c in sample:
            lr = lr_hard if c.hard_case else lr_easy
            ev = EvidenceItem(
                name='boot', description='',
                p_if_claim_true=lr * 0.5,
                p_if_claim_false=0.5,
            )
            try:
                br.update(ev)
            except ZeroDivisionError:
                pass
        posteriors.append(br.current_posterior)
    arr = np.array(posteriors)
    return float(np.percentile(arr, 2.5)), float(np.percentile(arr, 97.5))


def compute_calibration_curve(claims: List[StructuredClaim],
                               n_bins: int = 5) -> Dict[str, Any]:
    """Compute calibration curve: predicted confidence vs actual positive rate."""
    # Assign confidence bins based on hard_case and claim_type
    bins = defaultdict(lambda: {'predicted': [], 'actual': []})

    for c in claims:
        # Confidence proxy: higher for non-hard cases
        confidence = 0.8 if not c.hard_case else 0.4
        # Bin by confidence
        bin_idx = min(int(confidence * n_bins), n_bins - 1)
        bins[bin_idx]['predicted'].append(confidence)
        bins[bin_idx]['actual'].append(1.0 if c.positive_control else 0.0)

    curve = []
    for idx in sorted(bins.keys()):
        preds = bins[idx]['predicted']
        actuals = bins[idx]['actual']
        curve.append({
            'bin': idx,
            'mean_predicted': float(np.mean(preds)),
            'mean_actual': float(np.mean(actuals)),
            'n': len(actuals),
        })
    return {'bins': curve, 'n_bins': n_bins}


# ============================================================
# Report generation
# ============================================================

def generate_plots(results: List[CalibrationResult],
                   proof_outcomes: List[ProofOutcome],
                   output_dir: Path):
    """Generate calibration and posterior plots."""
    try:
        import matplotlib
        matplotlib.use('Agg')
        import matplotlib.pyplot as plt
    except ImportError:
        print("  matplotlib not available, skipping plots")
        return

    output_dir.mkdir(parents=True, exist_ok=True)

    # Plot 1: Prior vs Posterior by domain
    fig, ax = plt.subplots(figsize=(10, 6))
    domains = [r.domain for r in results]
    priors = [r.prior for r in results]
    posteriors = [r.posterior for r in results]
    ci_lo = [r.credible_interval[0] if r.credible_interval else r.posterior for r in results]
    ci_hi = [r.credible_interval[1] if r.credible_interval else r.posterior for r in results]

    x = np.arange(len(domains))
    width = 0.35

    bars1 = ax.bar(x - width/2, priors, width, label='Prior (base rate)', color='#3498db', alpha=0.8)
    bars2 = ax.bar(x + width/2, posteriors, width, label='Posterior (after calibration)', color='#e74c3c', alpha=0.8)

    # Error bars for credible intervals
    err_lo = [p - lo for p, lo in zip(posteriors, ci_lo)]
    err_hi = [hi - p for p, hi in zip(posteriors, ci_hi)]
    ax.errorbar(x + width/2, posteriors, yerr=[err_lo, err_hi],
                fmt='none', color='black', capsize=5, linewidth=1.5)

    ax.set_xlabel('Legal Domain', fontsize=11)
    ax.set_ylabel('Probability (positive_control)', fontsize=11)
    ax.set_title('#95: Bayesian Calibration — Prior vs Posterior by Domain\n'
                 '(180 structured claims, proxy calibration)', fontsize=13)
    ax.set_xticks(x)
    ax.set_xticklabels(domains, rotation=20, ha='right')
    ax.legend(fontsize=10)
    ax.grid(True, alpha=0.3, axis='y')
    ax.set_ylim(0, 1.1)
    plt.tight_layout()
    plt.savefig(output_dir / 'calibration_prior_posterior.png', dpi=150)
    plt.close()
    print(f"  Saved: {output_dir / 'calibration_prior_posterior.png'}")

    # Plot 2: Likelihood ratios
    fig, ax = plt.subplots(figsize=(10, 6))
    lr_hard = [r.lr_hard for r in results]
    lr_easy = [r.lr_easy for r in results]
    bars1 = ax.bar(x - width/2, lr_hard, width, label='LR (hard_case=True)', color='#e67e22', alpha=0.8)
    bars2 = ax.bar(x + width/2, lr_easy, width, label='LR (hard_case=False)', color='#27ae60', alpha=0.8)
    ax.axhline(y=1.0, color='gray', linestyle='--', alpha=0.5, label='LR=1 (no update)')
    ax.set_xlabel('Legal Domain', fontsize=11)
    ax.set_ylabel('Likelihood Ratio', fontsize=11)
    ax.set_title('#95: Likelihood Ratios by Domain and Difficulty\n'
                 '(hard_case vs non-hard_case)', fontsize=13)
    ax.set_xticks(x)
    ax.set_xticklabels(domains, rotation=20, ha='right')
    ax.legend(fontsize=10)
    ax.grid(True, alpha=0.3, axis='y')
    plt.tight_layout()
    plt.savefig(output_dir / 'calibration_likelihood_ratios.png', dpi=150)
    plt.close()
    print(f"  Saved: {output_dir / 'calibration_likelihood_ratios.png'}")

    # Plot 3: Proof outcomes pie chart
    fig, ax = plt.subplots(figsize=(8, 6))
    status_counts = Counter(p.status for p in proof_outcomes)
    labels = list(status_counts.keys())
    sizes = list(status_counts.values())
    colors = ['#2ecc71', '#e74c3c', '#f39c12', '#95a5a6'][:len(labels)]
    ax.pie(sizes, labels=labels, autopct='%1.0f%%', colors=colors, startangle=90)
    ax.set_title('#95: Proof Outcome Distribution\n'
                 f'(n={len(proof_outcomes)})', fontsize=13)
    plt.tight_layout()
    plt.savefig(output_dir / 'proof_outcomes.png', dpi=150)
    plt.close()
    print(f"  Saved: {output_dir / 'proof_outcomes.png'}")


def generate_manifest(claims: List[StructuredClaim],
                      results: List[CalibrationResult],
                      proof_outcomes: List[ProofOutcome],
                      aaf_summary: Dict,
                      output_path: Path):
    """Generate calibration manifest JSONL."""
    output_path.parent.mkdir(parents=True, exist_ok=True)

    # Build domain result lookup
    domain_lookup = {r.domain: r for r in results}

    with open(output_path, 'w', encoding='utf-8') as f:
        for c in claims:
            dr = domain_lookup.get(c.domain)
            record = {
                'claim_id': c.claim_id,
                'domain': c.domain,
                'claim_type': c.claim_type,
                'hard_case': c.hard_case,
                'positive_control': c.positive_control,
                'verification_status': c.verification_status,
                'primary_claim': c.primary_claim,
                'domain_prior': dr.prior if dr else None,
                'domain_posterior': dr.posterior if dr else None,
                'domain_lr_hard': dr.lr_hard if dr else None,
                'domain_lr_easy': dr.lr_easy if dr else None,
            }
            f.write(json.dumps(record, ensure_ascii=False) + '\n')

    print(f"  Manifest: {output_path} ({len(claims)} records)")


def generate_csv_report(results: List[CalibrationResult],
                        proof_outcomes: List[ProofOutcome],
                        output_path: Path):
    """Generate CSV summary."""
    output_path.parent.mkdir(parents=True, exist_ok=True)
    with open(output_path, 'w', encoding='utf-8', newline='') as f:
        writer = csv.writer(f)
        writer.writerow([
            'domain', 'n_total', 'n_positive', 'n_hard',
            'prior', 'posterior', 'lr_hard', 'lr_easy',
            'ci_95_lo', 'ci_95_hi', 'ci_width',
        ])
        for r in results:
            ci_lo = r.credible_interval[0] if r.credible_interval else ''
            ci_hi = r.credible_interval[1] if r.credible_interval else ''
            ci_width = (r.credible_interval[1] - r.credible_interval[0]) if r.credible_interval else ''
            writer.writerow([
                r.domain, r.n_total, r.n_positive, r.n_hard,
                f'{r.prior:.4f}', f'{r.posterior:.4f}',
                f'{r.lr_hard:.4f}', f'{r.lr_easy:.4f}',
                f'{ci_lo:.4f}' if isinstance(ci_lo, float) else ci_lo,
                f'{ci_hi:.4f}' if isinstance(ci_hi, float) else ci_hi,
                f'{ci_width:.4f}' if isinstance(ci_width, float) else ci_width,
            ])
        # Add proof outcomes summary
        writer.writerow([])
        writer.writerow(['proof_artifact', 'artifact_id', 'status', 'trust_label',
                         'runtime_seconds', 'checker_type', 'is_correct'])
        for p in proof_outcomes:
            writer.writerow([
                p.name, p.artifact_id, p.status, p.trust_label,
                f'{p.runtime_seconds:.2f}', p.checker_type, p.is_correct,
            ])
    print(f"  CSV report: {output_path}")


def generate_markdown_report(
    results: List[CalibrationResult],
    proof_outcomes: List[ProofOutcome],
    aaf_summary: Dict,
    calibration_curve: Dict,
    output_path: Path,
):
    """Generate markdown report."""
    output_path.parent.mkdir(parents=True, exist_ok=True)

    lines = [
        '# #95 Bayesian Confidence Calibration: Proxy Calibration Report',
        '',
        '> **Evidence level:** PROXY_CALIBRATION',
        '> **Date:** 2026-06-19',
        '> **Status:** Internal label calibration; NOT real judicial outcome calibration',
        '',
        '---',
        '',
        '## 1. Data Summary',
        '',
        f'- **Structured claims:** {sum(r.n_total for r in results)} (6 domains × 30)',
        f'- **Proof outcomes:** {len(proof_outcomes)} (10 PROVED, 3 REFUTED, 4 PENDING)',
        f'- **AAF stability patterns:** {aaf_summary.get("total_patterns", "N/A")}',
        '',
        '## 2. Domain Calibration Results',
        '',
        '| Domain | N | Positive | Hard | Prior | Posterior | 95% CI | LR_hard | LR_easy |',
        '|---|---:|---:|---:|---:|---:|---|---:|---:|',
    ]
    for r in results:
        ci_str = f'[{r.credible_interval[0]:.3f}, {r.credible_interval[1]:.3f}]' if r.credible_interval else 'N/A'
        lines.append(
            f'| {r.domain} | {r.n_total} | {r.n_positive} | {r.n_hard} '
            f'| {r.prior:.3f} | {r.posterior:.3f} | {ci_str} | {r.lr_hard:.3f} | {r.lr_easy:.3f} |'
        )

    # Summary statistics
    all_priors = [r.prior for r in results if r.n_total > 0]
    all_posteriors = [r.posterior for r in results if r.n_total > 0]
    lines += [
        '',
        '### Summary Statistics',
        '',
        f'- **Mean prior:** {np.mean(all_priors):.3f} (range: {min(all_priors):.3f}–{max(all_priors):.3f})',
        f'- **Mean posterior:** {np.mean(all_posteriors):.3f} (range: {min(all_posteriors):.3f}–{max(all_posteriors):.3f})',
        f'- **Mean CI width:** {np.mean([(r.credible_interval[1]-r.credible_interval[0]) for r in results if r.credible_interval]):.3f}',
        '',
        '## 3. Proof Outcome Analysis',
        '',
        f'- **Total proof artifacts:** {len(proof_outcomes)}',
        f'- **PROVED:** {sum(1 for p in proof_outcomes if p.status == "PROVED")}',
        f'- **REFUTED:** {sum(1 for p in proof_outcomes if p.status == "REFUTED")}',
        f'- **PENDING_TOOLCHAIN:** {sum(1 for p in proof_outcomes if p.status == "PENDING_TOOLCHAIN")}',
        '',
        '### Proof checker types',
        '',
    ]
    checker_counts = Counter(p.checker_type for p in proof_outcomes)
    for checker, count in checker_counts.most_common():
        proved = sum(1 for p in proof_outcomes if p.checker_type == checker and p.status == 'PROVED')
        lines.append(f'- **{checker}:** {count} artifacts ({proved} PROVED)')

    lines += [
        '',
        '## 4. AAF Stability Analysis',
        '',
        f'- **Total patterns:** {aaf_summary.get("total_patterns", "N/A")}',
        f'- **Dung modelable:** {aaf_summary.get("dung_modelable", "N/A")}',
        f'- **Dung more stable:** {aaf_summary.get("dung_more_stable", "N/A")}',
        f'- **Current evaluator more stable:** {aaf_summary.get("current_evaluator_more_stable", "N/A")}',
        f'- **Dung fails:** {aaf_summary.get("dung_fails", "N/A")}',
        '',
        f'**Conclusion:** {aaf_summary.get("conclusion", "N/A")}',
        '',
        '## 5. Calibration Curve',
        '',
        '| Bin | Mean Predicted | Mean Actual | N |',
        '|---|---:|---:|---:|',
    ]
    for b in calibration_curve.get('bins', []):
        lines.append(
            f'| {b["bin"]} | {b["mean_predicted"]:.3f} | {b["mean_actual"]:.3f} | {b["n"]} |'
        )

    lines += [
        '',
        '## 6. Critical Finding: Zero Negative Class',
        '',
        '**ALL 180 claims have positive_control=True (100%%).** This means:',
        '- The prior is 1.0 for every domain',
        '- The posterior is always 1.0 (trivial calibration)',
        '- There are no negative examples to calibrate against',
        '- Only 1 out of 180 claims has hard_case=True (0.6%%)',
        '',
        'This is a fundamental limitation of the current structured claims data.',
        'The claims were designed as expected positive outcomes for the engine,',
        'not as a balanced calibration dataset.',
        '',
        '## 7. Alternative: Proof Outcome Calibration',
        '',
        'The 17 proof outcomes provide a genuine binary dataset:',
        '- 10 PROVED (positive) vs 3 REFUTED (negative) = 76.9%% base rate',
        '- This is the only real binary ground truth in the project',
        '',
        '## 8. Limitations (CRITICAL)',
        '',
        '1. **NOT real judicial outcomes.** These 180 claims are structured internal labels',
        '   with verification_status=VERIFIED. They represent expected engine outputs,',
        '   not actual court decisions.',
        '2. **Confidence_expected is uniformly "high"** for all claims. There is no',
        '   confidence gradient in the ground truth. The calibration uses hard_case',
        '   as a proxy for difficulty/confidence.',
        '3. **Prior is computed from the same data** used for updating, which introduces',
        '   circularity. A proper calibration would use a held-out test set.',
        '4. **The BayesianReasoning class uses sequential updating**, not batch MCMC.',
        '   For n=30 per domain, the order of evidence presentation affects the trajectory',
        '   (though not the final posterior if all evidence is used).',
        '5. **No real-world validation.** The calibration has not been tested against',
        '   actual legal outcomes or expert judgments.',
        '',
        '## 8. Next Steps',
        '',
        '1. **Collect real calibration data:** 30+ cases with actual court outcomes.',
        '2. **Run held-out calibration:** Split claims into train/test, calibrate on train,',
        '   validate on test.',
        '3. **Add confidence gradient:** Replace binary positive_control with continuous',
        '   confidence scores from expert annotation.',
        '4. **MCMC validation:** Use PyMC/Stan for proper posterior inference with',
        '   hierarchical priors across domains.',
        '',
    ]

    with open(output_path, 'w', encoding='utf-8') as f:
        f.write('\n'.join(lines))
    print(f"  Markdown report: {output_path}")


# ============================================================
# Main
# ============================================================

def main():
    start = time.time()
    data_dir = _PROJECT_ROOT / 'data'
    proof_path = _PROJECT_ROOT / 'proofs' / 'engineering_proof_artifacts' / 'proof_run_results.json'
    output_dir = _PROJECT_ROOT / 'reports' / 'bayesian_calibration'
    output_dir.mkdir(parents=True, exist_ok=True)

    print('=' * 70)
    print('#95: Bayesian Confidence Calibration')
    print('=' * 70)

    # 1. Load data
    print('\n[1/7] Loading data...')
    claims = load_claims(data_dir)
    proof_outcomes = load_proof_outcomes(proof_path)
    aaf_summary = load_aaf_stability(data_dir)
    print(f'  Claims: {len(claims)} (domains: {Counter(c.domain for c in claims)})')
    print(f'  Proof outcomes: {len(proof_outcomes)}')
    print(f'  AAF patterns: {aaf_summary.get("total_patterns", "N/A")}')

    # 2. Per-domain Bayesian calibration
    print('\n[2/7] Per-domain Bayesian calibration...')
    domains = sorted(set(c.domain for c in claims))
    results = []
    for domain in domains:
        result = calibrate_domain(claims, domain)
        results.append(result)
        ci_str = f'[{result.credible_interval[0]:.3f}, {result.credible_interval[1]:.3f}]' if result.credible_interval else 'N/A'
        print(f'  {domain}: prior={result.prior:.3f}, posterior={result.posterior:.3f}, '
              f'CI={ci_str}, LR_hard={result.lr_hard:.3f}, LR_easy={result.lr_easy:.3f}')

    # 3. Overall calibration
    print('\n[3/7] Overall calibration...')
    overall_prior = sum(1 for c in claims if c.positive_control) / len(claims)
    overall_hard = sum(1 for c in claims if c.hard_case) / len(claims)
    print(f'  Overall prior (positive_control rate): {overall_prior:.3f}')
    print(f'  Overall hard_case rate: {overall_hard:.3f}')

    # 4. Calibration curve
    print('\n[4/7] Computing calibration curve...')
    cal_curve = compute_calibration_curve(claims)
    for b in cal_curve['bins']:
        print(f'  Bin {b["bin"]}: predicted={b["mean_predicted"]:.3f}, '
              f'actual={b["mean_actual"]:.3f}, n={b["n"]}')

    # 5. Proof outcome analysis
    print('\n[5/7] Analyzing proof outcomes...')
    for p in proof_outcomes:
        print(f'  {p.artifact_id}: {p.status} ({p.trust_label}), '
              f'checker={p.checker_type}, runtime={p.runtime_seconds:.1f}s')

    # 6. Generate plots
    print('\n[6/7] Generating plots...')
    generate_plots(results, proof_outcomes, output_dir)

    # 7. Generate reports
    print('\n[7/7] Generating reports...')
    generate_manifest(claims, results, proof_outcomes, aaf_summary,
                      output_dir / 'calibration_manifest.jsonl')
    generate_csv_report(results, proof_outcomes, output_dir / 'calibration_report.csv')
    generate_markdown_report(results, proof_outcomes, aaf_summary, cal_curve,
                             output_dir / 'calibration_report.md')

    elapsed = time.time() - start
    print(f'\n{"=" * 70}')
    print(f'DONE in {elapsed:.1f}s')
    print(f'Output: {output_dir}')
    print(f'{"=" * 70}')


if __name__ == '__main__':
    main()
