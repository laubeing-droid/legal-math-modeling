# Bayesian Confidence Calibration: Proxy Calibration Report

> **Evidence level:** PROXY_CALIBRATION
> **Date:** 2026-06-19
> **Status:** Internal label calibration; NOT real judicial outcome calibration

---

## 1. Data Summary

- **Structured claims:** 180 (6 domains x 30)
- **Proof outcomes:** 17 (10 PROVED, 3 REFUTED, 4 PENDING)
- **AAF stability patterns:** 18

## 2. Domain Calibration Results

| Domain | N | Positive | Hard | Prior | Posterior | 95% CI | LR_hard | LR_easy |
|---|---:|---:|---:|---:|---:|---|---:|---:|
| administrative | 30 | 30 | 0 | 1.000 | 1.000 | [1.000, 1.000] | 1.000 | 31.000 |
| contract | 30 | 30 | 0 | 1.000 | 1.000 | [1.000, 1.000] | 1.000 | 31.000 |
| corporate | 30 | 30 | 0 | 1.000 | 1.000 | [1.000, 1.000] | 1.000 | 31.000 |
| criminal | 30 | 30 | 0 | 1.000 | 1.000 | [1.000, 1.000] | 1.000 | 31.000 |
| data_crossborder | 30 | 30 | 1 | 1.000 | 1.000 | [1.000, 1.000] | 2.000 | 30.000 |
| tort | 30 | 30 | 0 | 1.000 | 1.000 | [1.000, 1.000] | 1.000 | 31.000 |

### Summary Statistics

- **Mean prior:** 1.000 (range: 1.000-1.000)
- **Mean posterior:** 1.000 (range: 1.000-1.000)
- **Mean CI width:** 0.000

## 3. Proof Outcome Analysis

- **Total proof artifacts:** 17
- **PROVED:** 10
- **REFUTED:** 3
- **PENDING_TOOLCHAIN:** 4

### Proof checker types

- **python:** 12 artifacts (9 PROVED)
- **z3:** 2 artifacts (1 PROVED)
- **lean:** 2 artifacts (0 PROVED)
- **tlaplus:** 1 artifacts (0 PROVED)

## 4. AAF Stability Analysis

- **Total patterns:** 18
- **Dung modelable:** 17
- **Dung more stable:** 16
- **Current evaluator more stable:** 1
- **Dung fails:** 1

**Conclusion:** Horn closure + Dung grounded extension is more stable than current rebuttal confidence-zeroing for legal defeasible reasoning in 16 out of 18 patterns, with 1 pattern where Dung cannot fully model the legal nuance (e.g., partial liability reduction, liability transfer).

## 5. Calibration Curve

| Bin | Mean Predicted | Mean Actual | N |
|---|---:|---:|---:|
| 2 | 0.400 | 1.000 | 1 |
| 4 | 0.800 | 1.000 | 179 |

## 6. Critical Finding: Zero Negative Class

**ALL 180 claims have positive_control=True (100%).** This means:
- The prior is 1.0 for every domain
- The posterior is always 1.0 (trivial calibration)
- There are no negative examples to calibrate against
- Only 1 out of 180 claims has hard_case=True (0.6%)

This is a fundamental limitation of the current structured claims data.
The claims were designed as expected positive outcomes for the engine,
not as a balanced calibration dataset.

## 7. Alternative: Proof Outcome Calibration

The 17 proof outcomes provide a genuine binary dataset:
- 10 PROVED (positive) vs 3 REFUTED (negative) = 76.9% base rate
- This is the only real binary ground truth in the project

## 8. Brier Score Comparison

- **Our proxy calibration:** 0.2209
- **COMPAS recidivism (7,214 records):** 0.2295

Our Brier score is marginally better than COMPAS, but this comparison has
critical caveats: our calibration uses proxy labels (not real judicial outcomes)
and our sample size (n=13 proof outcomes for LOO-CV) is far smaller than
COMPAS (n=7,214).

## 9. Limitations (CRITICAL)

1. **NOT real judicial outcomes.** These 180 claims are structured internal labels
   with verification_status=VERIFIED. They represent expected engine outputs,
   not actual court decisions.
2. **Confidence_expected is uniformly "high"** for all claims. There is no
   confidence gradient in the ground truth. The calibration uses hard_case
   as a proxy for difficulty/confidence.
3. **Prior is computed from the same data** used for updating, which introduces
   circularity. A proper calibration would use a held-out test set.
4. **The BayesianReasoning class uses sequential updating**, not batch MCMC.
   For n=30 per domain, the order of evidence presentation affects the trajectory
   (though not the final posterior if all evidence is used).
5. **No real-world validation.** The calibration has not been tested against
   actual legal outcomes or expert judgments.

## 10. Next Steps

1. **Collect real calibration data:** 30+ cases with actual court outcomes.
2. **Run held-out calibration:** Split claims into train/test, calibrate on train,
   validate on test.
3. **Add confidence gradient:** Replace binary positive_control with continuous
   confidence scores from expert annotation.
4. **MCMC validation:** Use PyMC/Stan for proper posterior inference with
   hierarchical priors across domains.
