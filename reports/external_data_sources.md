# External Data Sources Report (Online Collection)

> **Date:** 2026-06-19
> **Purpose:** #94 MDL vs FP empirical study + #95 Bayesian calibration

---

## Downloaded and Analyzed

### COMPAS Recidivism Prediction Dataset

- **Source:** ProPublica / GitHub
- **URL:** `https://github.com/propublica/compas-analysis`
- **File:** `data/external/compas_scores_two_years.csv`
- **Records:** 7,214
- **Key fields:** `decile_score` (1-10 risk score), `two_year_recid` (binary reoffend), `race`, `age_cat`, `sex`
- **Calibration results:**
  - Brier score: 0.2295
  - ECE (5 bins): 0.0785
  - COMPAS overestimates risk for high scores (7-10) (gap -0.11 to -0.23)
  - COMPAS underestimates risk for low scores (1-3) (gap +0.08 to +0.11)

### LegalBench Legal Reasoning Benchmark

- **Source:** Stanford HazyResearch / HuggingFace
- **URL:** `https://huggingface.co/datasets/nguha/legalbench`
- **Files:** `data/external/legalbench/*.json` (11 tasks)
- **Records:** 2,529
- **Binary label tasks:** 4 (consumer_contracts_qa: 396, diversity_6: 300, hearsay: 94, international_citizenship: 500)

---

## Identified but Not Downloaded

| Dataset | Domain | Records | Jurisdiction | Access | Use Case |
|---|---|---|---|---|---|
| CAIL2018 | Criminal | 260K+ | CN | GitHub (manual download required) | Chinese criminal charge prediction calibration |
| JEC-QA | Multi-domain QA | 26K+ | CN | Academic sharing | Chinese legal reasoning calibration |
| CaseHOLD | Case law | 53K+ | US | HuggingFace | Case law reasoning calibration |
| LexGLUE | 7 tasks | Tens of thousands | EU/US | HuggingFace | Cross-jurisdiction NLP calibration |
| ECHR/ECtHR | Human rights | 11K+ | EU | HuggingFace | Multi-label calibration |
| ILDC | Court judgments | 35K+ | India | HuggingFace | Binary judgment prediction |
| SCOTUS Database | Supreme Court | 8K+ | US | Website direct download | US Supreme Court prediction |
| OpenLaw | Court cases | Millions | CN | Partially free | Chinese court document structuring |
| Pkulaw | All law | Millions | CN | Subscription required | Highest quality Chinese legal data |

---

## Key Findings

1. **COMPAS is the only downloaded dataset containing real predicted probabilities + real outcomes.** Its calibration characteristics (overestimation at high scores, underestimation at low scores) provide a baseline reference for the juris-calculus calibration.

2. **LegalBench provides 4 binary label tasks** that can be used to test the juris-calculus reasoning engine's accuracy and calibration across different legal reasoning types.

3. **CAIL2018 is the most relevant Chinese legal dataset** (260K+ criminal cases), but requires manual GitHub download (HuggingFace mirror unavailable).

4. **A cross CN/US/HK jurisdiction mapping dataset does not exist.** This is a domain gap. The juris-calculus `claim_mapping.csv` (44 records) is the only known cross CN/US/HK structured mapping data available.

---

## Recommendations for Next Steps

1. Use COMPAS for calibration methodology validation (data already available)
2. Use LegalBench 4 binary tasks for reasoning engine benchmark testing
3. Manually download CAIL2018 for Chinese legal calibration (requires GitHub clone)
4. Use juris-calculus internal data (180 claims + 17 proof outcomes) for internal calibration
