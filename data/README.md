# Data — Legal Validation Datasets

This directory contains the legal data used for empirical verification of mathematical claims.

## Structure

| Directory | Content | Source |
|-----------|---------|--------|
| `cn_legal/` | PRC legal claims (contract, tort, corporate, criminal, admin, data) | Kimi data collection |
| `us_legal/` | US legal generation scripts | Kimi data collection |
| `hk_legal/` | HK obstruction and privilege lattice data | Kimi strict proof |
| `aaf_legal/` | AAF validation summary | Kimi strict proof |
| `banach_pricing/` | Lipschitz estimates and pricing evidence | Kimi strict proof |
| `category_rosetta/` | Corpus manifest and obstruction analysis | Kimi strict proof |
| `dp_privilege/` | Jurisdiction lattices | Kimi strict proof |
| `galois_semantics/` | Galois audit summary and theorem dependency graph | Kimi strict proof |
| `legal_validation_results.json` | Overall validation results | Kimi engineering |

## Data Warning

- The pricing data (`banach_pricing/`) is **fee-schedule proxy data**, not real law-firm timesheets. It cannot prove the real Banach contraction claim.
- The CN/US/HK legal data is **curated and annotated**, not scraped from production systems.
- Google synthetic data has been **deleted** after validation to prevent accidental promotion into real evidence.
