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

## Data Relationship to Lean Formalization

The data in this directory provides empirical grounding for the mathematical models. The Lean formalization (94 theorems, 0 sorry, 25 files) operates on abstract structures that this data helps instantiate:

| Lean Layer | Data Support |
|------------|--------------|
| Horn closure (HornFixedPoint.lean) | Legal facts and rules from cn_legal/ |
| Dung AAF (DungFixedPoint.lean) | Argument and attack structures from aaf_legal/ |
| Banach contraction (BanachFixedPoint.lean) | Pricing evidence from banach_pricing/ |
| Finite Rosetta (FiniteRosetta.lean) | Cross-jurisdiction mapping from category_rosetta/ |
| Galois adjunction (FiniteGaloisAdjunction.lean) | Semantic lattice data from galois_semantics/ |

## Data Warning

- The pricing data (`banach_pricing/`) is **fee-schedule proxy data**, not real law-firm timesheets. It supports schema exploration, not real Banach contraction proof.
- The CN/US/HK legal data is **curated and annotated**, not scraped from production systems.
- Google synthetic data has been **deleted** after validation to prevent accidental promotion into real evidence.
- Data quality must be checked before any statistical claims; see the `data_quality` field in each dataset.

## Spec Types

The 11 spec types that connect data to formalization:

LegalFact, LegalRule, LegalNorm, LegalClaim, Argument, Attack, Priority, Violation, Reparation, DecisionStatus, ProofTrace
