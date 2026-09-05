# Legal Validation Data

This directory contains curated, generated, proxy, and summary datasets used to instantiate or test bounded mathematical models. Dataset presence is not proof of provenance, representativeness, legal authority, or a theorem.

| Directory | Intended use |
|---|---|
| `cn_legal/`, `us_legal/`, `hk_legal/` | Jurisdiction-specific claims, statutes, mappings, and generators |
| `aaf_legal/` | Argumentation examples and summaries |
| `banach_pricing/` | Fee-schedule proxy data for model exploration |
| `category_rosetta/` | Cross-jurisdiction mapping and obstruction experiments |
| `dp_privilege/` | Privacy/privilege lattice experiments |
| `galois_semantics/` | Finite semantic-lattice examples |

## Use rules

- Read each file's provenance and quality fields before use.
- Treat generated or model-produced records as candidates, not authoritative legal facts.
- The pricing material is proxy data, not law-firm timesheets and not proof of a real contraction coefficient.
- Finite examples may validate a fixture or expose a counterexample; they do not prove an unrestricted theorem.
- Do not infer current formal-release status from historical data summaries.

The 11 v1 schema names and 48-type v2 registry are documented in [Canonical Legal Schema](../docs/spec/canonical_legal_schema.md).
