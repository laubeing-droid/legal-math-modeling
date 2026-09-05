# Allowed Claims

Claims are allowed only when their named evidence is present, content-valid, and bound to the cited subject commit.

| Claim | Minimum evidence |
|---|---|
| A named Lean theorem elaborates | Successful CI build of its module at the cited commit |
| A named theorem uses no custom domain axiom | Its axiom-audit entry reports only accepted Lean foundations or no axioms |
| ULM01–ULM16 passed the documented release run | Module matrix, clean build, audits, certificate, verifier, and final gate for run 33946211096 |
| The Python suite passed | Full collection and full execution report for the cited commit |
| The checker rejected the controlled mutations | Mutation report naming every mutation and recording 0 survivors/errors/skips |
| Three runtime fixtures refined successfully | Receipts for `contract_breach`, `fact_admission`, and `unknown_timeout`, bound to both repository commits |
| The v2 registry contains 48 distinct types and preserves v1 names | `LegalModelV2.lean` and `theory/spec/canonical_v2/manifest.py` |

Qualifiers such as “for the named model,” “for the named fixtures,” and “at commit …” are part of the claim, not optional caveats.

The exact immutable-run facts are recorded in [Final Formal Release Report](FINAL_FORMAL_RELEASE_REPORT.md).
