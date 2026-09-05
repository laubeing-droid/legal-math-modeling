# Runtime Refinement Evidence

## Current bounded result

GitHub Actions run `33946211096`, attempt 1, recorded three passing cross-repository fixtures:

| Fixture | Result |
|---|---|
| `contract_breach` | PASS |
| `fact_admission` | PASS |
| `unknown_timeout` | PASS |

The reports bind legal-math-modeling commit `2a1d33df353a005dffc5d8b95faa591524e2636e`, juris-calculus commit `c79e03b8d0cfed85c43cc013bf8a0b50326bc858`, and build identity `github-actions:33946211096:1`.

The fixtures execute the runtime path, generate real receipts, and validate their content and bindings through the release pipeline. This supersedes the earlier inconclusive 2026-08-15 page at this path; that historical state remains recoverable from Git history.

## Claim boundary

The evidence supports only bounded agreement for these three fixtures and these two commits. It does not establish:

- general refinement of all juris-calculus behavior;
- completeness of fact extraction, source authority, or legal rules;
- correctness of every timeout, conflict, remedy, or procedural path;
- legal correctness of a real case;
- validity for later commits.

See [Final Formal Release Report](../../formal-release/FINAL_FORMAL_RELEASE_REPORT.md) for the complete same-subject gate record.
