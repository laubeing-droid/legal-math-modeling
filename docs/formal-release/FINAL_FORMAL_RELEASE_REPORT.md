# Final Formal Release Report

## Decision

GitHub Actions run [33946211096](https://github.com/laubeing-droid/legal-math-modeling/actions/runs/33946211096), attempt 1, passed its final release gate for the exact subject below. This is an immutable-run report, not a claim about later commits.

| Binding | Value |
|---|---|
| Workflow | `Lean Authority + Formal Release Pipeline` |
| Event | `push` |
| Subject commit | `2a1d33df353a005dffc5d8b95faa591524e2636e` |
| Subject tree | `c7525f767b43c7e8a663a4a9702f64cdea78b979` |
| Run / attempt | `33946211096` / `1` |
| Ref | `refs/heads/main` |
| Lean toolchain | `v4.30.0` |
| Job result | 97 success, 0 failure |

## Content-level evidence

| Gate | Recorded result |
|---|---|
| Module matrix | All 91 source-module jobs passed |
| Clean build | `Build completed successfully (2993 jobs)` |
| Certificate source inventory | 91 Lean files; 452 theorem declarations |
| ULM all-theorem audit | 145 declarations checked: 136 with allowed foundation axioms, 9 axiom-free |
| ULM core-composition audit | 27 declarations checked: 24 with allowed foundation axioms, 3 axiom-free |
| Reported foundation axioms | `propext`, `Classical.choice`, `Quot.sound` only |
| Python tests | 131 collected; 131 passed |
| Controlled mutation gate | 46/46 killed; 0 survived, errored, or skipped; score 1.0 |
| Runtime refinement | 3/3 fixtures passed: `contract_breach`, `fact_admission`, `unknown_timeout` |
| Claim audit | 0 forbidden hits |
| Certificate | `RELEASE_PASS_PENDING_INDEPENDENT_VERIFICATION`; non-empty subject binding; no missing CI evidence |
| Independent verifier | `VERIFIED_PENDING_RELEASE_GATE`; `error_codes=[]` |
| Final gate | Success |

The certificate and verifier use staged statuses by design. Their agreement plus the successful final gate is the pipeline's release decision; the staged strings must not be rewritten into a different verdict.

## Cross-repository binding

The runtime-refinement reports bind:

- legal-math-modeling commit `2a1d33df353a005dffc5d8b95faa591524e2636e`;
- juris-calculus runtime commit `c79e03b8d0cfed85c43cc013bf8a0b50326bc858`;
- build identity `github-actions:33946211096:1`.

These fixtures establish bounded agreement for the three named cases. They do not prove general refinement of the complete juris-calculus runtime.

## Limits

- This report does not certify the documentation commit that contains it; a later full-release run is needed for that commit.
- The mutation gate changes controlled checker inputs. It is not mutation testing of all Lean or Python source code.
- Three runtime fixtures are not exhaustive operational coverage.
- Axiom output discloses Lean dependencies; it does not establish legal truth, source completeness, empirical calibration, or production fitness.
- GitHub artifacts have finite retention. Preserve the JSON reports separately when durable archival evidence is required.

## Verification rule

Do not rely on workflow color alone. Read, for the same `head_sha`, `ci-run-identity.json`, `formal-release-certificate.json`, `independent-verifier-report.json`, `mutation-property-report.json`, `runtime-refinement-report.json`, `claim-audit-report.json`, the clean-build log, the axiom-audit logs, and the final-gate result.
