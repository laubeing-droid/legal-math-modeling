# Authority Map

| Question | Deciding artifact | Non-authority |
|---|---|---|
| What is a Lean theorem's statement? | `.lean` source at the cited commit | README, paper, theorem count |
| Did a Lean module elaborate? | Successful GitHub Actions module job for that commit | Local text scan, green badge alone |
| Did the clean build pass? | Complete clean-build log with successful command exit | Partial module build, piped output without failure propagation |
| Which axioms does a theorem report? | Raw axiom-audit output for the same subject | Narrative summary |
| Did Python behavior pass? | Full collected test manifest and full test log | Selected tests |
| Did controlled malformed inputs fail closed? | `mutation-property-report.json` | Test-count claim |
| Did runtime refinement pass? | Signed/bound receipts plus `runtime-refinement-report.json` for both repository commits | Similar output, manually copied JSON |
| Is the release certificate valid? | Certificate content, independent verifier, run identity, and final gate together | Certificate filename or workflow color |
| Is a legal source authoritative or a conclusion legally correct? | External legal authority and accountable human review | Lean, checker, receipt, LLM output |

## Fail-closed rule

When the deciding artifact is missing, expired without preservation, stale, skipped, timed out, from a different subject, or internally inconsistent, the answer is `UNKNOWN` or BLOCKED. Explanatory documents cannot upgrade it.

The current documented immutable snapshot is [GitHub Actions run 33946211096](../formal-release/FINAL_FORMAL_RELEASE_REPORT.md).
