# Project Memory

## 2026-08-15 Necessary Supplement Construction

- GitHub Actions is the authoritative Lean runner for this work. Do not resume local Lake/Lean
  compilation unless the user explicitly reverses the CI-only direction.
- A strict release build must compile the root plus explicit targets derived from every Lean source
  inventory path. The default root build omitted valid source files and previously hid stale scratch
  API probes.
- The release gate order is Python collection/full tests, source inventory, `lake clean`, pinned
  Mathlib cache restore, all-module Lake build, AxiomAudit, and forbidden-token guard scan.
- Current source inventory: 33 Lean files, 141 theorem declarations. A successful CI artifact must
  be used for release claims; the generated source manifests remain inventories only.
- Certificate/checker v2 and the task-bounded Horn-to-AAF translation witness are implemented and
  mutation-tested. V1 remains parseable but cannot obtain v2 decisive acceptance.
- L3 temporal applicability and L4 exact numeric integration remain `DEFERRED` because no real
  consumer trigger was found.
- L5 remains fail-closed. LMM has the receipt schema and independent verifier, but the external
  `juris-calculus` formal entrypoint does not yet emit an actual `RuntimeRefinementReceipt`.
- Project network operations require proxy `http://127.0.0.1:10808`; stale process defaults may point
  at inactive port `20808`.
