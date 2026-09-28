# External ports under `JurisLean/External/` — provenance and license notices

This directory holds **ported copies of external Lean libraries**, brought in by
the 2026-09-28 owner decision ("literature-first; no self-built proof islands").
Two regimes live here:

| subtree | source | revision | pin | license | regime |
|---|---|---|---|---|---|
| `GameTheory/`, `FixedPointTheorems/` | elazarg/GameTheory + elazarg/fixed-point-theorems-lean4 | `107085bc4` / `42d4b401f` | same as this repo (lean v4.30.0, mathlib `c5ea0035…`) | MIT | byte-faithful: header + import roots only, gate re-derives each upstream sha256 |
| `NeuralNetworkProofs/` | davorrunje/neural-network-proofs | `f909425` | upstream is mathlib v4.32.0-rc1 → **cross-pin backport** | Apache-2.0 | drift repairs logged per file (`adaptations`), statement headers pinned |

Carry the gap-closing theorems: `mixed_nash_exists`, `oneShotDeviation_iff_spe`,
Kuhn both directions, Minimax, `brouwer_fixed_point`, `kakutani_fixed_point`
(same-pin) and `leshno_dense_iff` (backport). Machine-readable records:
`PROVENANCE.json` (same-pin) and `NeuralNetworkProofs/PROVENANCE.json` (backport).
Gates: `tests/spec/test_external_port_provenance.py`,
`tests/spec/test_neural_backport_provenance.py`.

Build status: all 57 modules built and axiom-audited green by run 36456965606
(subject `c5830ed`); release-root entry is a separate round per module
(`PENDING_CI_MODULES` in `scripts/ci/check_import_reachability.py`).

## Licenses

### elazarg/GameTheory — MIT

Source: https://github.com/elazarg/GameTheory at revision
`107085bc4a0306672f2f35fce1abc1345d7975ed`. The upstream `LICENSE` at that
revision reads:

> MIT License
>
> Copyright (c) 2025 Elazar Gershuni
>
> Permission is hereby granted, free of charge, to any person obtaining a copy
> of this software and associated documentation files (the "Software"), to deal
> in the Software without restriction, including without limitation the rights
> to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
> copies of the Software, and to permit persons to whom the Software is
> furnished to do so, subject to the following conditions:
>
> The above copyright notice and this permission notice shall be included in all
> copies or substantial portions of the Software.
>
> THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
> IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
> FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
> AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
> LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
> OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
> SOFTWARE.

Per-file headers in `GameTheory/` carry the same notice.

### elazarg/fixed-point-theorems-lean4 — MIT

Source: https://github.com/elazarg/fixed-point-theorems-lean4 (a fork of
https://github.com/harfe/fixed-point-theorems-lean4) at revision
`42d4b401f7b6a6520e3bac3a76b8538d7f47ba3e`. No `LICENSE` file exists in the
tree at that revision; the repository (and its upstream) report the MIT license
via GitHub's license detection, and the `LICENSE` file entered the tree in a
later upstream commit (`9571dd7`). The MIT notice above applies, with
`Copyright (c) Harfe` per the upstream harfe repository's license metadata.
The files in `FixedPointTheorems/` carry no per-file header upstream; this
document is the notice that travels with the copies.

### davorrunje/neural-network-proofs — Apache-2.0

See `NeuralNetworkProofs/PROVENANCE.md`; the full Apache-2.0 text is copied at
`NeuralNetworkProofs/LICENSE`.
