"""Pytest bootstrap for the unified_math_v2 test directory.

The tests import sibling modules directly (`test_v2_contract_and_models`)
and the packages `unified` / `unified_v21` / `reference` that live one
directory up, mirroring the sys.path layout used by
`tools/unified_math_v2/scripts` entry points.
"""

import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
PKG = HERE.parent

# `reference` is also the package name of tools/full_math/reference; under a
# repo-wide single-process pytest run whichever tree is collected first wins in
# sys.modules and starves the other. Evict cached copies of the shared names so
# this tree re-resolves them against its own path entries below. The other
# trees bind these modules at collection time and never re-import at runtime,
# so eviction cannot corrupt them.
for shared in ("reference", "unified", "unified_v21"):
    for name in [m for m in sys.modules if m == shared or m.startswith(shared + ".")]:
        del sys.modules[name]

for candidate in (str(PKG), str(HERE)):
    if candidate not in sys.path:
        sys.path.insert(0, candidate)
