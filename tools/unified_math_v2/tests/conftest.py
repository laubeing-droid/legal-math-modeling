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
for candidate in (str(PKG), str(HERE)):
    if candidate not in sys.path:
        sys.path.insert(0, candidate)
