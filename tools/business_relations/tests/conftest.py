"""Import path for the business test suite (mirrors ci/run_reference.py:
the suite imports `business` from tools/business_relations/reference)."""
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'reference'))
