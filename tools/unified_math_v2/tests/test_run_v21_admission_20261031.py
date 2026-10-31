"""Synthetic CLI negatives for fail-closed fact-standing parsing."""

import json
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[3]
RUNNER = REPO_ROOT / "tools" / "unified_math_v2" / "scripts" / "run_v21.py"


class RunV21AdmissionTests(unittest.TestCase):
    def _run_case(self, directory: Path, *, standing_marker=None):
        fact = {"id": "fact-1", "predicate": "receipt_confirmed"}
        if standing_marker is not None:
            fact["standing"] = standing_marker
        case_path = directory / "case.json"
        output_path = directory / "result.json"
        case_path.write_text(
            json.dumps({"case_id": "case-1", "issue": "loan", "facts": [fact]}),
            encoding="utf-8",
        )
        result = subprocess.run(
            [
                sys.executable,
                "-B",
                str(RUNNER),
                "--case",
                str(case_path),
                "--output",
                str(output_path),
            ],
            cwd=REPO_ROOT,
            capture_output=True,
            text=True,
            check=False,
        )
        return result, output_path

    def test_missing_standing_is_rejected_without_success_output(self):
        with tempfile.TemporaryDirectory() as temporary:
            result, output_path = self._run_case(Path(temporary))
            self.assertNotEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertIn("KeyError: 'standing'", result.stderr)
            self.assertFalse(output_path.exists())
            self.assertNotIn("independent_check_ok", result.stdout)

    def test_unknown_standing_is_rejected_without_success_output(self):
        with tempfile.TemporaryDirectory() as temporary:
            result, output_path = self._run_case(
                Path(temporary), standing_marker="WITHDRAWN"
            )
            self.assertNotEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertIn("KeyError: 'WITHDRAWN'", result.stderr)
            self.assertFalse(output_path.exists())
            self.assertNotIn("independent_check_ok", result.stdout)


if __name__ == "__main__":
    unittest.main()
