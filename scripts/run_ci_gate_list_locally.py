"""Run every command the CI python-gates step runs, in CI order, and report each exit code.

On 2026-10-03 a round reddened in CI on `generate_probability_audit_surface.py --check` after a
new lemma changed AxiomAudit.lean. Nothing was wrong with the gate -- the local pre-check ran a
*subset* chosen from memory, and the one command that would have caught it was the one skipped.
A hand-picked subset of a gate list is worse than no pre-check, because it produces a green that
means "the gates I happened to think of".

So the list is read from the workflow itself rather than duplicated here: if a step is added to
`.github/workflows/lean-build.yml`, this runner picks it up, and the wiring test
(`tests/spec/test_all_ci_gates_are_wired.py`) already keeps that step honest.

    python scripts/run_ci_gate_list_locally.py             # everything
    python scripts/run_ci_gate_list_locally.py --skip-pytest
"""

from __future__ import annotations

import re
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
WORKFLOW = ROOT / ".github" / "workflows" / "lean-build.yml"
STEP_MARKER = "Existing gates plus full retained and new root tests"


def gate_commands() -> list[str]:
    """The `python ...` lines of the python-gates step, in file order."""
    text = WORKFLOW.read_text(encoding="utf-8")
    start = text.index(STEP_MARKER)
    body = text[start:]
    end = body.index("\n    - name:") if "\n    - name:" in body[10:] else len(body)
    commands = []
    for line in body[:end].splitlines():
        stripped = line.strip()
        if stripped.startswith("python ") and ">" not in stripped and "|" not in stripped:
            commands.append(stripped)
    assert len(commands) >= 10, f"only found {len(commands)} gate commands in the step"
    return commands


def main() -> int:
    skip_pytest = "--skip-pytest" in sys.argv
    failures = []
    for command in gate_commands():
        if skip_pytest and re.search(r"-m pytest", command):
            print(f"SKIP  {command}")
            continue
        proc = subprocess.run(command.split(), cwd=ROOT, capture_output=True, text=True)
        status = "ok" if proc.returncode == 0 else "FAIL"
        print(f"{status:4s} exit={proc.returncode}  {command}")
        if proc.returncode != 0:
            tail = (proc.stdout + proc.stderr).strip().splitlines()[-4:]
            for line in tail:
                print("      | " + line[:160])
            failures.append(command)
    print(f"\n{len(failures)} of the CI gate commands failed locally")
    return 1 if failures else 0


if __name__ == "__main__":
    raise SystemExit(main())
