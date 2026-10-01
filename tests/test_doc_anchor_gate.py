"""Doc anchors must resolve: a `name:LINE` in the construction docs is a citation.

The delivery notes and the binding table quote theorem locations. Every one of those
was checked when written, and a single mid-file insertion still invalidated 36 of them
at once, because line numbers are not stable facts -- they are coordinates into a file
that keeps growing.
"""

import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
SCRIPT = ROOT / "scripts" / "ci" / "check_doc_anchors.py"


def test_the_construction_docs_anchor_gate_passes():
    proc = subprocess.run(
        [sys.executable, str(SCRIPT)], cwd=ROOT, capture_output=True, text=True
    )
    assert proc.returncode == 0, proc.stdout + proc.stderr
    assert "stale anchors" not in proc.stdout


def test_the_gate_actually_reads_source_lines(tmp_path):
    """A doc that cites a wrong line must be rejected, not nodded through.

    The right line is read from source at test time rather than hard-coded, so this
    test cannot itself go stale the way the docs it guards do.
    """

    source = ROOT / "proofs" / "lean" / "juris_lean" / "JurisLean" / "Seams" / "BoundaryClosure.lean"
    lines = source.read_text(encoding="utf-8").splitlines()
    real = [
        i for i, line in enumerate(lines, 1)
        if line.startswith("theorem delimitation_is_not_general")
    ]
    assert len(real) == 1, f"expected one such theorem, found {real}"
    real_line = real[0]

    doc = tmp_path / "cite.md"

    def run() -> subprocess.CompletedProcess:
        return subprocess.run(
            [sys.executable, str(SCRIPT), "--doc", str(doc)],
            cwd=ROOT,
            capture_output=True,
            text=True,
        )

    doc.write_text("see `delimitation_is_not_general:1`\n", encoding="utf-8")
    bad = run()
    assert bad.returncode == 1, bad.stdout + bad.stderr
    assert "delimitation_is_not_general:1" in bad.stdout
    assert f"{real_line}" in bad.stdout, "the report must show where the source really is"

    doc.write_text(f"see `delimitation_is_not_general:{real_line}`\n", encoding="utf-8")
    good = run()
    assert good.returncode == 0, good.stdout + good.stderr
