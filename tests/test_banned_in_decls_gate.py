"""The §9.1 self-check is a gate, not a hand-run grep.

Three things this pins down, each of which was a live failure mode during
construction:

* a violation has to be attributed to a declaration, and the gate has to actually
  fire when one exists -- a scanner that always returns zero would pass the tree
  and pass a review;
* the banned words that appear **inside comments** must not count, because
  `Genealogy/TSpectrum/Batch1.lean` lists them one per line as a checklist, so a
  raw grep reports violations the source does not contain;
* a file that `git` has never seen must still be scanned, because the CI guard
  scan takes `git ls-files` and a brand-new seam file is exactly when a `sorry`
  is likeliest.
"""

import re
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
SCRIPT = ROOT / "scripts" / "ci" / "check_banned_in_decls.py"

sys.path.insert(0, str(ROOT / "scripts" / "ci"))

from check_banned_in_decls import scan_file  # noqa: E402

BLOCK_OPEN = "/-"
BLOCK_CLOSE = "-/"


def write(tmp_path: Path, name: str, lines: list[str]) -> Path:
    path = tmp_path / name
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")
    return path


def test_a_sorry_in_a_proof_body_is_a_violation(tmp_path):
    path = write(
        tmp_path,
        "Fake.lean",
        ["namespace X", "", "theorem hole (n : Nat) : n = n := by sorry", "", "end X"],
    )
    found, inspected = scan_file(path)
    assert inspected == 1
    assert len(found) == 1, found
    assert "Fake.lean:3" in found[0]
    assert "in hole" in found[0]


def test_a_true_theorem_evasion_is_a_violation(tmp_path):
    path = write(tmp_path, "Triv.lean", ["theorem trivial_fake : True := by trivial"])
    found, _ = scan_file(path)
    assert len(found) == 1, found
    assert "theorem-of-True evasion" in found[0]


def test_a_top_level_axiom_before_any_declaration_is_not_missed(tmp_path):
    path = write(
        tmp_path,
        "Pre.lean",
        ["import Init", "", "axiom myMagic : 1 = 2", "", "theorem ok : 1 = 1 := rfl"],
    )
    found, inspected = scan_file(path)
    assert inspected == 2, "the axiom line must count as a declaration boundary"
    assert len(found) == 1, found
    assert "axiom declaration" in found[0]


def test_banned_words_inside_a_block_comment_are_not_violations(tmp_path):
    path = write(
        tmp_path,
        "Checked.lean",
        [
            BLOCK_OPEN,
            "sorry",
            "admit",
            "native_decide",
            "axiom",
            BLOCK_CLOSE,
            "",
            "theorem ok : 1 = 1 := rfl",
        ],
    )
    found, inspected = scan_file(path)
    assert found == [], found
    assert inspected == 1


def test_banned_words_inside_a_line_comment_are_not_violations(tmp_path):
    path = write(
        tmp_path,
        "Line.lean",
        ["-- sorry / admit / native_decide are listed as forbidden", "theorem ok : 1 = 1 := rfl"],
    )
    found, inspected = scan_file(path)
    assert found == [], found
    assert inspected == 1


def test_the_working_tree_passes_and_covers_files_git_has_never_seen():
    """The committed gate run: zero violations, and a scope no narrower than git's."""

    proc = subprocess.run(
        [sys.executable, str(SCRIPT)], cwd=ROOT, capture_output=True, text=True
    )
    assert proc.returncode == 0, proc.stdout + proc.stderr
    tracked = subprocess.run(
        ["git", "ls-files", "*.lean"], cwd=ROOT, capture_output=True, text=True
    )
    tracked_count = len([p for p in tracked.stdout.split() if p.startswith("proofs/")])
    reported = int(re.search(r"passed: (\d+) files", proc.stdout).group(1))
    assert reported >= tracked_count, (
        f"the working-tree scan reported {reported} files but git tracks "
        f"{tracked_count}; the scan scope has narrowed"
    )
    assert "0 violations" in proc.stdout


def test_reviewed_admission_identifiers_are_byte_bound(tmp_path):
    from scripts.scan_lean_guards import scan_file as guard_scan
    from scripts.scan_lean_guards import reviewed_admission_identifier_lines
    for rel, expected in [("CN/World.lean", {65}), ("CN/Completion20261105/Runtime.lean", {17, 35, 47})]:
        source = ROOT / "proofs/lean/juris_lean/JurisLean" / rel
        assert reviewed_admission_identifier_lines(source, source.read_bytes()) == expected
        assert scan_file(source)[0] == []
        assert guard_scan(source)[0] == []
        copy = tmp_path / source.name
        copy.write_bytes(source.read_bytes())
        assert reviewed_admission_identifier_lines(copy, copy.read_bytes()) == set()
        assert any("admit tactic" in v for v in scan_file(copy)[0])
        assert any("admit tactic" in v for v in guard_scan(copy)[0])


def test_admit_tactics_remain_forbidden_in_identifier_contexts(tmp_path):
    from scripts.scan_lean_guards import scan_file as guard_scan
    samples = [
        "def admit : Nat := by admit",
        "theorem hole : 1 = 2 := by admit",
        "inductive X\n  | mk : (by admit : Type) -> X",
        "inductive X\n  | admit\ntheorem hole : 1 = 2 := by\n  admit",
        'def f : String := by\n  let s := "admit"\n  admit',
        "theorem hole : 1 = 2 := by first | admit | rfl",
        "inductive X\n | mk : (by first\n | admit\n : Type) -> X",
        "inductive X (n : Nat := by first\n | admit\n) where\n | mk : X n",
        'def hole : String := s!"{(by admit : Nat)}"',
        "inductive X\n  | mk\nprivate theorem hole : 1 = 2 := by\n  first\n  | admit\n  | rfl",
        "inductive X\n  | mk\n@[simp] theorem hole : 1 = 2 := by\n  first\n  | admit\n  | rfl",
    ]
    for i, sample in enumerate(samples):
        path = write(tmp_path, f"Hole{i}.lean", sample.splitlines())
        assert any("admit tactic" in v for v in scan_file(path)[0]), sample
        assert any("admit tactic" in v for v in guard_scan(path)[0]), sample


def test_guard_hash_and_scan_share_one_byte_snapshot():
    from unittest.mock import patch
    from scripts.scan_lean_guards import scan_file as guard_scan
    source = ROOT / "proofs/lean/juris_lean/JurisLean/CN/World.lean"
    original = source.read_bytes()
    changed = original.replace(b"def admit (s : Sit) : Sit :=", b"def admit (s : Sit) : Sit := by admit --")
    for scanner in (scan_file, guard_scan):
        with patch.object(Path, "read_bytes", side_effect=[original, changed]) as read:
            with patch.object(Path, "read_text", side_effect=AssertionError("second source read")):
                assert scanner(source)[0] == []
            assert read.call_count == 1
        with patch.object(Path, "read_bytes", return_value=changed) as read:
            assert any("admit tactic" in v for v in scanner(source)[0])
            assert read.call_count == 1
