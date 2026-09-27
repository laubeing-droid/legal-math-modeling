"""The declaration-collision gate must bite on the failure it was written for.

`check_import_reachability.py --write` added `import JurisLean.TypedAttack` to the
root's generated block while `JurisLean.AttackDecision` was already imported there;
both declared `JurisLean.isSelfAttack`, so `lake build` rejected the root
(`environment already contains 'JurisLean.isSelfAttack' from JurisLean.AttackDecision`,
CI run 36290409329). These tests pin the scanner's namespace handling and prove the
gate fails when the collision is present.
"""

from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
SCRIPT = ROOT / "scripts" / "ci" / "check_declaration_collisions.py"
sys.path.insert(0, str(ROOT / "scripts"))

from lean_grammar import declarations  # noqa: E402

TWO_NAMESPACES = """
namespace JurisLean.Alpha
def isSelfAttack (a : Nat) : Prop := True
theorem useful : True := trivial
end JurisLean.Alpha
namespace JurisLean.Beta
def isSelfAttack (a : Nat) : Prop := True
end JurisLean.Beta
"""

NESTED = """
namespace JurisLean
namespace Mandate
def value : Nat := 0
end Mandate
def value : Nat := 1
end JurisLean
"""


def test_namespace_prefixes_are_tracked():
    names = [(d["keyword"], d["name"]) for d in declarations(TWO_NAMESPACES, namespace=True)]
    assert ("def", "JurisLean.Alpha.isSelfAttack") in names
    assert ("def", "JurisLean.Beta.isSelfAttack") in names
    # Same identifier, different namespaces: two distinct environment names.
    assert len(names) == len(set(names))


def test_nested_namespaces_do_not_share_a_prefix():
    names = {d["name"] for d in declarations(NESTED, namespace=True)}
    assert names == {"JurisLean.Mandate.value", "JurisLean.value"}


def test_unqualified_scan_keeps_local_names():
    names = {d["name"] for d in declarations(NESTED)}
    assert names == {"value"}


def test_doc_and_block_comments_do_not_declare():
    text = """/-! `def isSelfAttack` in prose -/
/-- def ghost : Nat -/
def real : Nat := 0
"""
    assert {d["name"] for d in declarations(text)} == {"real"}


def _mini_repo(tmp_path: Path, second_body: str) -> Path:
    pkg = tmp_path / "proofs" / "lean" / "juris_lean" / "JurisLean"
    pkg.mkdir(parents=True)
    (pkg / "First.lean").write_text(
        "namespace JurisLean\ndef shared : Nat := 0\nend JurisLean\n", encoding="utf-8"
    )
    (pkg / "Second.lean").write_text(second_body, encoding="utf-8")
    (pkg.parent / "JurisLean.lean").write_text(
        "import JurisLean.First\nimport JurisLean.Second\n", encoding="utf-8"
    )
    return tmp_path


def test_gate_fails_when_two_imported_modules_share_a_name(tmp_path):
    repo = _mini_repo(
        tmp_path, "namespace JurisLean\ndef shared : Nat := 1\nend JurisLean\n"
    )
    out = repo / "out.json"
    proc = subprocess.run(
        [sys.executable, str(SCRIPT), "--repo", str(repo), "--root", "JurisLean",
         "--json", str(out), "--check"],
        capture_output=True, text=True, encoding="utf-8", cwd=str(ROOT),
    )
    assert proc.returncode == 1, proc.stdout + proc.stderr
    payload = json.loads(out.read_text(encoding="utf-8"))
    assert payload["collision_count"] == 1
    assert payload["collisions"]["JurisLean.shared"][0]["module"] == "JurisLean.First"


def test_gate_passes_when_the_duplicate_lives_elsewhere(tmp_path):
    repo = _mini_repo(
        tmp_path, "namespace JurisLean.Other\ndef shared : Nat := 1\nend JurisLean.Other\n"
    )
    out = repo / "out.json"
    proc = subprocess.run(
        [sys.executable, str(SCRIPT), "--repo", str(repo), "--root", "JurisLean",
         "--json", str(out), "--check"],
        capture_output=True, text=True, encoding="utf-8", cwd=str(ROOT),
    )
    assert proc.returncode == 0, proc.stdout + proc.stderr
    assert json.loads(out.read_text(encoding="utf-8"))["collision_count"] == 0


def test_gate_passes_when_the_other_module_is_not_imported(tmp_path):
    """A name may repeat across modules that no build ever imports together."""
    repo = _mini_repo(
        tmp_path, "namespace JurisLean\ndef shared : Nat := 1\nend JurisLean\n"
    )
    root = repo / "proofs" / "lean" / "juris_lean" / "JurisLean.lean"
    root.write_text("import JurisLean.First\n", encoding="utf-8")
    proc = subprocess.run(
        [sys.executable, str(SCRIPT), "--repo", str(repo), "--root", "JurisLean",
         "--check"],
        capture_output=True, text=True, encoding="utf-8", cwd=str(ROOT),
    )
    assert proc.returncode == 0, proc.stdout + proc.stderr


def test_the_real_root_closure_is_collision_free():
    out = ROOT / "build" / "declaration_collisions.json"
    out.parent.mkdir(exist_ok=True)
    proc = subprocess.run(
        [sys.executable, str(SCRIPT), "--repo", str(ROOT), "--root", "JurisLean",
         "--json", str(out), "--check"],
        capture_output=True, text=True, encoding="utf-8", cwd=str(ROOT),
    )
    assert proc.returncode == 0, proc.stdout + proc.stderr
    payload = json.loads(out.read_text(encoding="utf-8"))
    # 233 modules reachable; the gate is not vacuous because the mini-repo tests above
    # show it reporting 1 collision for the same shape of defect.
    assert payload["modules_in_closure"] > 200
    assert payload["collision_count"] == 0


def test_the_historical_collision_was_renamed_not_deleted():
    attack = ROOT / "proofs" / "lean" / "juris_lean" / "JurisLean" / "AttackDecision.lean"
    typed = ROOT / "proofs" / "lean" / "juris_lean" / "JurisLean" / "TypedAttack.lean"
    attack_names = {d["name"] for d in declarations(attack.read_text(encoding="utf-8"),
                                                   namespace=True)}
    typed_names = {d["name"] for d in declarations(typed.read_text(encoding="utf-8"),
                                                  namespace=True)}
    assert "JurisLean.isSelfAttack" in attack_names
    assert "JurisLean.isTypedSelfAttack" in typed_names
    assert not attack_names & typed_names
    assert "JurisLean.isSelfAttack" not in typed_names
