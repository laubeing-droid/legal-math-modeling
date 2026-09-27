"""Gate: the single `lake build` root must reach every non-driver module.

Audit P1-12 started as "FullMath is imported by nothing". Measured properly, 109
of the package's modules were outside the root's import closure, so a plain
`lake build` elaborated far less than the theorem count in the paper implies; only
the CI all-module plan covered the rest, silently.
"""

from __future__ import annotations

import importlib.util
import subprocess
import tempfile
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
TOOL = ROOT / "scripts" / "ci" / "check_import_reachability.py"
LEAN_BASE = ROOT / "proofs" / "lean" / "juris_lean"
PKG = LEAN_BASE / "JurisLean"
ROOT_MODULE = PKG.parent / "JurisLean.lean"
AGGREGATOR = PKG / "FullMath" / "All.lean"

spec = importlib.util.spec_from_file_location("reach", TOOL)
assert spec and spec.loader
reach = importlib.util.module_from_spec(spec)
spec.loader.exec_module(reach)


def test_default_mode_passes() -> None:
    proc = subprocess.run([sys.executable, str(TOOL)], cwd=ROOT,
                          capture_output=True, text=True)
    assert proc.returncode == 0, proc.stdout + proc.stderr


def test_root_has_a_reachability_block() -> None:
    text = ROOT_MODULE.read_text(encoding="utf-8")
    assert reach.ROOT_BLOCK_BEGIN in text
    assert reach.ROOT_BLOCK_END in text


def test_block_is_what_the_base_root_needs() -> None:
    """The committed block must equal the computed closure gap, no more, no less."""
    root_text = ROOT_MODULE.read_text(encoding="utf-8")
    before, _after = reach.split_root_block(root_text)
    inner = root_text.split(reach.ROOT_BLOCK_BEGIN, 1)[1].split(reach.ROOT_BLOCK_END, 1)[0]
    listed = sorted(
        line[len("import "):].strip() for line in inner.splitlines()
        if line.startswith("import JurisLean.")
    )

    with tempfile.TemporaryDirectory() as td:
        base = Path(td) / "JurisLean.lean"
        base.write_text(before, encoding="utf-8")
        mods = reach.modules()
        mods["JurisLean"] = base
        gap = reach.unreachable_from(mods)

    assert listed == sorted(gap), (
        f"block lists {len(listed)} modules, the base root needs {len(gap)}; "
        "run scripts/ci/check_import_reachability.py --write"
    )


def test_aggregator_lists_every_fullmath_module() -> None:
    mods = reach.modules()
    on_disk = {m for m in mods if m.startswith("JurisLean.FullMath.") and m != "JurisLean.FullMath.All"}
    listed = {
        line[len("import "):].strip()
        for line in AGGREGATOR.read_text(encoding="utf-8").splitlines()
        if line.startswith("import ")
    }
    assert listed == on_disk, listed.symmetric_difference(on_disk)


def test_allow_list_names_all_exist_and_are_reasoned() -> None:
    mods = reach.modules()
    for name, reason in reach.ALLOWED_UNREACHABLE.items():
        assert name in mods, f"allow-list entry no longer exists: {name}"
        assert len(reason) > 8, name


def test_mandate_quarantine_is_exactly_the_pending_wave() -> None:
    """The quarantine covers precisely the Mandate tree, nothing more, nothing less."""
    on_disk = {
        f"JurisLean.Mandate.{f.stem}" for f in (PKG / "Mandate").glob("*.lean")
    }
    assert set(reach.PENDING_CI_MODULES) == on_disk, (
        set(reach.PENDING_CI_MODULES) ^ on_disk
    )
    assert len(on_disk) >= 10
    root_text = ROOT_MODULE.read_text(encoding="utf-8")
    for name in reach.PENDING_CI_MODULES:
        assert f"import {name}" not in root_text, (
            f"{name} entered the release root; remove it from PENDING_CI_MODULES "
            "only together with a CI-verified module build"
        )


def test_probability_line_is_now_reachable() -> None:
    """The specific orphan the audit found must stay fixed."""
    mods = reach.modules()
    reached = reach.closure("JurisLean", mods)
    prob = [m for m in mods if m.startswith("JurisLean.FullMath.Probability.")]
    assert prob, "probability tree vanished from the package"
    assert set(prob) <= reached, sorted(set(prob) - reached)
    assert "JurisLean.BusinessRoot.Analytics" in reached
    assert "JurisLean.BanachCertificate" in reached or not (PKG / "BanachCertificate.lean").exists()


def test_generated_files_never_place_an_import_after_a_command() -> None:
    """The aggregator used to lead with a `/-!` module doc, which is itself a command.

    Lean then rejects every `import` in the file, so the 64-module tree the root was
    wired to reach silently stopped compiling: a generator that emits a legal-looking
    header can produce a file the compiler refuses.
    """

    transparent = ("/-", "/-!", "-/", "--")
    offenders = []
    for path in (AGGREGATOR, ROOT_MODULE):
        seen_command = False
        for line in path.read_text(encoding="utf-8").splitlines():
            stripped = line.strip()
            if not stripped or stripped.startswith(transparent):
                continue
            if stripped.startswith("import "):
                if seen_command:
                    offenders.append(f"{path.name}: {stripped}")
            else:
                seen_command = True
    assert not offenders, f"imports after a command: {offenders}"
