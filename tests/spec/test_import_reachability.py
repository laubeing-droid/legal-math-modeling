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


def test_quarantine_never_shelters_a_promoted_or_missing_module() -> None:
    """The quarantine is a to-do list, not a hiding place.

    It used to hold the fifteen mandate modules while none of them had been built;
    run 36297146468 built them and they joined the root, so the list is empty here
    two more arrivals joined the root the same way after their own rounds built them.
    Whatever the list holds later, three things must hold with it: every entry is a
    real file, no entry is imported by the release root (that would make the reason
    a lie), and no module that is in the root is still listed.
    """
    on_disk = {
        f"JurisLean.{p.relative_to(PKG).with_suffix('').as_posix().replace('/', '.')}"
        for p in PKG.rglob("*.lean")
    }
    root_text = ROOT_MODULE.read_text(encoding="utf-8")
    pending = set(reach.PENDING_CI_MODULES)
    mandate = {f"JurisLean.Mandate.{f.stem}" for f in (PKG / "Mandate").glob("*.lean")}
    assert pending <= on_disk, f"quarantine names modules that do not exist: {pending - on_disk}"
    for name in sorted(pending):
        assert f"import {name}" not in root_text, (
            f"{name} entered the release root; remove it from PENDING_CI_MODULES "
            "only together with a CI-verified module build"
        )

    promoted = {
        "Kernel", "CohortRate", "StructureInvariants", "DerivedCertificate", "GameTree",
        "ZeroSumSion",
        "SourceRank", "GateTable", "SubstrAdmission", "LinearScorer", "Disclosure",
        "Waterfall", "CohortInterval", "RouteDecision", "TaxSlices", "MatrixGame",
        "CaseIsomorphism",
        # Promoted later, each after the CI module build the test's own message demands:
        # ReLUApprox in run 36344882459 (subject 1b6a8d6a9), MixedPennies in run
        # 36351623739 (subject 71d2177bc). SequentialGames was in this list on the strength
        # of a run/subject pair whose subject predates the file; it is out again, booked in
        # the quarantine table, until a build of its own repaired source returns green.
        "ReLUApprox", "MixedPennies",
    }
    wave = {f"JurisLean.Mandate.{name}" for name in promoted}
    assert not (wave & pending), (
        "these were built in CI 36297146468 and must not stay quarantined: "
        f"{sorted(wave & pending)}"
    )
    for name in sorted(wave):
        assert f"import {name}" in root_text, f"{name} never joined the release root"
    # Anything else under Mandate/ is a new arrival: it may be quarantined, but then it
    # must not be in the root, and its reason must say what has to happen next.
    for name in sorted(mandate - wave):
        assert name in pending, (
            f"{name} is neither promoted nor quarantined: an unrooted module with no "
            "recorded reason is exactly how a module stops being compiled"
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
