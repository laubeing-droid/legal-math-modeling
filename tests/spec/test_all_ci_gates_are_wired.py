"""Every gate in scripts/ci/ must be invoked by CI.

A gate nobody runs is not a gate -- it is a script that looks like a control. This test is the
general form of the `rehearse_regeneration.py` finding (a rehearsal script exists but no workflow
step runs it): the failure mode is not "the script is wrong", it is "the script is unread".
"""

from __future__ import annotations

import re
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
WORKFLOW = ROOT / ".github" / "workflows" / "lean-build.yml"


def ci_scripts() -> list[str]:
    return sorted(p.name for p in (ROOT / "scripts" / "ci").glob("check_*.py"))


def workflow_text() -> str:
    return WORKFLOW.read_text(encoding="utf-8")


def test_gates_exist() -> None:
    assert ci_scripts(), "no check_*.py found -- the glob or the path moved"


def test_every_check_gate_is_invoked_by_ci() -> None:
    text = workflow_text()
    unwired = [name for name in ci_scripts() if f"scripts/ci/{name}" not in text]
    assert not unwired, (
        "these gates exist but no CI step runs them, so they cannot stop anything: "
        + ", ".join(unwired)
    )


def test_wiring_survives_the_block_scalar_style() -> None:
    # The lesson recorded at lean-build.yml's `run: |-` comment: a single-quoted run: line with a
    # `#` inside silently never starts. Guard the shape we rely on rather than trusting YAML.
    text = workflow_text()
    assert re.search(r"run: \|-\n", text), "python-gates step no longer uses a literal block"
    assert "python scripts/ci/check_concept_ledger.py\n" in text


# Scripts that are deliberately NOT CI steps. Each entry is a registered decision with a reason,
# not an oversight: an empty allowlist would be as dishonest as a gate nobody runs.
NOT_A_GATE = {
    # Runs the eight-step regeneration sequence in a clean clone. It is a local rehearsal, kept
    # out of CI on purpose: it needs network + a full lake build, and the six generated accounts
    # are each already `--check`ed in python-gates. Its existence is asserted by
    # tests/spec/test_generated_accounts_have_a_regeneration_step.py.
    "rehearse_regeneration.py",
    # Plans builds; asserts nothing (see its own --all/--module surface).
    "changed_lean_modules.py",
    # Emits run identity only while running inside CI; exits 1 locally by design.
    "build_run_identity.py",
    # Writes docs/master-plan/基线/未覆盖片段登记.md by copying each wave module's own closing
    # comment. It HAS a --check mode and it is deliberately not wired this round: the modules it
    # reads are being edited today, so the register changes on every proof that lands, and a gate
    # that reddens because the work moved forward is a gate people learn to ignore. Wiring it is
    # a recorded debt for after the wave settles, not an oversight -- see the header note the
    # generated register carries.
    "generate_uncovered_fragment_register.py",
    # An acceptance instrument, not a gate: it takes two subjects and reports the theorem-name
    # set difference plus whether each addition is on the landed axiom surface. It cannot run as
    # a CI step because it compares a commit against its ancestor, and the repository has no
    # "this wave added N" contract to enforce -- the number it exists to check lives in prose.
    # Added by the 2026-10-05 acceptance round, which found the ledger claiming 24 additions
    # where the diff is 22.
    "count_added_theorems.py",
}


# Accounts that CI checks indirectly: python-gates runs `pytest tests/`, and these two are
# asserted inside a test rather than invoked as a workflow line. Naming the covering test here
# keeps the claim checkable -- if that test stops mentioning the script, this test goes red.
WIRED_VIA_TESTS = {
    "build_statement_duplication_census.py": "tests/test_statement_duplication_census.py",
    "generate_theorem_manifest.py": "tests/test_theorem_inventory.py",
}


def test_every_ci_script_is_either_wired_or_registered_as_not_a_gate() -> None:
    text = workflow_text()
    unexplained = []
    for path in sorted((ROOT / "scripts" / "ci").glob("*.py")):
        if path.name in NOT_A_GATE or path.name.startswith("test_"):
            continue
        if f"scripts/ci/{path.name}" in text:
            continue
        cover = WIRED_VIA_TESTS.get(path.name)
        if cover and (ROOT / cover).exists() and path.name in (ROOT / cover).read_text(encoding="utf-8"):
            continue
        unexplained.append(path.name)
    assert not unexplained, (
        "scripts/ci/ scripts that neither run in CI, nor have a named covering test, nor appear "
        "in NOT_A_GATE: " + ", ".join(unexplained)
        + " -- either wire them or record why they are not a control"
    )


def test_indirect_wiring_claims_stay_true() -> None:
    # A registered covering test that no longer covers is worse than no registration.
    for script, cover in WIRED_VIA_TESTS.items():
        assert (ROOT / cover).exists(), f"{cover} vanished; update WIRED_VIA_TESTS"
        assert script in (ROOT / cover).read_text(encoding="utf-8"), (
            f"{cover} no longer mentions {script}; it is no longer the gate's cover"
        )
