"""The neural backport's provenance record must always match the tree's reality.

`JurisLean/External/NeuralNetworkProofs/` is a CROSS-PIN backport (mathlib
v4.32.0-rc1 -> v4.30.0), so unlike the same-pin ports byte-faithfulness is not
an invariant: drift repairs are expected. What must never happen is the record
and the tree disagreeing silently -- a file that was repaired without logging
the repair, or a record claiming repairs that do not exist. This gate checks:

* every `.lean` under `External/NeuralNetworkProofs/` is listed, and vice versa;
* for each file, stripping the header and reversing the import rewrite either
  reproduces the recorded upstream sha256 (unadapted) or the record says
  `adapted: true` **and** carries a non-empty, non-placeholder adaptation log;
* `adapted` is exactly the reconstruction outcome -- a stale flag is a finding;
* the header claims no attestation and no `subject <hash>` wording (the pinned
  upstream revision is a foreign commit, which the misattribution gate would
  rightly reject).
"""

from __future__ import annotations

import hashlib
import json
from pathlib import Path

import pytest

from tests.spec.test_run_subject_pairs_are_not_misattributed import HEADER_SUBJECT

ROOT = Path(__file__).resolve().parents[2]
EXTERNAL = ROOT / "proofs" / "lean" / "juris_lean" / "JurisLean" / "External" / "NeuralNetworkProofs"
PROVENANCE = EXTERNAL / "PROVENANCE.json"

REVERSE = (
    ("import JurisLean.External.NeuralNetworkProofs.", "import NeuralNetworkProofs."),
)


def _doc() -> dict:
    return json.loads(PROVENANCE.read_text(encoding="utf-8"))


def _reverse_imports(text: str) -> str:
    out = []
    for line in text.split("\n"):
        for old, new in REVERSE:
            if line.startswith(old):
                line = new + line[len(old):]
                break
        out.append(line)
    return "\n".join(out)


def _strip_header(text: str, marker: str) -> str:
    assert marker in text, "backport header marker missing"
    lines = text.split("\n")
    first = lines.index("-/")
    assert marker in "\n".join(lines[:first]), "the first '-/' line closes the header"
    return "\n".join(lines[first + 1:])


def _reconstruct(rec: dict, marker: str) -> str:
    text = (ROOT / rec["repo_path"]).read_text(encoding="utf-8")
    return _reverse_imports(_strip_header(text, marker))


PLACEHOLDER_LOG = ("", "n/a", "todo", "tbd")


def test_every_backport_file_is_listed_and_vice_versa() -> None:
    listed = {rec["repo_path"] for rec in _doc()["files"]}
    on_disk = {
        p.relative_to(ROOT).as_posix()
        for p in EXTERNAL.rglob("*.lean")
    }
    assert listed == on_disk, (
        f"provenance record and tree disagree: unlisted={sorted(on_disk - listed)} "
        f"missing={sorted(listed - on_disk)}"
    )


def test_adapted_flag_matches_reconstruction_and_drift_is_logged() -> None:
    doc = _doc()
    stale = []
    unlogged = []
    for rec in doc["files"]:
        upstream = _reconstruct(rec, doc["header_marker"])
        digest = hashlib.sha256(upstream.encode("utf-8")).hexdigest()
        drifted = digest != rec["upstream_sha256"]
        if drifted != rec["adapted"]:
            stale.append(
                f"{rec['repo_path']}: record says adapted={rec['adapted']}, "
                f"reconstruction says drifted={drifted}"
            )
        if drifted:
            log = [str(e).strip().lower() for e in rec.get("adaptations", [])]
            if not log or any(e in PLACEHOLDER_LOG for e in log):
                unlogged.append(rec["repo_path"])
    assert not stale, f"provenance flags out of sync with the tree: {stale}"
    assert not unlogged, f"drifted files without a real adaptation log: {unlogged}"


def test_unadapted_files_reproduce_upstream_bytes() -> None:
    """While a file is still unadapted it must stay byte-faithful.

    This is what makes `adapted: false` meaningful: the flag is not a vibe, it is
    the statement that strip+reverse still reproduces the upstream sha256, and a
    repair that forgets to flip the flag fails the previous test while a file
    that drifted without any repair at all fails here first.
    """
    doc = _doc()
    bad = []
    for rec in doc["files"]:
        if rec["adapted"]:
            continue
        upstream = _reconstruct(rec, doc["header_marker"])
        digest = hashlib.sha256(upstream.encode("utf-8")).hexdigest()
        if digest != rec["upstream_sha256"]:
            bad.append(rec["repo_path"])
    assert not bad, f"files marked unadapted no longer match upstream: {bad}"


def test_the_backport_carries_no_attestation_wording() -> None:
    for path in sorted(EXTERNAL.rglob("*.lean")):
        text = path.read_text(encoding="utf-8")
        header = text[: text.index("\n-/\n")]
        assert "built green" not in header and "attested" not in header, path
        assert not HEADER_SUBJECT.search(header), (
            f"{path.name}: header uses subject-citation wording, which the "
            "misattribution gate would read as an attestation of a foreign commit"
        )


def test_the_record_pins_the_upstream_revision_and_license() -> None:
    doc = _doc()
    src = doc["sources"]["neuralnetworkproofs"]
    assert src["license"] == "Apache-2.0"
    assert len(src["revision"]) == 40
    assert (EXTERNAL / "LICENSE").exists(), "Apache-2.0 requires the license text beside the copy"


def test_no_upstream_import_roots_survive() -> None:
    offenders = []
    for path in sorted(EXTERNAL.rglob("*.lean")):
        for line in path.read_text(encoding="utf-8").split("\n"):
            if line.strip().startswith("import NeuralNetworkProofs."):
                offenders.append(f"{path.name}: {line.strip()}")
    assert not offenders, f"un-rewritten upstream imports: {offenders[:5]}"


def test_leshno_headline_is_on_the_audit_surface() -> None:
    """The point of the backport is a named, auditable theorem, not just files.

    `leshno_dense_iff` is the carrier the ReLU instantiation will cite; if the
    audit surface loses it, the port stopped being about the theorem.
    """
    audit = (ROOT / "proofs" / "lean" / "juris_lean" / "JurisLean" / "AxiomAudit.lean").read_text(
        encoding="utf-8"
    )
    assert "#print axioms UniversalApproximation.Leshno.leshno_dense_iff" in audit
    assert "#print axioms UniversalApproximation.Leshno.leshno_dense" in audit


@pytest.mark.parametrize("marker", ["sorry", "admit", "native_decide"])
def test_backport_files_carry_no_forbidden_tokens(marker: str) -> None:
    """The upstream claims sorry-free; the backport must not regress that.

    Comments are stripped first (mirroring the guard scan's intent) so English
    prose about the tokens cannot false-positive. CI's guard scan and
    elaboration remain the authority; this catches a repair that 'fixes' drift
    by cheating before it reaches them.
    """
    import re
    import sys

    sys.path.insert(0, str(ROOT / "scripts"))
    from lean_grammar import strip_comments

    for path in sorted(EXTERNAL.rglob("*.lean")):
        depth = 0
        for line in path.read_text(encoding="utf-8").splitlines():
            code, depth = strip_comments(line, depth)
            if re.search(rf"\b{marker}\b", code):
                assert False, f"{path.name}: forbidden token {marker!r} in {code.strip()[:80]}"
