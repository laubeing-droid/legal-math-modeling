"""The external ports must remain byte-faithful to their pinned upstream revisions.

`JurisLean/External/` holds ported copies of two external Lean libraries (see
`JurisLean/External/PROVENANCE.md`). The whole point of the port is that the
repository does **not** build its own proof islands for the three proof-level
gaps: the theorems must be the literature carriers' theorems, verbatim. So the
claim "only the header and the import roots were rewritten" is load-bearing, and
this gate checks it mechanically:

* every `.lean` under `External/` is listed in `PROVENANCE.json`, and vice versa;
* for each file, stripping the provenance header and reversing the documented
  import rewrite must reproduce bytes whose sha256 equals the recorded upstream
  sha256 (the upstream hashes were computed from `git show <rev>:<path>` in
  clones at exactly the pinned revisions, by `scripts/port_external_same_pin.py`,
  which refuses any other revision);
* the recorded revisions pin this repository's exact mathlib revision, and the
  header names the revision it was ported from.

If this gate fails, someone edited a port in place: either revert the edit, or
deliberately re-port from a new pinned revision and update PROVENANCE.json with
a fresh record -- silently diverging copies are how a "carrier" turns back into
a home-made proof wearing someone else's name.
"""

from __future__ import annotations

import hashlib
import json
from pathlib import Path

from tests.spec.test_run_subject_pairs_are_not_misattributed import HEADER_SUBJECT

ROOT = Path(__file__).resolve().parents[2]
EXTERNAL = ROOT / "proofs" / "lean" / "juris_lean" / "JurisLean" / "External"
PROVENANCE = EXTERNAL / "PROVENANCE.json"

# Exact inverse of scripts/port_external_same_pin.py:REWRITES, longest first.
REVERSE = (
    ("import JurisLean.External.GameTheory.Math.", "import Math."),
    ("import JurisLean.External.GameTheory.Semantics.", "import Semantics."),
    ("import JurisLean.External.GameTheory.", "import GameTheory."),
    ("import JurisLean.External.FixedPointTheorems.", "import FixedPointTheorems."),
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
    assert marker in text, "provenance header marker missing"
    lines = text.split("\n")
    first = lines.index("-/")  # header terminator; header is always prepended
    assert marker in "\n".join(lines[:first]), "the first '-/' line closes the header"
    return "\n".join(lines[first + 1:])


def test_every_external_lean_file_is_listed_and_vice_versa() -> None:
    listed = {rec["repo_path"] for rec in _doc()["files"]}
    on_disk = {
        p.relative_to(ROOT).as_posix()
        for p in EXTERNAL.rglob("*.lean")
    }
    assert listed == on_disk, (
        f"provenance record and tree disagree: unlisted={sorted(on_disk - listed)} "
        f"missing={sorted(listed - on_disk)}"
    )


def test_each_port_reproduces_its_upstream_bytes() -> None:
    doc = _doc()
    bad = []
    for rec in doc["files"]:
        text = (ROOT / rec["repo_path"]).read_text(encoding="utf-8")
        upstream = _reverse_imports(_strip_header(text, doc["header_marker"]))
        digest = hashlib.sha256(upstream.encode("utf-8")).hexdigest()
        if digest != rec["upstream_sha256"]:
            bad.append(rec["repo_path"])
    assert not bad, f"ports that no longer match their upstream sha256: {bad}"


def test_no_upstream_import_roots_survive_in_the_ports() -> None:
    """A port whose imports were never rewritten would still hash-verify.

    The upstream-sha256 gate derives its expected hash by *reversing* the
    rewrite, so a file whose `import GameTheory.Concepts.MixedExtension` line
    was never rewritten in the first place round-trips to itself and passes.
    The first generated batch had exactly that bug (written with `original`
    instead of `rewritten`); this check makes it impossible to commit again:
    any upstream-rooted import left in a port fails here, while a broken
    `JurisLean.External.` import fails CI at elaboration.
    """
    offenders = []
    for path in sorted(EXTERNAL.rglob("*.lean")):
        text = path.read_text(encoding="utf-8")
        for line in text.split("\n"):
            stripped = line.strip()
            for old in ("import GameTheory.", "import Math.", "import Semantics.",
                        "import FixedPointTheorems."):
                if stripped.startswith(old):
                    offenders.append(f"{path.name}: {stripped}")
    assert not offenders, f"un-rewritten upstream imports: {offenders[:5]}"


def test_the_port_carries_no_attestation_wording() -> None:
    """A port awaiting its first CI build may not already claim one.

    This is the `Mandate/SequentialGames.lean` lesson (ledger round 71-72) applied
    ahead of time: no header here may name a run or bind a verdict, and none may
    use the `subject <hash>` wording that the pairing gate reads as an
    attestation -- the pinned upstream revisions are foreign commits, which that
    gate would correctly reject as unknown.
    """
    for path in sorted(EXTERNAL.rglob("*.lean")):
        text = path.read_text(encoding="utf-8")
        header = text[: text.index("\n-/\n")]
        assert "built green" not in header and "attested" not in header, path
        assert not HEADER_SUBJECT.search(header), (
            f"{path.name}: header uses subject-citation wording, which the "
            "misattribution gate would read as an attestation of a foreign commit"
        )


def test_recorded_revisions_pin_this_repositorys_mathlib() -> None:
    doc = _doc()
    manifest = (ROOT / "proofs" / "lean" / "juris_lean" / "lake-manifest.json").read_text(
        encoding="utf-8"
    )
    pin = doc["mathlib_pin_checked"]
    assert pin in manifest, "recorded mathlib pin no longer matches the lake manifest"
    for source in doc["sources"].values():
        assert source["license"] == "MIT"
        assert len(source["revision"]) == 40 and source["revision"].strip("0123456789abcdef") == ""
