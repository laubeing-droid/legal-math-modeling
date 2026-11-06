"""A verdict a header claims must be re-readable from bytes in this repository.

Round 72 is the reason: `SequentialGames.lean` carried a verdict whose run/subject pairing was
perfectly real and which nevertheless attested nothing, because the subject predated the file.
Pairing gates cannot catch that; only the round's own bytes can, and only if they are here. So
the rule is: a module whose header cites build rounds must cite at least one round whose landed
`axiom-audit` output actually names that module's declarations. "The job was green" is a colour;
"`'JurisLean.Mandate.X.theorem_name' does not depend on any axioms`" is evidence.

Citations of red rounds stay unconstrained here -- headers are required to name their failures
too, and those are already bound to the run index elsewhere. What this gate demands is that
among everything a header cites, the verdict is somewhere a reader can recompute it.
"""

from __future__ import annotations

import re
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
PKG = ROOT / "proofs" / "lean" / "juris_lean" / "JurisLean"
EVIDENCE = ROOT / "docs" / "formal-release" / "ci-evidence"
RUN = re.compile(r"\brun\s+(\d{8,})", re.I)
NAMESPACE = re.compile(r"^namespace\s+([\w.]+)", re.M)


def _landed_names(run: str) -> set[str] | None:
    """Read full-audit names, or explicitly scoped, byte-bound module output.

    A module build must never enter the full-release axiom-audit path: its
    printed names do not claim coverage of the repository's entire audit root.
    """
    path = EVIDENCE / run / "axiom-audit" / "axiom-audit.raw.txt"
    if run != "41933733392" and path.exists():
        text = path.read_text(encoding="utf-8", errors="replace")
    else:
        # Only this independently downloaded artifact is approved for the scoped
        # fallback. Sidecar hashes alone cannot authenticate an edited log.
        if run != "41933733392":
            return None
        pinned_subject = "1f2f03b77f9dbe46332f3ab3406c7cd1ef32dfd5"
        pinned_module = "JurisLean.CN.Completion20261105.Acceptance"
        pinned_zip = "5363f7fa3d6168ef95470d6c5ac28b6900c60c6afa017ba66f8295ba174c930f"
        pinned_hashes = {
            "changed-module.log": "9820685676137b87edfba538bcd0e7b79cec4e314e2af5481819d79dbca8806e",
            "module-plan.json": "4fe90dd87a06f4adc579ad7acb522324952e38fc8f0403306518d02b9d6eb2a3",
        }
        root = EVIDENCE / run
        sidecar = root / "digests.json"
        log = root / "changed-module.log"
        plan = root / "module-plan.json"
        if not all(p.is_file() for p in (sidecar, log, plan)):
            return None
        metadata = json.loads(sidecar.read_bytes())
        scope = metadata.get("scope", {})
        if (str(metadata.get("run_id")) != run or scope.get("kind") != "changed-module"
                or scope.get("module") != pinned_module or metadata.get("subject") != pinned_subject
                or metadata.get("artifact_id") != 13373097032 or metadata.get("zip_sha256") != pinned_zip):
            return None
        index = json.loads((ROOT / "docs/formal-release/ci_run_index.json").read_bytes())
        identity = next((r for r in index["runs"] if str(r["run_id"]) == run), None)
        if not identity or identity["conclusion"] != "success" or identity["head_sha"] != metadata.get("subject"):
            return None
        snapshots = {"changed-module.log": log.read_bytes(), "module-plan.json": plan.read_bytes()}
        for name, raw in snapshots.items():
            record = next((f for f in metadata["files"] if f["path"] == name), None)
            if (not record or record["sha256"] != hashlib.sha256(raw).hexdigest()
                    or record["bytes"] != len(raw) or hashlib.sha256(raw).hexdigest() != pinned_hashes[name]):
                return None
        targets = {r["module"] for r in json.loads(snapshots["module-plan.json"])["include"]}
        if targets != {pinned_module}:
            return None
        text = snapshots["changed-module.log"].decode("utf-8")
        from scripts.ci.check_axiom_audit_log import parse
        verdict = parse(text)
        if (not verdict["audited_targets"] or verdict["targets_with_sorryAx"]
                or verdict["targets_outside_standard_axioms"] or verdict["conflicting_target_lines"]):
            return None
        # Strip only diagnostic location prefixes, after validating the same bytes.
        text = re.sub(r"^info: [^\n]*?:\d+:\d+: ", "", text, flags=re.M)
        # Dependency names are not acceptance attestations for unrelated modules.
        return {line.split("'", 2)[1] for line in text.splitlines()
                if line.startswith("'" + pinned_module + ".") and "'" in line[1:]}
    out: set[str] = set()
    for line in text.splitlines():
        if line.startswith("'") and "'" in line[1:]:
            out.add(line.split("'", 2)[1])
    return out


def _modules() -> list[tuple[str, str, list[str]]]:
    """(stem, namespace, cited runs) for every package module whose header cites runs."""
    rows = []
    for path in sorted(PKG.rglob("*.lean")):
        text = path.read_text(encoding="utf-8", errors="replace")
        header = _header(text)
        runs = sorted(set(RUN.findall(header)))
        if not runs:
            continue
        ns = NAMESPACE.search(text)
        rows.append((path.stem, ns.group(1) if ns else "", runs))
    return rows


def _header(text: str) -> str:
    i = text.find("/-!")
    j = text.find("-/", i)
    return text[i:j] if 0 <= i < j else text[:4000]


def test_the_rule_reads_real_headers_and_real_evidence() -> None:
    rows = _modules()
    assert len(rows) >= 15, (
        f"only {len(rows)} modules cite build rounds; either headers stopped attesting or "
        "this gate stopped reading them"
    )
    landed = {p.parent.parent.name for p in EVIDENCE.glob("*/axiom-audit/axiom-audit.raw.txt")}
    assert len(landed) >= 10, (
        f"only {len(landed)} rounds have landed audit bytes, so the reference set is too thin "
        "to demand anything"
    )


def test_every_attesting_header_cites_at_least_one_landed_round() -> None:
    unsatisfied: list[str] = []
    for stem, namespace, runs in _modules():
        prefix = f"{namespace}." if namespace else ""
        if not any(
            (names := _landed_names(run)) is not None
            and any(n.startswith(prefix) for n in names)
            for run in runs
        ):
            unsatisfied.append(f"{stem}: cites {runs}, none landed names {prefix}*")
    assert not unsatisfied, (
        "these headers claim build verdicts that no landed audit text in this repository can "
        "re-read; land the round with `build_ci_run_index.py --fetch-evidence <id>` or correct "
        "the header:\n  " + "\n  ".join(unsatisfied)
    )


def test_the_gate_can_actually_go_red() -> None:
    """Drive the comparison with a module whose runs are known not to cover it."""
    stem, namespace, runs = next(
        (s, n, r) for s, n, r in _modules() if s == "PureNash"
    )
    assert runs, "PureNash's header stopped citing rounds; update this test"
    prefix = f"{namespace}."
    wrong = "36298572193"  # a real landed round from a different era
    names = _landed_names(wrong)
    assert names is not None and not any(n.startswith(prefix) for n in names), (
        "the chosen wrong round now covers this module, so the negative case proves nothing"
    )


def test_scoped_module_evidence_is_not_full_audit_and_rejects_mutation():
    from unittest.mock import patch
    run = "41933733392"
    assert not (EVIDENCE / run / "axiom-audit/axiom-audit.raw.txt").exists()
    names = _landed_names(run)
    assert names and all(n.startswith("JurisLean.CN.Completion20261105.Acceptance.") for n in names)
    original_read = Path.read_bytes
    for filename in ("changed-module.log", "module-plan.json"):
        target = EVIDENCE / run / filename
        def corrupted_read(path):
            raw = original_read(path)
            return raw + b"\ncorrupted" if path == target else raw
        with patch.object(Path, "read_bytes", corrupted_read):
            assert _landed_names(run) is None


def test_scoped_log_and_sidecar_cannot_be_rewritten_together():
    from unittest.mock import patch
    root = EVIDENCE / "41933733392"
    original_read = Path.read_bytes
    fake = original_read(root / "changed-module.log") + b"\ninfo: 'JurisLean.CN.Completion20261105.Acceptance.fake' depends on axioms: [sorryAx]\n"
    metadata = json.loads(original_read(root / "digests.json"))
    for record in metadata["files"]:
        if record["path"] == "changed-module.log":
            record.update(sha256=hashlib.sha256(fake).hexdigest(), bytes=len(fake))
    def corrupted_read(path):
        if path == root / "changed-module.log":
            return fake
        if path == root / "digests.json":
            return json.dumps(metadata).encode()
        return original_read(path)
    with patch.object(Path, "read_bytes", corrupted_read):
        assert _landed_names("41933733392") is None


def test_scoped_axiom_verdict_is_required():
    from unittest.mock import patch
    bad = {"audited_targets": 1, "targets_with_sorryAx": {"fake": ["sorryAx"]},
           "targets_outside_standard_axioms": {}, "conflicting_target_lines": {}}
    with patch("scripts.ci.check_axiom_audit_log.parse", return_value=bad):
        assert _landed_names("41933733392") is None


def test_scoped_run_cannot_be_promoted_by_adding_a_full_audit_path():
    from unittest.mock import patch
    with patch.object(Path, "exists", return_value=True):
        with patch.object(Path, "read_text", side_effect=AssertionError("untrusted full-audit path")):
            names = _landed_names("41933733392")
    assert names and all(n.startswith("JurisLean.CN.Completion20261105.Acceptance.") for n in names)
