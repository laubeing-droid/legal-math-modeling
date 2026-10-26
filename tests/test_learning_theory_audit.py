"""Keep the original-theory proof receipt bound to its exact CI source and names."""

import hashlib
import json
import re
import subprocess
from pathlib import Path

from scripts.ci import check_axiom_audit_log as audit

ROOT = Path(__file__).resolve().parents[1]
EVIDENCE = ROOT / "docs/formal-release/evidence/learning-theory-20261027"
RECEIPT = json.loads((EVIDENCE / "verification.json").read_text(encoding="utf-8"))


def test_learning_types_and_axioms_name_the_same_fourteen_targets():
    driver = (ROOT / RECEIPT["driver_path"]).read_text(encoding="utf-8")
    expected = set(RECEIPT["named_theorems_full"])
    assert len(expected) == RECEIPT["named_count"] == 14
    for command in ("#check", "#print axioms"):
        names = re.findall(rf"^{command} (\S+)$", driver, re.MULTILINE)
        assert len(names) == len(set(names)) == 14
        assert set(names) == expected
    raw = (EVIDENCE / "axiom-audit.raw.txt").read_text(encoding="utf-8")
    names = [m.group(1) for m in audit.TARGET.finditer(raw)]
    names += [m.group(1) for m in audit.CLEAN.finditer(raw)]
    assert len(names) == len(set(names)) == 14
    assert set(names) == expected
    result = audit.parse(raw)
    assert result == RECEIPT["axiom_audit"]
    for field in ("targets_with_sorryAx", "targets_outside_standard_axioms", "conflicting_target_lines"):
        assert not result[field]


def test_learning_proof_sources_match_the_successful_module_subject():
    for source in RECEIPT["sources"]:
        current = (ROOT / source["path"]).read_bytes().replace(b"\r\n", b"\n")
        built = subprocess.run(
            ["git", "show", f"{RECEIPT['subject']}:{source['path']}"],
            cwd=ROOT, capture_output=True, check=True,
        ).stdout
        assert current == built
        assert hashlib.sha256(current).hexdigest() == source["sha256"]
    assert RECEIPT["closes_debt"] is False
    assert RECEIPT["discharges_archived_manuscript_gaps"] is False
