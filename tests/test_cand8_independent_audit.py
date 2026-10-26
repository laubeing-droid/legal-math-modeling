"""Bind the separate CAND8 kernel receipt without promoting the frozen live pin."""

import hashlib
import json
import re
import subprocess
from pathlib import Path

from scripts.ci import check_axiom_audit_log as audit

ROOT = Path(__file__).resolve().parents[1]
EVIDENCE = ROOT / "docs/formal-release/evidence/cand8-independent-20261027"
RECEIPT = json.loads((EVIDENCE / "verification.json").read_text(encoding="utf-8"))
LEAN = ROOT / "proofs/lean/juris_lean/JurisLean/Candidates"


def test_kernel_names_match_the_source_and_both_audit_commands():
    source = (ROOT / RECEIPT["source_path"]).read_text(encoding="utf-8")
    expected = {
        "JurisLean.Candidates.FormalTail20261024." + short
        for short in re.findall(r"^theorem (\S+)", source, re.MULTILINE)
    }
    driver = (LEAN / "FormalTailCAND8AxiomAudit20261027.lean").read_text(encoding="utf-8")
    for command in ("#check", "#print axioms"):
        named = re.findall(rf"^{command} (\S+)$", driver, re.MULTILINE)
        assert len(named) == len(set(named)) == 69
        assert set(named) == expected
    raw = (EVIDENCE / RECEIPT["kernel_output"]).read_text(encoding="utf-8")
    printed = [m.group(1) for m in audit.TARGET.finditer(raw)]
    printed += [m.group(1) for m in audit.CLEAN.finditer(raw)]
    assert len(printed) == len(set(printed)) == 69
    assert set(printed) == expected == set(RECEIPT["named_theorems_full"])
    result = audit.parse(raw)
    assert result == RECEIPT["axiom_audit"]
    for field in ("targets_with_sorryAx", "targets_outside_standard_axioms", "conflicting_target_lines"):
        assert not result[field]


def test_audited_source_matches_its_build_and_merged_proof_tip():
    source_bytes = (ROOT / RECEIPT["source_path"]).read_bytes().replace(b"\r\n", b"\n")
    assert hashlib.sha256(source_bytes).hexdigest() == RECEIPT["source_sha256"]
    for revision in (RECEIPT["audit_subject"], RECEIPT["proof_tip"]):
        committed = subprocess.run(
            ["git", "show", f"{revision}:{RECEIPT['source_path']}"],
            cwd=ROOT, capture_output=True, check=True,
        ).stdout
        assert committed == source_bytes


def test_expansion_preserves_the_old_61_target_pin_and_does_not_close_debt():
    prior = json.loads((LEAN / "Final20261021/evidence/ci-tip-21862d9b/verification.json")
                       .read_text(encoding="utf-8"))
    previous = set(prior["named_theorems_full"])
    expanded = set(RECEIPT["named_theorems_full"])
    assert len(previous) == RECEIPT["prior_count"] == 61
    assert previous < expanded
    assert len(expanded - previous) == RECEIPT["cand8_count"] == 8
    assert RECEIPT["frozen_live_pin_unchanged"] == {
        "subject": prior["subject_commit"], "run_id": prior["run_id"], "named_count": 61,
    }
    assert prior["subject_commit"] == "21862d9bdd94bfa15e5da39079538b5eb30ff235"
    assert prior["run_id"] == 40274167574
    assert RECEIPT["closes_debt"] is False
    assert RECEIPT["discharges_archived_manuscript_gaps"] is False
    assert RECEIPT["math_flip_authorized"] is False
    assert RECEIPT["open_formal_tail_remaining"] == 20
