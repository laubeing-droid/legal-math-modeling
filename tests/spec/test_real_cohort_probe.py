"""Gates over the real-corpus cohort report (R-08's first stage).

The point of these checks is not to re-prove the numbers -- the report is regenerable
with one command -- but to make sure a real corpus can only ever produce what it is
entitled to: a REFERENCE-grade frequency, no interval it did not compute, no case text,
and no bulk download smuggled in as provenance.
"""

from __future__ import annotations

import importlib.util
import json
import re
from fractions import Fraction
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
REPORT = ROOT / "docs" / "formal-release" / "real_cohort_probe.json"

_spec = importlib.util.spec_from_file_location("real_cohort_probe", ROOT / "theory/spec/real_cohort_probe.py")
probe = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(probe)


def _doc() -> dict:
    return json.loads(REPORT.read_text(encoding="utf-8"))


def test_report_declares_its_own_ceiling() -> None:
    doc = _doc()
    assert doc["schema_version"] == "real-cohort-probe-v1"
    assert doc["status"] == "reference_grade_real_corpus_probe_not_causal_claim"
    assert doc["grade_ceiling"] == "REFERENCE"
    assert doc["forbidden_readings"], "a real-data report must state what it does not license"
    assert doc["limitations"], "the report dropped its own limitations"


def test_ceiling_is_the_crosscut_ledgers_value_not_a_second_opinion() -> None:
    """The grade has to come from the artifact that assigns grades."""

    import sys

    sys.path.insert(0, str(ROOT))
    from theory.spec.receipt_ledger import ReceiptLedger

    ledger = ReceiptLedger.load()
    doc = _doc()
    ceiling = ledger.crosscut_ceiling("crosscutA", "empirical_output")
    assert doc["grade_ceiling"] == ceiling
    assert doc["crosscut_grade"] == f"crosscutA/empirical_output={ceiling}"


def test_every_frequency_is_the_counted_ratio() -> None:
    doc = _doc()
    whole = doc["whole_sample"]
    assert Fraction(whole["successes"], whole["rows_observed"]) == Fraction(whole["frequency"])
    for c in doc["cohorts"]:
        assert c["rows_observed"] <= c["rows_retrieved"], c["charge"]
        if c["frequency"] is None:
            assert c["rows_observed"] == 0, c["charge"]
            continue
        assert Fraction(c["successes"], c["rows_observed"]) == Fraction(c["frequency"]), c["charge"]


def test_no_interval_is_claimed_without_a_computed_bound() -> None:
    for c in _doc()["cohorts"]:
        if c["status"] == "BACKEND_UNAVAILABLE":
            assert c["interval_low"] is None and c["interval_high"] is None, c["charge"]
            assert c.get("backend_note") or c.get("identity"), c["charge"]
        elif c["interval_low"] is not None:
            assert Fraction(c["interval_low"]) <= Fraction(c["frequency"]) <= Fraction(c["interval_high"])


def test_fetch_was_ranged_not_bulk() -> None:
    src = _doc()["source"]
    assert 0 < src["bytes_transferred"] < src["remote_bytes"], "the probe downloaded the whole corpus"
    assert src["row_groups_read"] >= 1 and src["records_read"] > 0
    assert re.fullmatch(r"\d{4}-\d\d-\d\dT\d\d:\d\d:\d\d\+00:00", src["retrieved_at"])


def test_no_case_text_or_identifier_is_stored() -> None:
    doc = _doc()
    blob = json.dumps(doc, ensure_ascii=False)
    assert "fact" not in {k.lower() for k in doc["source"]}
    long_strings = [v for v in _strings(doc) if len(v) > 400]
    assert not long_strings, f"stored strings are too long to be aggregates: {len(long_strings)}"
    assert "被告" not in blob or blob.count("被告") < 5, "party/charge text is leaking into the report"


def _strings(node):
    if isinstance(node, dict):
        for v in node.values():
            yield from _strings(v)
    elif isinstance(node, list):
        for v in node:
            yield from _strings(v)
    elif isinstance(node, str):
        yield node


def test_event_contracts_are_complete_enough_to_be_identified() -> None:
    """The probe must not blank-fill the contract to get a number out of the pipeline."""

    from theory.spec.probability_pipeline import IdentificationStatus, identify_event

    result = identify_event(probe.event_for("盗窃", "train"))
    assert result.status is IdentificationStatus.IDENTIFIED, result.reasons


def test_outcome_rule_is_decidable_on_missing_and_boundary_values() -> None:
    assert probe.outcome_of({"imprisonment": None}) == (False, None)
    assert probe.outcome_of({}) == (False, None)
    assert probe.outcome_of({"imprisonment": -1}) == (False, None)
    assert probe.outcome_of({"imprisonment": 100000}) == (False, None)
    assert probe.outcome_of({"imprisonment": 36}) == (True, True)
    assert probe.outcome_of({"imprisonment": 37}) == (True, False)
