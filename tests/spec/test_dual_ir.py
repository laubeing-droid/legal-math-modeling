from __future__ import annotations

from copy import deepcopy

from theory.spec.dual_ir import (
    build_pipeline_witness,
    lower_ivl_to_targets,
    lower_spec_to_ivl,
    normalize_spec,
)
from theory.spec.translation_witness import check_translation_witness


def _spec() -> dict:
    return {
        "spec_id": "spec::contract",
        "rules": [
            {
                "rule_id": "rule::breach",
                "locator": {"path": "/statute/article-3", "anchor": "clause-1"},
                "conditions": ["fact::contract"],
                "conclusion": "breach",
                "exceptions": [],
                "priority_over": [],
            },
            {
                "rule_id": "rule::exception",
                "locator": {"path": "/statute/article-5", "anchor": "clause-2"},
                "conditions": ["fact::exception"],
                "conclusion": "exception",
                "exceptions": ["fact::exception"],
                "priority_over": ["rule::breach"],
            },
        ],
    }


def _arguments() -> list:
    return [
        {
            "argument_id": "argument::breach",
            "rule_id": "rule::breach",
            "conclusion": "breach",
            "support_fact_ids": ["fact::contract"],
        },
        {
            "argument_id": "argument::exception",
            "rule_id": "rule::exception",
            "conclusion": "exception",
            "support_fact_ids": ["fact::exception"],
        },
    ]


def test_normalize_is_idempotent_and_drops_unlocated_rules() -> None:
    spec = _spec()
    spec["rules"].append(
        {"rule_id": "rule::ghost", "locator": "", "conditions": [], "conclusion": "ghost"}
    )

    normalized = normalize_spec(spec)

    assert [rule["rule_id"] for rule in normalized["rules"]] == [
        "rule::breach",
        "rule::exception",
    ]
    assert [rule["rule_id"] for rule in normalized["dropped_rules"]] == ["rule::ghost"]
    assert normalize_spec(normalized)["rules"] == normalized["rules"]


def test_lowering_preserves_rule_ids_and_blocks_decisive_on_lost_fields() -> None:
    ivl = lower_spec_to_ivl(normalize_spec(_spec()))

    assert [rule["rule_id"] for rule in ivl["rules"]] == ["rule::breach", "rule::exception"]
    assert ivl["decisive_allowed"] is True

    spec = deepcopy(_spec())
    spec["rules"][0]["uncertain_fields"] = ["amount"]
    ivl_lost = lower_spec_to_ivl(normalize_spec(spec))
    assert ivl_lost["decisive_allowed"] is False
    assert ivl_lost["lost_fields"] == ["amount"]


def test_pipeline_witness_passes_independent_checker() -> None:
    _, _, witness = build_pipeline_witness(_spec(), _arguments())

    report = check_translation_witness(witness)

    assert report.satisfied is True
    assert len(witness["expected_attacks"]) == 1
    assert witness["expected_attacks"][0]["kind"] == "PRIORITY_DEFEAT"


def test_pipeline_witness_detects_omitted_and_spurious_mutations() -> None:
    _, _, witness = build_pipeline_witness(_spec(), _arguments())

    omitted = deepcopy(witness)
    omitted["output_attacks"] = []
    assert "EXPECTED_EDGE_OMITTED" in check_translation_witness(omitted).error_codes

    spurious = deepcopy(witness)
    spurious["output_attacks"].append(
        {
            "attack_id": "attack::invented",
            "attacker_id": "argument::breach",
            "target_id": "argument::exception",
            "kind": "REBUTTAL",
            "input_witness": "rule::invented",
        }
    )
    assert "SPURIOUS_EDGE" in check_translation_witness(spurious).error_codes

    reversed_priority = deepcopy(witness)
    reversed_priority["output_attacks"][0]["attacker_id"] = "argument::breach"
    reversed_priority["output_attacks"][0]["target_id"] = "argument::exception"
    codes = check_translation_witness(reversed_priority).error_codes
    assert "PRIORITY_DIRECTION_REVERSED" in codes


def test_horn_target_preserves_clauses() -> None:
    ivl = lower_spec_to_ivl(normalize_spec(_spec()))
    targets = lower_ivl_to_targets(ivl, _arguments())

    assert [clause["rule_id"] for clause in targets["horn"]] == [
        "rule::breach",
        "rule::exception",
    ]
    assert targets["horn"][0]["conclusion"] == "breach"
