from __future__ import annotations

from copy import deepcopy

import pytest

from theory.spec.translation_witness import (
    build_translation_witness,
    check_translation_witness,
    translation_witness_to_dict,
)


def _valid_witness() -> dict:
    witness = build_translation_witness(
        input_content={
            "facts": ["fact::contract", "fact::exception"],
            "rules": ["rule::breach", "rule::exception", "rule::priority"],
            "exceptions": ["fact::exception"],
            "priorities": [{"winner": "rule::exception", "loser": "rule::breach"}],
        },
        expected_arguments=(
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
        ),
        expected_attacks=(
            {
                "attack_id": "attack::priority",
                "attacker_id": "argument::exception",
                "target_id": "argument::breach",
                "kind": "PRIORITY_DEFEAT",
                "input_witness": "rule::priority",
            },
        ),
        output_arguments=(
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
        ),
        output_attacks=(
            {
                "attack_id": "attack::priority",
                "attacker_id": "argument::exception",
                "target_id": "argument::breach",
                "kind": "PRIORITY_DEFEAT",
                "input_witness": "rule::priority",
            },
        ),
        semantics_id="grounded",
        semantics_version="1",
    )
    return translation_witness_to_dict(witness)


def test_translation_witness_accepts_exact_translation() -> None:
    report = check_translation_witness(_valid_witness())

    assert report.satisfied is True
    assert not report.error_codes


@pytest.mark.parametrize(
    ("mutator", "code"),
    (
        (lambda w: w["output_attacks"].clear(), "EXPECTED_EDGE_OMITTED"),
        (
            lambda w: w["output_attacks"].append(
                {
                    "attack_id": "attack::invented",
                    "attacker_id": "argument::breach",
                    "target_id": "argument::exception",
                    "kind": "REBUTTAL",
                    "input_witness": "rule::invented",
                }
            ),
            "SPURIOUS_EDGE",
        ),
        (
            lambda w: w["output_attacks"][0].update(
                attacker_id="argument::breach",
                target_id="argument::exception",
            ),
            "PRIORITY_DIRECTION_REVERSED",
        ),
    ),
)
def test_translation_witness_rejects_edge_mutations(mutator, code: str) -> None:
    witness = deepcopy(_valid_witness())
    mutator(witness)

    report = check_translation_witness(witness)

    assert report.satisfied is False
    assert code in report.error_codes

