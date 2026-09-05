from __future__ import annotations

from theory.spec.argumentation_semantics import (
    PROTECTED_DEFAULT_SEMANTICS,
    SEMANTICS_REGISTRY,
    check_semantics_switch,
    grounded_labelling,
    resolve_priority,
)


def test_unattacked_chain_is_accepted() -> None:
    labelling = grounded_labelling((("a", "b"),))

    assert "a" in labelling.in_nodes
    assert "b" in labelling.out_nodes
    assert not labelling.undecided_nodes


def test_self_attack_is_never_in_grounded() -> None:
    labelling = grounded_labelling((("a", "a"),))

    assert "a" not in labelling.in_nodes
    assert "a" in labelling.undecided_nodes


def test_mutual_attack_pair_is_undecided() -> None:
    labelling = grounded_labelling((("a", "b"), ("b", "a")))

    assert labelling.undecided_nodes == {"a", "b"}
    assert not labelling.in_nodes


def test_odd_cycle_is_undecided() -> None:
    labelling = grounded_labelling((("a", "b"), ("b", "c"), ("c", "a")))

    assert labelling.undecided_nodes == {"a", "b", "c"}


def test_defended_argument_is_reinstated() -> None:
    labelling = grounded_labelling((("b", "a"), ("c", "b")))

    assert labelling.in_nodes == {"a", "c"}
    assert labelling.out_nodes == {"b"}


def test_priority_cycle_yields_undecided() -> None:
    assert resolve_priority((("r1", "r2"),), "r1", "r2") == "r1"
    assert resolve_priority((("r2", "r1"),), "r1", "r2") == "r2"
    assert resolve_priority((("r1", "r2"), ("r2", "r1")), "r1", "r2") is None
    assert resolve_priority((), "r1", "r2") is None


def test_semantics_registry_is_explicit_and_protected() -> None:
    assert PROTECTED_DEFAULT_SEMANTICS == "GROUNDED"
    assert SEMANTICS_REGISTRY == ("GROUNDED", "PREFERRED", "STABLE", "COMPLETE")

    allowed, errors = check_semantics_switch(
        {"from": "GROUNDED", "to": "PREFERRED", "contract_version_bound": True}
    )
    assert allowed is True

    allowed, errors = check_semantics_switch(
        {"from": "GROUNDED", "to": "PREFERRED", "contract_version_bound": False}
    )
    assert allowed is False
    assert "SEMANTICS_SWITCH_UNBOUND" in errors

    allowed, errors = check_semantics_switch(
        {"from": "GROUNDED", "to": "AD_HOC", "contract_version_bound": True}
    )
    assert allowed is False
    assert "UNKNOWN_TARGET_SEMANTICS" in errors
