from __future__ import annotations

from copy import deepcopy

import pytest

from theory.spec.source_bundle import (
    build_bundle_entry,
    build_source_bundle,
    canonical_digest,
    check_source_bundle,
)
from theory.spec.source_path import build_source_path, check_source_path
from theory.spec.source_contracts import HierarchyRank, select_indexed_source
from theory.spec.temporal_applicability import (
    build_version_record,
    check_supersession_chain,
    check_temporal_applicability,
    effective_at,
)


def test_indexed_identity_does_not_accept_title_substrings_or_other_ranks():
    national = dict(rank=HierarchyRank.STATUTE, title="Synthetic Code", version_id="v1", effective_from=10)
    local = dict(national, rank=HierarchyRank.LOCAL_REGULATION)
    records = [local, dict(national, title="Synthetic Code Commentary"), national]
    assert select_indexed_source(records, rank=HierarchyRank.STATUTE,
                                 title="Synthetic Code", at_day=10) == (national, "")
    assert select_indexed_source(records, rank=HierarchyRank.STATUTE,
                                 title="Synthetic", at_day=10)[1] == "SOURCE_IDENTITY_NOT_FOUND"


def test_indexed_versions_use_bound_time_including_the_repeal_boundary():
    old = dict(rank=HierarchyRank.STATUTE, title="Synthetic Code", version_id="v1",
               effective_from=10, effective_to=19)
    new = dict(old, version_id="v2", effective_from=20, effective_to=None)
    for day, expected in [(9, None), (10, old), (19, old), (20, new), (100, new)]:
        chosen, _ = select_indexed_source([new, old], rank=HierarchyRank.STATUTE,
                                          title="Synthetic Code", at_day=day)
        assert chosen == expected
    # A later query still resolves the old version at the bound historical day.
    assert select_indexed_source([new, old], rank=HierarchyRank.STATUTE,
        title="Synthetic Code", at_day=15, version_id="v1")[0] == old
    assert select_indexed_source([new, old], rank=HierarchyRank.STATUTE,
        title="Synthetic Code", at_day=20, version_id="v1")[1] == "NO_VERSION_AT_BOUND_TIME"


def test_indexed_version_ambiguity_does_not_depend_on_input_order():
    a = dict(rank=HierarchyRank.STATUTE, title="Synthetic Code", version_id="a", effective_from=10)
    b = dict(a, version_id="b")
    for rows in ([a, b], [b, a]):
        assert select_indexed_source(rows, rank=HierarchyRank.STATUTE,
            title="Synthetic Code", at_day=11)[1] == "AMBIGUOUS_SOURCE_VERSION"
        assert select_indexed_source(rows, rank=HierarchyRank.STATUTE,
            title="Synthetic Code", at_day=11, version_id="b") == (b, "")


@pytest.mark.parametrize("interval", [{}, {"effective_from": 20, "effective_to": 10}])
def test_indexed_version_never_substitutes_filename_date_for_unknown_effectivity(interval):
    record = dict(rank=HierarchyRank.STATUTE, title="Synthetic Code", version_id="v1", **interval)
    assert select_indexed_source([record], rank=HierarchyRank.STATUTE,
        title="Synthetic Code", at_day=30)[1] == "SOURCE_INTERVAL_UNRESOLVED"


def _valid_bundle() -> dict:
    entries = (
        build_bundle_entry(
            snapshot_id="snapshot::statute",
            locator={"path": "/statute/v1", "anchor": "article-3"},
            content="third article text",
            version="spec-schema-v2",
        ),
        build_bundle_entry(
            snapshot_id="snapshot::contract",
            locator={"path": "/contract/v1", "anchor": "clause-2"},
            content="delivery clause",
            version="spec-schema-v2",
        ),
    )
    return build_source_bundle(entries)


def test_bundle_accepts_bound_entries() -> None:
    report = check_source_bundle(_valid_bundle())

    assert report.satisfied is True
    assert not report.error_codes


@pytest.mark.parametrize(
    ("mutator", "code"),
    (
        (lambda b: b["entries"][0].update(content="tampered"), "SOURCE_DIGEST_MISMATCH"),
        (
            lambda b: b["entries"][0]["locator"].update(path="/statute/v2"),
            "LOCATOR_DIGEST_MISMATCH",
        ),
        (lambda b: b["entries"][0].pop("locator"), "MISSING_LOCATOR"),
        (lambda b: b["entries"][0].update(version="unknown"), "UNKNOWN_VERSION"),
        (
            lambda b: b["entries"].append(deepcopy(b["entries"][0])),
            "DUPLICATE_SNAPSHOT",
        ),
        (lambda b: b["snapshot_ids"].pop(), "BROKEN_REFERENCE"),
    ),
)
def test_bundle_rejects_mutations(mutator, code: str) -> None:
    bundle = deepcopy(_valid_bundle())
    mutator(bundle)

    report = check_source_bundle(bundle)

    assert report.satisfied is False
    assert code in report.error_codes


def test_content_digest_binds_exact_content() -> None:
    assert canonical_digest("a") != canonical_digest("b")


def _valid_path() -> dict:
    return build_source_path(
        (
            {"from": "snapshot::statute", "to": "snapshot::contract", "kind": "DERIVATION", "witness": "article-3"},
            {"from": "snapshot::contract", "to": "snapshot::statute", "kind": "CITATION", "witness": "clause-2"},
        )
    )


def test_source_path_accepts_witnessed_edges() -> None:
    report = check_source_path(
        _valid_path(),
        known_snapshots=("snapshot::statute", "snapshot::contract"),
    )

    assert report.satisfied is True


@pytest.mark.parametrize(
    ("mutator", "code"),
    (
        (lambda p: p["edges"][0].update(witness=""), "EMPTY_WITNESS"),
        (lambda p: p["edges"][0].update(kind="HYPERLINK"), "UNKNOWN_EDGE_KIND"),
        (lambda p: p["edges"][0].update(to=p["edges"][0]["from"]), "SELF_EDGE"),
        (
            lambda p: p["edges"][0].__setitem__("from", "snapshot::ghost"),
            "BROKEN_LINK",
        ),
        (
            lambda p: p["edges"][1].__setitem__("kind", "DERIVATION"),
            "DEPENDENCY_CYCLE",
        ),
    ),
)
def test_source_path_rejects_mutations(mutator, code: str) -> None:
    path = deepcopy(_valid_path())
    mutator(path)

    report = check_source_path(
        path,
        known_snapshots=("snapshot::statute", "snapshot::contract"),
    )

    assert report.satisfied is False
    assert code in report.error_codes


def test_retrieval_relevance_never_grants_authority() -> None:
    path = build_source_path(
        ({"from": "snapshot::statute", "to": "snapshot::contract", "kind": "RETRIEVAL", "witness": "similarity"},)
    )

    report = check_source_path(path, declares_authority=True)

    assert report.satisfied is False
    assert report.authority_granted is False
    assert "RETRIEVAL_NOT_APPLICABILITY" in report.error_codes


def test_temporal_applicability_accepts_active_interval() -> None:
    version = build_version_record(
        snapshot_id="snapshot::statute",
        publication_day=100,
        effective_from=120,
        effective_to=200,
    )

    report = check_temporal_applicability(
        version, event_day=120, observed_day=130, as_of_day=140, decision_day=150
    )

    assert report.applicable is True
    assert effective_at(version, 200) is True
    assert effective_at(version, 201) is False


@pytest.mark.parametrize(
    ("mutator", "kwargs", "code"),
    (
        (lambda v: v.update(status="RETRACTED"), {}, "RETRACTED_SOURCE_INVALIDATED"),
        (lambda v: v.update(status="SUPERSEDED"), {}, "SUPERSEDED_SOURCE_INVALIDATED"),
        (lambda v: v.update(timezone=None), {}, "IMPLICIT_TIME_GRANULARITY"),
        (lambda v: v.update(effective_to=90), {}, "INVERTED_EFFECTIVE_INTERVAL"),
        (lambda v: None, {"observed_day": 200, "as_of_day": 150}, "FUTURE_INFORMATION_BACKFLOW"),
        (lambda v: None, {"event_day": 50}, "OUTSIDE_EFFECTIVE_INTERVAL"),
        (lambda v: None, {"decision_day": 999}, "DECISION_OUTSIDE_EFFECTIVE_INTERVAL"),
    ),
)
def test_temporal_applicability_rejects_mutations(mutator, kwargs, code: str) -> None:
    version = build_version_record(
        snapshot_id="snapshot::statute",
        publication_day=100,
        effective_from=120,
        effective_to=200,
    )
    mutator(version)
    defaults = {"event_day": 130, "observed_day": 130, "as_of_day": 140}
    defaults.update(kwargs)

    report = check_temporal_applicability(version, **defaults)

    assert report.applicable is False
    assert code in report.error_codes


def test_supersession_chain_classifies_failures() -> None:
    assert check_supersession_chain(({"old": "a", "new": "b"},)) == ()
    assert "SELF_SUPERSESSION" in check_supersession_chain(({"old": "a", "new": "a"},))
    assert "SUPERSESSION_CYCLE" in check_supersession_chain(
        ({"old": "a", "new": "b"}, {"old": "b", "new": "a"})
    )
    assert check_supersession_chain(
        ({"old": "a", "new": "b"}, {"old": "b", "new": "c"})
    ) == ()
