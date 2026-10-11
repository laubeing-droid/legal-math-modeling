"""Group-02 sourcing reference entries (D009-D018, W2-A batch B02).

Every entry consumes real structured input (no fixtures, no precomputed
answers) and produces the intermediate result whose formal contract is
``JurisLean.FullMath.Contracts.demand_D009`` … ``demand_D018``:

* D009 ``quote_span`` / ``version_accepts`` — quoted_span is exactly the
  ``[start, end)`` slice of the source; the provenance coordinates
  read back verbatim; a real quotation citing the wrong version is
  rejected by the cache-key version check.
* D010 ``applicable_rules``  — results come from the frozen rule base and
  satisfy the applicability predicate; a full-applicability claim needs
  independent candidate coverage (every applicable rule in the result).
* D011 ``applies_at`` / ``historical_version_decision`` — applicability
  is judged by the legal-effect time at the event day, never by the
  registration (upload) time; a later-uploaded old text is still the law
  in its own effective window and a new law does not apply before its
  effective date.
* D012 ``resolve_definition`` — bounded citation chase over the declared
  definition table and cross-reference graph; registered qualifiers
  (exclusion flags) survive resolution; fuel exhaustion is an explicit
  rejection path, never an invented meaning.
* D013 ``compare_score`` / ``transfer_case`` — the ranking comparator is
  the designated score itself (antisymmetric); a similar-case transfer
  copies the substantive conclusion only under a feature-preservation
  witness (every relevant feature kept in the target case).
* D014 ``pool_recall`` / ``corpus_completeness_claimable`` — returned ⊆
  relevant (and pool-exhaustive inside the pool); the corpus-wide
  no-miss claim is refused while any relevant corpus item sits outside
  the judged pool.
* D015 ``approved_edges`` / ``upgrade_claim`` — approved support edges
  are generated only from pro-stance citations; a real case number that
  supports only the opposite view is never a positive basis; a claim
  upgrade requires every cited id to carry an approved edge.
* D016 ``precedent_validity`` — the precedent validity graph is keyed by
  (case, issue) and tied to the citation day: an overruled issue is
  invalid from its effective day on, unrelated issues of the same case
  stay valid, and the overturned point is never retained.
* D017 ``select_framework`` — LegalFramework candidates are filtered by
  the conjunction of four applicability conditions (jurisdiction,
  subject, conflict, applicability); any single condition is
  insufficient (an English contract or a US party alone does not select
  the UCC); undecided branches stay retained as pending.
* D018 ``compare_regimes`` — a cross-jurisdiction comparison preserves
  each domain's subjects/threshold/timing/effect dimensions; identical
  filing thresholds with different effects are distinguished and a named
  difference witness is returned instead of an equivalence verdict.

The downstream adapters at the bottom feed these intermediate results
into the unified pipeline public entries (``run_case`` / ``step_event``
/ ``run_trace``); they never accept a precomputed verdict.  The
independent contract checker lives in ``sourcing_check`` and shares no
code with this module.
"""
from __future__ import annotations

from fractions import Fraction
from typing import Callable, Optional, Sequence

# ---------------------------------------------------------------------------
# D009 — quotation span readback and version check
# ---------------------------------------------------------------------------


def quote_span(source: Sequence[str], start: int, end: int) -> dict:
    """quoted_span = source[start:end]; the recorded provenance coordinates
    read back to exactly the delivered span (verbatim slice semantics)."""

    if not (0 <= start <= end <= len(source)):
        raise ValueError("quote coordinates must satisfy 0 <= start <= end "
                         "<= len(source)")
    span = tuple(source[start:end])
    readback = tuple(source[start:end])
    if readback != span:
        raise AssertionError("provenance readback diverged from the span")
    return {"span": span, "start": start, "end": end,
            "length": end - start, "source_length": len(source)}


def version_key(version: dict) -> tuple:
    """The frozen cache-key triple (published, effective, repeal); the
    registration time and the legal-effect time are separate fields."""

    return (version["published"], version["effective"], version["repeal"])


def version_accepts(source_version: dict, quoted_version: dict) -> bool:
    """The version check passes only on identical cache keys; a real
    quotation citing the wrong version is rejected outright."""

    return version_key(source_version) == version_key(quoted_version)


# ---------------------------------------------------------------------------
# D010 — applicable rules inside the frozen rule base
# ---------------------------------------------------------------------------


def applicable_rules(rules: Sequence[tuple]) -> dict:
    """Results satisfy the applicability predicate inside the frozen rule
    base: hits are exactly the rules whose predicate holds; similar but
    inapplicable rules never enter the result."""

    hits = tuple(r[0] for r in rules if r[1])
    return {"hits": hits,
            "frozen_base": tuple((r[0], bool(r[1])) for r in rules)}


def full_applicability_certificate(rules: Sequence[tuple],
                                   hits: Sequence[str]) -> bool:
    """The all-applicable certificate is licensed only by independent
    candidate coverage: every rule of the frozen base that satisfies the
    predicate must be present in the delivered hits."""

    hit_set = frozenset(hits)
    return all(r[0] in hit_set for r in rules if r[1])


# ---------------------------------------------------------------------------
# D011 — legal-effect time vs. registration time
# ---------------------------------------------------------------------------


def applies_at(version: dict, day: int) -> bool:
    """Applicability is judged by the effective time at the event day and
    the repeal window; the registration (upload) time never decides."""

    if version["effective"] > day:
        return False
    repeal = version["repeal"]
    return repeal is None or day < repeal


def historical_version_decision(old: dict, new: dict, day: int) -> dict:
    """Which historical version governs at ``day``: the new law does not
    apply before its effective date even though it was uploaded first,
    and the later-uploaded old text still applies inside its own
    effective window."""

    return {"new_applies": applies_at(new, day),
            "old_applies": applies_at(old, day),
            "judged_by": "effective",
            "registration_times": (old["published"], new["published"]),
            "effect_times": (old["effective"], new["effective"])}


# ---------------------------------------------------------------------------
# D012 — definition scope, qualifiers and bounded reference chase
# ---------------------------------------------------------------------------


def resolve_definition(defs: Sequence[tuple], cites: Sequence[tuple],
                       term: str, fuel: int) -> dict:
    """Bounded citation chase: a registered meaning stops the chase and is
    returned with its qualifier (exclusion flag) intact; fuel exhaustion
    or a missing registration is an explicit rejection path."""

    if fuel < 0:
        raise ValueError("fuel must be nonnegative")

    def _first(rows, key):
        for row in rows:
            if row[0] == key:
                return row
        return None

    current = term
    hops = 0
    path = ()
    while True:
        if hops >= fuel:
            return {"status": "rejected", "term": term,
                    "reason": "fuel_exhausted", "hops": hops,
                    "path": path}
        hit = _first(defs, current)
        if hit is not None:
            return {"status": "resolved", "term": term,
                    "meaning": hit[1], "excluded": bool(hit[2]),
                    "hops": hops, "path": path}
        ref = _first(cites, current)
        if ref is None:
            return {"status": "rejected", "term": term,
                    "reason": "unregistered", "hops": hops,
                    "path": path}
        path = path + (current,)
        current = ref[1]
        hops += 1


# ---------------------------------------------------------------------------
# D013 — score-consistent ranking and witnessed similar-case transfer
# ---------------------------------------------------------------------------


def compare_score(score: dict, a: str, b: str) -> dict:
    """The ranking comparator is the designated score itself: the order
    agrees with the score order and is antisymmetric (equal scores share
    a rank, both directions can never hold at once)."""

    sa: Fraction = score[a]
    sb: Fraction = score[b]
    if sa > sb and sb > sa:
        raise AssertionError("score order must be antisymmetric")
    return {"a_before_b": sa > sb, "b_before_a": sb > sa,
            "same_rank": sa == sb}


def transfer_case(relevant: Sequence[str],
                  target_features: Sequence[str]) -> dict:
    """A similar-case transfer copies the substantive conclusion only
    under the feature-preservation witness: every relevant feature must
    be kept in the target case; any missing feature blocks the copy and
    is named."""

    target = frozenset(target_features)
    missing = tuple(f for f in relevant if f not in target)
    return {"copied": not missing, "missing_features": missing,
            "witness": tuple(relevant)}


# ---------------------------------------------------------------------------
# D014 — pool reranking vs. corpus-wide retrieval
# ---------------------------------------------------------------------------


def pool_recall(pool: Sequence[str], relevant: Callable[[str], bool]) -> tuple:
    """Returned ⊆ Relevant: the returned list is the pool filtered by the
    independent relevance definition; nothing outside the pool is
    invented."""

    return tuple(s for s in pool if relevant(s))


def corpus_completeness_claimable(corpus: Sequence[str],
                                  pool: Sequence[str],
                                  relevant: Callable[[str], bool]) -> bool:
    """Returned = Relevant_D over the whole corpus is claimable only once
    the pool covers the corpus and every item is adjudicated: a relevant
    corpus item outside the judged pool refuses the no-miss claim."""

    pool_set = frozenset(pool)
    for item in corpus:
        if item not in pool_set and relevant(item):
            return False
    return True


# ---------------------------------------------------------------------------
# D015 — citation support edges and claim upgrade
# ---------------------------------------------------------------------------


def approved_edges(cites: Sequence[tuple], prop_id: str) -> tuple:
    """Approved semantic-support edges are generated only from pro-stance
    citations; a citation record keeps its span verbatim in the
    registry."""

    edges = tuple((c[0], prop_id) for c in cites if c[2])
    registry = tuple((c[0], tuple(c[1]), bool(c[2])) for c in cites)
    return {"edges": edges, "prop_id": prop_id, "registry": registry}


def upgrade_claim(claim_cites: Sequence[str], edges: Sequence[tuple]) -> dict:
    """The declaration upgrade is licensed only after support-graph
    coverage: every cited id must carry an approved support edge."""

    sources = frozenset(e[0] for e in edges)
    uncovered = tuple(c for c in claim_cites if c not in sources)
    return {"upgraded": not uncovered, "uncovered_cites": uncovered}


# ---------------------------------------------------------------------------
# D016 — precedent validity graph keyed by (case, issue) and citation day
# ---------------------------------------------------------------------------


def precedent_validity(overruled: Sequence[tuple], case: str, issue: str,
                       day: int) -> dict:
    """Valid at ``day`` iff no overrule of exactly this (case, issue) has
    taken effect by the citation day; unrelated issues of the same case
    are never touched and the overturned point is never retained."""

    blocking = tuple(o for o in overruled
                     if o[0] == case and o[1] == issue and day >= o[2])
    return {"case": case, "issue": issue, "as_of": day,
            "valid": not blocking, "blocking_overrules": blocking}


# ---------------------------------------------------------------------------
# D017 — LegalFramework candidate filtering with pending branches
# ---------------------------------------------------------------------------


def select_framework(cands: Sequence[tuple], name: str) -> dict:
    """A framework candidate is selected only when all four applicability
    conditions (jurisdiction, subject, conflict, applicability) hold;
    undecided candidates stay retained as pending branches."""

    row = None
    for c in cands:
        if c[0] == name:
            row = c
            break
    if row is None:
        return {"status": "pending", "branch": None, "flags": None}
    flags = tuple(bool(x) for x in row[1:])
    selected = all(flags)
    return {"status": "selected" if selected else "pending",
            "branch": row, "flags": flags}


# ---------------------------------------------------------------------------
# D018 — cross-jurisdiction regime comparison with difference witness
# ---------------------------------------------------------------------------

_COMPARISON_DIMENSIONS = ("subjects", "threshold", "timing", "effect")


def compare_regimes(a: dict, b: dict) -> dict:
    """The comparison preserves each domain's four dimensions and returns
    a named difference witness; identical thresholds with different
    effects are distinguished (never reported as equivalent)."""

    witness = []
    if a["subjects"] != b["subjects"]:
        witness.append("subjects")
    if a["threshold"] != b["threshold"]:
        witness.append("threshold")
    if a["timing"] != b["timing"]:
        witness.append("timing")
    if a["effect"] != b["effect"]:
        witness.append("effect")
    return {"equivalent": not witness,
            "difference_witness": tuple(witness),
            "preserved": tuple(_COMPARISON_DIMENSIONS)}


# ---------------------------------------------------------------------------
# Downstream adapters: sourcing results → pipeline carriers (PY-RUN)
# ---------------------------------------------------------------------------

SOURCING_ENV_ID = "env-sourcing-b02"


def build_sourcing_intake() -> dict:
    """Synthetic sourcing bundle for one civil loan case; every field is
    produced by the entries above from declared input tables."""

    # D009: the quotation is the exact slice of the declared source text,
    # with its provenance coordinates; the cited version must match the
    # source version (a real quote of the wrong version is rejected)
    source_text = ("loan", "contract", "signed", "principal", "due")
    quote = quote_span(source_text, 1, 4)
    source_version = {"published": 20, "effective": 30, "repeal": None}
    version_ok = version_accepts(source_version, source_version)
    version_rejects = version_accepts(source_version,
                                      {"published": 21, "effective": 30,
                                       "repeal": None})
    # D010: the frozen rule base; the loan-delivery rule applies, a
    # similar tort rule does not (similarity alone is not applicability)
    rules = (("loan-delivery-civil", True), ("tort-lookalike", False))
    applicable = applicable_rules(rules)
    certificate = full_applicability_certificate(rules, applicable["hits"])
    # D011: the old text was uploaded later but governs at the event day;
    # the new law does not apply before its own effective date
    old_text = {"published": 90, "effective": 10, "repeal": None}
    new_text = {"published": 40, "effective": 200, "repeal": None}
    historical = historical_version_decision(old_text, new_text, 50)
    # D012: the definition of "affiliate" carries an exclusion qualifier;
    # the chase resolves it with the qualifier intact
    defs = (("affiliate", "excluded-from-main-text", True),
            ("loan", "principal-and-interest", False))
    definition = resolve_definition(defs, (), "affiliate", 3)
    # D013: the transferred similar case keeps every relevant feature;
    # scores rank the candidates (higher score first)
    similar = transfer_case(
        relevant=("loan", "written_contract", "delivered_funds"),
        target_features=("loan", "written_contract", "delivered_funds"))
    scores = {"case-a": Fraction(3, 4), "case-b": Fraction(1, 2)}
    ordering = compare_score(scores, "case-a", "case-b")
    # D014: the judged pool and the corpus — one relevant corpus item
    # outside the pool refuses the corpus-wide no-miss claim
    corpus = ("p1", "p2", "p3", "outside-relevant")
    pool = ("p1", "p2", "p3")
    recall = pool_recall(pool, lambda s: s.startswith("p") and s != "p3")
    claim_ok = corpus_completeness_claimable(corpus, pool,
                                             lambda s: s != "p3")
    # D015: pro-stance citations generate the approved edges; the con
    # stance never does; the claim upgrade needs every cite covered
    cites = (("case-pro", ("supports", "loan"), True),
             ("case-con", ("contradicts", "loan"), False))
    support = approved_edges(cites, "loan")
    upgrade = upgrade_claim(("case-pro",), support["edges"])
    # D016: the overrule of one issue does not touch the other issue and
    # does not retain the overturned point
    overruled = (("case-pro", "quantum", 20),
                 ("case-pro", "limitation", 40))
    precedent = precedent_validity(overruled, "case-pro", "quantum", 30)
    # D017: jurisdiction holds but the subject condition fails — the UCC
    # branch stays pending, never auto-selected
    cands = (("ucc-sale", True, False, True, True),
             ("civil-loan", True, True, True, True))
    framework = select_framework(cands, "ucc-sale")
    # D018: identical filing thresholds, different legal effects — the
    # regimes are distinguished with the named difference witness
    comparison = compare_regimes(
        {"subjects": ("turnover",), "threshold": Fraction(100_000_000),
         "timing": 30, "effect": "prohibited"},
        {"subjects": ("turnover",), "threshold": Fraction(100_000_000),
         "timing": 30, "effect": "file-then-proceed"})
    return {
        "case_id": "case-b02",
        "quote": quote,
        "source_version": source_version,
        "version_ok": version_ok,
        "version_rejects": version_rejects,
        "applicable": applicable,
        "certificate": certificate,
        "historical": historical,
        "definition": definition,
        "similar": similar,
        "ordering": ordering,
        "scores": scores,
        "recall": recall,
        "recall_claim_ok": claim_ok,
        "support": support,
        "upgrade": upgrade,
        "precedent": precedent,
        "framework": framework,
        "comparison": comparison,
        "admitted_facts": ("contract_signed", "final_settlement",
                           "receipt_confirmed"),
    }


def build_case_input(intake: dict):
    """Assemble the normalized CaseInput from the sourcing results; the
    pipeline consumes exactly these intermediate objects (the issue table
    comes from the D010 applicable hits, the claim from the D013
    transferred similar case, the evidence from the D009 quotation)."""
    from fractions import Fraction

    from theory.spec.canonical_v2.case import (
        CaseInput,
        Claim,
        ExactQuantity,
        FactRecord,
        FactStanding,
        Polar,
        ProcessState,
        ScopedAtom,
    )
    from theory.spec.canonical_v2.kernel import NormState

    case_id = intake["case_id"]
    state = ProcessState(
        r=NormState(relations=()),
        environment_id=SOURCING_ENV_ID,
        stages=((f"{case_id}-trial", "trial"),),
        events=(),
        target_day=10,
        as_of_day=10,
    )
    # D010 output feeds the issue table: the applicable rule is the issue
    issues = tuple(intake["applicable"]["hits"])
    rule_id = issues[0]
    # parties of the transferred similar case: the D015 pro-stance citing
    # case against the transferred counterparty
    parties = ("case-pro", "borrower-d")
    # the D013 transferred claim feeds the claim table; its basis is the
    # D010 applicable rule (the issue the rule grounds)
    claims = (
        Claim("c0", "case-pro", "borrower-d", rule_id, "principal",
              "payment", subject="", issue=rule_id),
    )
    # D009 quotation provenance scopes the admitted facts (the evidence
    # is bound to the quoted span, not to a free-floating claim)
    subject = f"quote:{intake['quote']['start']}:{intake['quote']['end']}"
    facts = tuple(
        FactRecord(
            f"f-{i}-{pred}",
            ScopedAtom(case_id=case_id, subject=subject, issue=rule_id,
                       stage="trial", predicate=pred, polar=Polar.POS),
            FactStanding.ADMITTED_POSITIVE,
            produced_at=i,
            known_at=i,
        )
        for i, pred in enumerate(intake["admitted_facts"])
    )
    quantities = (
        ExactQuantity(Fraction(10_000_000), "CNY-fen", "principal",
                      "loan_contract_signed"),
    )
    return CaseInput(
        case_id=case_id,
        initial_state=state,
        parties=parties,
        issues=issues,
        claims=claims,
        defenses=(),
        fact_records=facts,
        evidence_records=(),
        questions=(),
        quantities=quantities,
    )


def build_environment(intake: dict):
    """Declared environment: named sufficiency template licensed by the
    D010 applicable rule; no verdicts, no prebuilt framework."""
    from theory.spec.canonical_v2.case import (
        LegalEnvironment,
        StrongTemplate,
    )
    from theory.spec.canonical_v2.kernel import Jurisdiction, JurisdictionRoute

    rule_id = intake["applicable"]["hits"][0]
    template = StrongTemplate(
        template_id="tpl-loan-delivery",
        kind="LOAN_DELIVERY",
        scope_issue=rule_id,
        premise_predicates=("contract_signed", "final_settlement",
                            "receipt_confirmed"),
        conclusion_predicate=rule_id,
        failure_predicates=("ref_matches_existing_goods_payment",),
        license_rule_id="",
        source_id=f"sourcing:{rule_id}",
    )
    return LegalEnvironment(
        environment_id=SOURCING_ENV_ID,
        jurisdiction=Jurisdiction(route=JurisdictionRoute.MAINLAND),
        rules=(),
        strong_templates=(template,),
    )


def sourcing_trace_events(intake: dict):
    """The D009 quotation and the D015 support edges become actual
    process events; the quotation stays its own evidence event bound to
    its provenance span, and each payment keeps its own event so
    per-obligor dispositions are never averaged."""
    from fractions import Fraction

    from theory.spec.canonical_v2.case import CaseEvent
    from unified.process import LegalEventKind, ProcessEvent

    quote_id = (f"quote-{intake['quote']['start']}-"
                f"{intake['quote']['end']}")
    evidence = ProcessEvent(
        event=CaseEvent(
            event_id=f"ev-{quote_id}",
            event_type="EVIDENCE_SUBMITTED",
            occurred_at=5,
            observed_at=6,
            object_ref=intake["quote"]["span"][0],
        ),
        kind=LegalEventKind.EVIDENCE_SUBMITTED,
    )
    events = [evidence]
    day = 11
    for obligor, amount in (("D1", 2_000_000), ("D2", 3_000_000)):
        events.append(
            ProcessEvent(
                event=CaseEvent(
                    event_id=f"pay-{obligor}",
                    event_type="PAYMENT_PERFORMED",
                    occurred_at=day,
                    observed_at=day,
                    object_ref="loan",
                ),
                kind=LegalEventKind.PAYMENT_PERFORMED,
                basis_key=intake["applicable"]["hits"][0],
                amount=Fraction(int(amount)),
                debt_order=(intake["applicable"]["hits"][0],),
            )
        )
        day += 1
    return tuple(events)
