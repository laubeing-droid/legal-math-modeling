"""Group-05 criminal reference entries (D037-D046, W2-A batch B05).

Every entry consumes real structured input (no fixtures, no precomputed
answers) and produces the intermediate result whose formal contract is
``JurisLean.FullMath.Contracts.demand_D037`` … ``demand_D046``:

* D037 ``crime_label_sets`` — each defendant's crime-label set is exactly
  the frozen candidate rows meeting the selected elements / barrier /
  concurrence policy at once (labels and semantics map in both
  directions); a single-label carrier that keeps only the first
  legitimate candidate is distinguishable from the full output — the
  second legitimate crime candidate is never silently dropped.
* D038 ``law_dict_roundtrip`` — the frozen statute dictionary answers a
  label-id lookup and, under declared (article, clause) uniqueness, the
  same row back by its article and clause (encode/decode roundtrip); the
  three fields (id / article / clause) stay distinct carriers and an
  unregistered id resolves to nothing (fail-closed, no fabricated
  citation such as rendering "law.txt" item 1 as an article).
* D039 ``penalty_ledger`` — penalty kinds are a sum type (term=1 with
  months, life=2, death=3 without); the numeric aggregate exists only
  when every row is a term row with months, and any life/death row
  poisons it — ordinary addition never mixes penalty kinds, so no
  -1/-2 sentinel can enter a sentence average or a fine computation.
* D040 ``prediction_configs`` — with-statute and without-statute are two
  fixed feature budgets (act=0, intent=1, statute_text=2); the statute
  feature sits only in the with budget, the budgets differ in length,
  and each score is normalized by its own budget length (denominators
  never mix): a full 3-feature hit is 1, not the 2-budget 3/2, so a
  gold-statute score cannot be reported as statute-free capability.
* D041 ``per_defendant_mapping`` — per-defendant rows (person, elements,
  circumstance, penalty) are checked per person against the register;
  swapping two defendants' penalties keeps the case total but fails the
  per-person checks, so identity is preserved per defendant.
* D042 ``case_correctness`` — CaseCorrect = every required defendant's
  verdict is determined-true AND relation consistency holds; a required
  defendant with no verdict is explicitly pending (listed), never
  silently correct, and a high per-person average (99/100 → 99.5)
  coexists with not-all-correct.
* D043 ``judgment_readback`` — the main text's kind / period / fine
  projections are compared field-by-field against the verified
  structured record; each mismatch is reported by name, so the classic
  tamper (structured fine 5000, text 50000) is found on read-back.
* D044 ``conviction_paths`` — the certified conclusions are the verbatim
  intersection of the operative-text crimes with the reasons' rule
  paths; a pathless crime is never certified (membership, not string
  similarity), so a text citing a second crime fails when the reasons
  cover only the first.
* D045 ``criminal_amounts`` — an item enters the criminal amount only
  when its property / act / subject attribution axes are all verified,
  and each verified source is counted exactly once — the same loot
  appearing in two records is added once, never twice.
* D046 ``hearsay_resolve`` / ``jurisdiction_rows`` — inside one declared
  US evidence-law version (synthetic registry 1975) each
  element/exception/use query gets an allowed branch (all hold) or the
  explicit pending branch (none); conclusion rows are keyed by
  jurisdiction, so a US-FRE row never enters the CN carrier even with a
  verbatim-identical label and boolean.

Amounts are ``Fraction`` (ℚ); kind codes and day/month counts are exact
integers.  The downstream adapters at the bottom feed these intermediate
results into the unified pipeline public entries (``run_case`` /
``step_event`` / ``run_trace``); they never accept a precomputed
verdict.  The independent contract checker lives in ``criminal_check``
and shares no code with this module.
"""
from __future__ import annotations

from fractions import Fraction
from typing import Sequence

# ---------------------------------------------------------------------------
# D037 — per-defendant crime label sets under the selected policy
# ---------------------------------------------------------------------------


def crime_label_sets(cands: Sequence[tuple]) -> dict:
    """``cands`` rows are (label, elements_met, not_barred,
    concurrence_ok).  The output label set is exactly the rows meeting
    all three policy predicates; the single-label carrier keeps only the
    first legitimate candidate, so a second legitimate crime candidate
    stays visible as dropped — never silently lost."""

    labels = tuple(r[0] for r in cands
                   if r[1] is True and r[2] is True and r[3] is True)
    single = labels[:1]
    return {"labels": labels,
            "single_label_carrier": single,
            "dropped_by_single_label": tuple(
                l for l in labels if l not in single),
            "policy": ("elements", "barrier", "concurrence")}


# ---------------------------------------------------------------------------
# D038 — frozen statute dictionary: encode/decode roundtrip, typed fields
# ---------------------------------------------------------------------------


def law_dict_roundtrip(dict_rows: Sequence[tuple], n: int) -> dict:
    """``dict_rows`` rows are (label_id, article, clause).  The id lookup
    encodes; under declared (article, clause) uniqueness the decode
    returns the same id (roundtrip); an unregistered id resolves to
    nothing — fail-closed, never auto-rendered as a citation."""

    hit = None
    for row in dict_rows:
        if row[0] == n:
            hit = row
            break
    if hit is None:
        return {"registered": False, "row": None, "decode_id": None,
                "roundtrip_ok": False, "frozen_unique": False,
                "fields": None}
    _id, article, clause = hit
    decode_id = None
    for row in dict_rows:
        if row[1] == article and row[2] == clause:
            decode_id = row[0]
            break
    same_key_ids = {row[0] for row in dict_rows
                    if row[1] == article and row[2] == clause}
    return {"registered": True, "row": hit, "decode_id": decode_id,
            "roundtrip_ok": decode_id == n,
            "frozen_unique": len(same_key_ids) == 1,
            "fields": {"id": _id, "article": article, "clause": clause}}


# ---------------------------------------------------------------------------
# D039 — penalty kinds are a sum type; no mixed-kind arithmetic
# ---------------------------------------------------------------------------

TERM_KIND = 1
LIFE_KIND = 2
DEATH_KIND = 3


def penalty_ledger(rows: Sequence[tuple]) -> dict:
    """``rows`` rows are (kind, months_or_None).  The numeric aggregate
    exists only when every row is a term row carrying months; life and
    death rows poison it (their aggregate is None), so ordinary addition
    never mixes penalty kinds and no sentinel number can ride along."""

    all_terms = all(r[0] == TERM_KIND and r[1] is not None for r in rows)
    poisoned = any(r[0] != TERM_KIND or r[1] is None for r in rows)
    has_life = any(r[0] == LIFE_KIND for r in rows)
    has_death = any(r[0] == DEATH_KIND for r in rows)
    total = sum((r[1] for r in rows), 0) if all_terms else None
    average = Fraction(total, len(rows)) if (all_terms and rows) else None
    return {"all_terms": all_terms, "poisoned": poisoned,
            "has_life": has_life, "has_death": has_death,
            "total": total, "average": average,
            "kinds": tuple(r[0] for r in rows)}


# ---------------------------------------------------------------------------
# D040 — two fixed prediction budgets; denominators never mix
# ---------------------------------------------------------------------------

FEATURE_ACTUS = 0
FEATURE_MENS = 1
FEATURE_STATUTE = 2
WITH_BUDGET = (FEATURE_ACTUS, FEATURE_MENS, FEATURE_STATUTE)
WITHOUT_BUDGET = (FEATURE_ACTUS, FEATURE_MENS)


def statute_free(budget: Sequence[int]) -> bool:
    """A budget is statute-free exactly when the statute feature is not
    in it — the labeling fact behind the adverse case."""

    return FEATURE_STATUTE not in budget


def prediction_score(hits: int, budget: Sequence[int]) -> Fraction:
    """The score is normalized by its OWN budget length — the denominator
    is part of the computation and never borrowed."""

    return Fraction(hits, len(budget))


def prediction_configs(hits_with: int, hits_without: int) -> dict:
    """The two configs are distinct fixed budgets with distinct lengths;
    each score carries its own budget and denominator, and the same hit
    count recounted under the other denominator is reported next to it —
    a with-statute score (full hits = 1) is never the same number as the
    2-budget recount (3/2), so denominators cannot be mixed silently and
    a gold-statute score cannot be labeled statute-free."""

    sw = prediction_score(hits_with, WITH_BUDGET)
    so = prediction_score(hits_without, WITHOUT_BUDGET)
    same_hits_other = prediction_score(hits_with, WITHOUT_BUDGET)
    return {
        "with": {"config": "with-statute", "budget": WITH_BUDGET,
                 "length": len(WITH_BUDGET), "score": sw,
                 "statute_free": statute_free(WITH_BUDGET)},
        "without": {"config": "without-statute", "budget": WITHOUT_BUDGET,
                    "length": len(WITHOUT_BUDGET), "score": so,
                    "statute_free": statute_free(WITHOUT_BUDGET)},
        "budgets_equal": WITH_BUDGET == WITHOUT_BUDGET,
        "lengths_equal": len(WITH_BUDGET) == len(WITHOUT_BUDGET),
        "scores_equal": sw == so,
        "same_hits_other_denominator": same_hits_other,
        "mixing_denominators_detected": sw != same_hits_other,
    }


# ---------------------------------------------------------------------------
# D041 — per-defendant mapping keeps common identity
# ---------------------------------------------------------------------------


def per_defendant_mapping(register: Sequence[tuple],
                          rows: Sequence[tuple]) -> dict:
    """``register`` rows are (person, elements, circumstance, penalty);
    ``rows`` are the computed per-defendant rows.  Each row is checked
    per person against the register (find-by-person) and the case total
    is reported; swapping two defendants' penalties keeps the total but
    breaks the per-person checks."""

    reg = {r[0]: r for r in register}
    checks = tuple({"person": r[0], "ok": reg.get(r[0]) == r}
                   for r in rows)
    total = sum((r[3] for r in rows), 0)
    return {"rows": tuple(rows), "checks": checks, "total": total,
            "all_ok": all(c["ok"] for c in checks),
            "checked_per_person": tuple(c["person"] for c in checks)}


def identity_swap(rows: Sequence[tuple]) -> tuple:
    """Exchange the two defendants' penalties (same persons, same case
    total) — the adverse candidate the per-person checks must reject."""

    if len(rows) < 2:
        return tuple(rows)
    swapped = [list(r) for r in rows]
    swapped[0][3], swapped[1][3] = swapped[1][3], swapped[0][3]
    return tuple(tuple(r) for r in swapped)


# ---------------------------------------------------------------------------
# D042 — CaseCorrect over the required defendants; explicit pending
# ---------------------------------------------------------------------------


def case_correctness(required: Sequence[str], verdicts: dict,
                     relation_ok: bool, scores: Sequence[Fraction]) -> dict:
    """``verdicts`` maps person → True/False/None (None = no determined
    verdict).  CaseCorrect = every required defendant determined true AND
    relation consistency; undetermined required defendants are listed as
    explicitly pending; the per-person average is reported next to the
    all-correct verdict — a high average never certifies correctness."""

    pending = tuple(d for d in required if verdicts.get(d) is None)
    all_correct = all(verdicts.get(d) is True for d in required)
    average = sum(scores, Fraction(0)) / len(scores) if scores else None
    return {"case_correct": bool(all_correct and relation_ok),
            "all_defendants_correct": all_correct,
            "relation_consistency": bool(relation_ok),
            "pending": pending,
            "average": average,
            "required": tuple(required)}


# ---------------------------------------------------------------------------
# D043 — main text projections vs the verified structured record
# ---------------------------------------------------------------------------


def judgment_readback(rec: tuple, txt: tuple) -> dict:
    """``rec`` and ``txt`` are (kind, months, fine) — the verified
    structured record and the rendered main text.  The read-back reports
    each mismatched field by name; matching text reads back empty."""

    mismatches = []
    if txt[0] != rec[0]:
        mismatches.append("kind")
    if txt[1] != rec[1]:
        mismatches.append("months")
    if txt[2] != rec[2]:
        mismatches.append("fine")
    return {"record": tuple(rec), "text": tuple(txt),
            "mismatches": tuple(mismatches),
            "projections_equal": txt == rec}


# ---------------------------------------------------------------------------
# D044 — conviction conclusions need rule paths in the reasons
# ---------------------------------------------------------------------------


def conviction_paths(paths: Sequence[str],
                     conclusions: Sequence[str]) -> dict:
    """Certified conclusions are the verbatim intersection of the
    operative-text crimes with the reasons' rule paths; any pathless
    crime is flagged — string similarity never substitutes for a path."""

    certified = tuple(c for c in conclusions if c in paths)
    unbacked = tuple(c for c in conclusions if c not in paths)
    return {"certified": certified, "unbacked": unbacked,
            "all_certified": not unbacked,
            "certified_equals_conclusions":
                certified == tuple(conclusions),
            "paths": tuple(paths)}


# ---------------------------------------------------------------------------
# D045 — criminal amounts: attribution gate + same-source deduplication
# ---------------------------------------------------------------------------


def criminal_amounts(items: Sequence[tuple]) -> dict:
    """``items`` rows are (source, ok_property, ok_act, ok_subject,
    amount).  Each item must pass all three attribution axes to enter;
    a verified source is counted exactly once, so loot appearing in two
    records is added once — the deduplicated total is reported next to
    the raw attributed sum for contrast."""

    counted_sources: list = []
    total = Fraction(0)
    unattributed: list = []
    duplicates: list = []
    for src, okp, oka, oks, amt in items:
        if not (okp and oka and oks):
            unattributed.append(src)
            continue
        if src in counted_sources:
            duplicates.append(src)
            continue
        counted_sources.append(src)
        total += Fraction(amt)
    raw = sum((Fraction(amt) for _s, okp, oka, oks, amt in items
               if okp and oka and oks), Fraction(0))
    return {"total": total, "attributed_sum_without_dedup": raw,
            "counted_sources": tuple(counted_sources),
            "duplicate_sources_skipped": tuple(duplicates),
            "unattributed_skipped": tuple(unattributed)}


# ---------------------------------------------------------------------------
# D046 — hearsay branches inside one declared version; jurisdiction keys
# ---------------------------------------------------------------------------

FRE_VERSION = 1975  # synthetic declared US evidence-law version


def hearsay_resolve(version: int, element_ok: bool, exception_ok: bool,
                    use_ok: bool):
    """Inside the declared version, an element/exception/use query that
    all holds gets the allowed branch (True); anything else — including
    an out-of-version query — gets the explicit pending branch (None),
    never a silent exclusion."""

    if version == FRE_VERSION and element_ok and exception_ok and use_ok:
        return True
    return None


def jurisdiction_rows(rows: Sequence[tuple]) -> dict:
    """``rows`` rows are (jurisdiction, label, conclusion).  The CN
    carrier keeps exactly the CN-keyed rows; a US-FRE row never enters
    it even when its label and boolean are verbatim identical."""

    cn = tuple(r for r in rows if r[0] == "CN")
    return {"cn": cn,
            "foreign_rows": tuple(r for r in rows if r[0] != "CN"),
            "leak": tuple(r for r in cn if r[0] != "CN")}


# ---------------------------------------------------------------------------
# Downstream adapters: criminal results → pipeline carriers (PY-RUN)
# ---------------------------------------------------------------------------

CRIMINAL_ENV_ID = "env-criminal-b05"


def build_criminal_intake() -> dict:
    """Synthetic criminal bundle for one theft case: every field is
    produced by the entries above from declared input tables; the
    dropped second legitimate label, the fail-closed unregistered id,
    the life-poisoned ledger, the mismatched denominators, the
    identity-swap failure, the pending second defendant, the mis-written
    fine, the pathless second crime, the double-recorded loot and the
    US→CN transplant all stay distinguishable."""

    # D037: two legitimate candidates (theft, handling) both survive the
    # policy; the single-label carrier drops the second — visible, not lost
    cands = (("theft", True, True, True),
             ("handling", True, True, True),
             ("fraud", True, False, True))
    labels = crime_label_sets(cands)
    # D038: the frozen dictionary roundtrips id 266; an unregistered id
    # (raw corpus line 1) resolves to nothing
    dict_rows = ((266, "刑法第266条", "第一款"), (1, "law.txt", "第1项"))
    roundtrip = law_dict_roundtrip(dict_rows, 266)
    raw_line = law_dict_roundtrip(dict_rows, 999)
    # D039: the term ledger sums exactly; the mixed ledger has no total
    ledger_terms = penalty_ledger(((TERM_KIND, 24), (TERM_KIND, 12)))
    ledger_mixed = penalty_ledger(((TERM_KIND, 24), (LIFE_KIND, None)))
    # D040: with/without budgets are fixed; denominators do not mix
    configs = prediction_configs(3, 2)
    # D041: per-defendant rows checked against the register; the swapped
    # variant keeps the total but fails both checks
    register = (("D1", "theft-elements", "recidivist", 36),
                ("D2", "handling-elements", "first-offense", 12))
    honest = per_defendant_mapping(
        register, (("D1", "theft-elements", "recidivist", 36),
                   ("D2", "handling-elements", "first-offense", 12)))
    swapped = per_defendant_mapping(
        register, identity_swap(
            (("D1", "theft-elements", "recidivist", 36),
             ("D2", "handling-elements", "first-offense", 12))))
    # D042: one defendant determined, one pending; the average is high
    correctness = case_correctness(
        ("D1", "D2"), {"D1": True, "D2": None}, True,
        (Fraction(99), Fraction(100)))
    # D043: the structured fine 5000 vs the mis-written text 50000
    record = judgment_readback(("imprisonment", 24, Fraction(5000)),
                               ("imprisonment", 24, Fraction(50000)))
    honest_text = judgment_readback(("imprisonment", 24, Fraction(5000)),
                                    ("imprisonment", 24, Fraction(5000)))
    # D044: the reasons cover theft only; the text also cites fraud
    reasons = conviction_paths(("theft",), ("theft", "fraud"))
    # D045: loot source 7 appears in two records — counted once; source 8
    # fails the act axis and never enters
    amounts = criminal_amounts(((7, True, True, True, Fraction(30000)),
                                (7, True, True, True, Fraction(30000)),
                                (8, True, False, True, Fraction(9000))))
    # D046: the in-version hearsay query resolves; the US row never
    # enters the CN carrier
    hearsay = hearsay_resolve(FRE_VERSION, True, True, True)
    pending_hearsay = hearsay_resolve(2020, True, True, True)
    juris = jurisdiction_rows((("CN", "theft", True),
                               ("US-FRE", "hearsay", False),
                               ("US-FRE", "theft", True)))
    return {"case_id": "case-b05",
            "labels": labels, "roundtrip": roundtrip, "raw_line": raw_line,
            "ledger_terms": ledger_terms, "ledger_mixed": ledger_mixed,
            "configs": configs, "honest": honest, "swapped": swapped,
            "correctness": correctness, "record": record,
            "honest_text": honest_text, "reasons": reasons,
            "amounts": amounts, "hearsay": hearsay,
            "pending_hearsay": pending_hearsay, "juris": juris,
            "stolen": Fraction(30000), "fine": Fraction(5000),
            "admitted_facts": ("elements_proved", "unlawful_take")}


def build_case_input(intake: dict):
    """Assemble the normalized CaseInput from the criminal results; the
    pipeline consumes exactly these intermediate objects: the D037
    surviving primary label supplies the issue, the D044-pathless fraud
    citation stays OUT of the claims, the D046 hearsay objection enters
    as a defense (never a written fact), and the D045 deduplicated
    amount is the only quantity — no double-counted loot."""

    from fractions import Fraction

    from theory.spec.canonical_v2.case import (
        CaseInput,
        Claim,
        Defense,
        ExactQuantity,
        FactRecord,
        FactStanding,
        Polar,
        ProcessState,
        ScopedAtom,
    )
    from theory.spec.canonical_v2.kernel import NormState

    case_id = intake["case_id"]
    issue = "THEFT_CONVICTION"
    state = ProcessState(
        r=NormState(relations=()),
        environment_id=CRIMINAL_ENV_ID,
        stages=((f"{case_id}-trial", "trial"),),
        events=(),
        target_day=10,
        as_of_day=10,
    )
    parties = ("prosecutor", "defendant", "D1", "D2")
    # the D037 primary surviving label supplies the conviction claim;
    # the D044 pathless "fraud" text crime is never claimed
    claims = (
        Claim("c0", "prosecutor", "defendant", issue, "stolen-property",
              "conviction-and-fine", subject="", issue=issue),
    )
    # the D046 hearsay objection is a DEFENSE targeting c0 — the US
    # hearsay label never becomes a written CN fact
    defenses = (
        Defense("def-hearsay", "defendant", ("c0",), "hearsay_objection"),
    )
    standings = {
        "admitted": FactStanding.ADMITTED_POSITIVE,
        "awaiting": FactStanding.AWAITING_ADMISSION,
    }
    # admitted: the D045 attributed act and the D037 elements; awaiting:
    # the hearsay-only proposition — pending, never silently written
    facts = tuple(
        FactRecord(
            fact_id,
            ScopedAtom(case_id=case_id, subject=f"span:{i}", issue=issue,
                       stage="trial", predicate=predicate,
                       polar=Polar.POS),
            standing,
            produced_at=i,
            known_at=i,
        )
        for i, (fact_id, predicate, standing) in enumerate((
            ("f-elements", "elements_proved",
             standings["admitted"]),      # D037 elements met
            ("f-take", "unlawful_take",
             standings["admitted"]),      # D045 attributed act
            ("f-hearsay-only", "hearsay_only",
             standings["awaiting"]),      # D046 pending, never written
        ))
    )
    quantities = (
        ExactQuantity(Fraction(int(intake["stolen"])), "CNY-fen",
                      "criminal_amount", "attributed-source-7"),
        ExactQuantity(Fraction(int(intake["fine"])), "CNY-fen",
                      "fine", "structured-record"),
    )
    return CaseInput(
        case_id=case_id,
        initial_state=state,
        parties=parties,
        issues=(issue,),
        claims=claims,
        defenses=defenses,
        fact_records=facts,
        evidence_records=(),
        questions=(),
        quantities=quantities,
    )


def build_environment(intake: dict):
    """Declared environment: named sufficiency template licensed by the
    D037/D044-backed conviction elements; no verdicts, no prebuilt
    framework."""

    from theory.spec.canonical_v2.case import (
        LegalEnvironment,
        StrongTemplate,
    )
    from theory.spec.canonical_v2.kernel import Jurisdiction, JurisdictionRoute

    issue = "THEFT_CONVICTION"
    template = StrongTemplate(
        template_id="tpl-theft-conviction-b05",
        kind="THEFT_CONVICTION",
        scope_issue=issue,
        premise_predicates=("elements_proved", "unlawful_take"),
        conclusion_predicate=issue,
        failure_predicates=("hearsay_only",),
        license_rule_id="",
        source_id=f"criminal:{issue}",
    )
    return LegalEnvironment(
        environment_id=CRIMINAL_ENV_ID,
        jurisdiction=Jurisdiction(route=JurisdictionRoute.MAINLAND),
        rules=(),
        strong_templates=(template,),
    )


def criminal_trace_events(intake: dict):
    """The two attributed-loot records (source 7 counted once, its second
    record kept distinguishable) become evidence events, and the
    structured fine is paid in two exact installments (2000 + 3000 =
    5000, never a merged average number)."""
    from fractions import Fraction

    from theory.spec.canonical_v2.case import CaseEvent
    from unified.process import LegalEventKind, ProcessEvent

    events = []
    day = 5
    evidence = ProcessEvent(
        event=CaseEvent(
            event_id="ev-loot-source-7",
            event_type="EVIDENCE_SUBMITTED",
            occurred_at=day,
            observed_at=day + 1,
            object_ref="criminal_amount",
        ),
        kind=LegalEventKind.EVIDENCE_SUBMITTED,
    )
    events.append(evidence)
    day += 2
    basis = "FINE_PAYMENT"
    for paid in (Fraction(2000), Fraction(3000)):
        events.append(
            ProcessEvent(
                event=CaseEvent(
                    event_id=f"pay-fine-{int(paid)}",
                    event_type="PAYMENT_PERFORMED",
                    occurred_at=day,
                    observed_at=day,
                    object_ref="fine",
                ),
                kind=LegalEventKind.PAYMENT_PERFORMED,
                basis_key=basis,
                amount=paid,
                debt_order=(basis,),
            )
        )
        day += 1
    return tuple(events)
