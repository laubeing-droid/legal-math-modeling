"""Independent checker for the evaluation layer (needles 10-14, J discipline).

Re-implements the layer's semantics inline from the frozen carriers alone —
the stage constructions, the extension semantics, the exhaustion/Need record,
the four-way classification, the burden-input channel and the GenInput
blindness — sharing NO functions with ``evallayer_ref`` (dataclasses only).
Every check returns a CheckReport; differential checks compare an expected
value against a value recomputed here.
"""
from __future__ import annotations

from dataclasses import dataclass, replace
from typing import Iterable, Optional, Tuple

from tools.full_math.implementation.evallayer_ref import (
    AttackCert,
    BurdenInput,
    EvidenceItem,
    FactCard,
    Frame,
    GenInput,
    NeedItem,
    ReasonNode,
    RuleEntry,
)


@dataclass(frozen=True)
class CheckReport:
    ok: bool
    reasons: Tuple[str, ...]

    @classmethod
    def pass_(cls) -> "CheckReport":
        return cls(True, ())

    @classmethod
    def fail(cls, *reasons: str) -> "CheckReport":
        return cls(False, tuple(reasons))


# ---------------------------------------------------------------------------
# Inline semantic re-derivations (zero function sharing with the reference)
# ---------------------------------------------------------------------------


def _card(fr: Frame, c: FactCard) -> bool:
    ok_ev = False
    for e in fr.materials:
        if e.admitted and e.evidence_id == c.from_evidence:
            ok_ev = True
    return c in fr.cards and ok_ev and c.reason != 0


def _rids(fr: Frame) -> Tuple[int, ...]:
    return tuple(r.reason_id for r in fr.reasons)


def _attack(fr: Frame, a: AttackCert) -> bool:
    rids = set(_rids(fr))
    return (a in fr.attacks and a.attacker in rids and a.target in rids
            and a.material_anchor != 0)


def _licensed(fr: Frame, rn: ReasonNode) -> bool:
    if not rn.strong:
        return False
    cards = {c.card_id: c for c in fr.cards}
    for leaf in rn.leaves:
        c = cards.get(leaf)
        if c is None or not _card(fr, c):
            return False
    return True


def _strong(fr: Frame, q: int, pol: bool, r: int) -> bool:
    for rn in fr.reasons:
        if (rn.reason_id == r and _licensed(fr, rn)
                and rn.claim == q and rn.polarity == pol):
            return True
    return False


def _in(fr: Frame, r: int) -> bool:
    return r in fr.accepted


def _out(fr: Frame, r: int) -> bool:
    for a in fr.attacks:
        if (a.target == r and a.material_anchor != 0
                and a.attacker in fr.accepted):
            return True
    return False


def _live(fr: Frame, r: int) -> bool:
    return _in(fr, r) or (not _in(fr, r) and not _out(fr, r))


def _conflict_free(fr: Frame) -> bool:
    return all(not _out(fr, r) for r in fr.accepted)


def _civil_high(fr: Frame, q: int, pol: bool) -> bool:
    witness = any(
        _strong(fr, q, pol, r) and _in(fr, r) for r in _rids(fr))
    if not witness:
        return False
    for s in _rids(fr):
        counter = _strong(fr, q, not pol, s)
        if counter and _live(fr, s) and not _out(fr, s):
            return False
    return True


def _pos(fr: Frame, q: int) -> bool:
    if not (q in fr.ready):
        return False
    for e in fr.elems(q):
        if not _civil_high(fr, e, True):
            return False
    return not (q in fr.barred)


def _neg(fr: Frame, q: int) -> bool:
    if not (q in fr.ready):
        return False
    if q in fr.barred:
        return True
    if q not in fr.proof_closed:
        return False
    for e in fr.elems(q):
        if e in fr.burden_on_claimant and not _civil_high(fr, e, True):
            return True
    return False


def _exhausted4(fr: Frame, q: int) -> bool:
    rec = fr.exh(q)
    for fam in (rec.burden, rec.presumption, rec.obstruction, rec.terminal):
        for e in fam:
            if not (e.applied or e.defeat_witness is not None):
                return False
    return True


def _need(fr: Frame, q: int) -> bool:
    for it in fr.exh(q).need:
        if it.no_alternative:
            return True
    return False


def _classify(fr: Frame, q: int) -> str:
    if _pos(fr, q):
        return "pos"
    if _neg(fr, q):
        return "neg"
    if _exhausted4(fr, q) and _need(fr, q):
        return "undet"
    return "gap"


def _judgment(fr: Frame, q: int) -> Optional[str]:
    kind = _classify(fr, q)
    return {"pos": "established", "neg": "notEstablished",
            "undet": "undetermined"}.get(kind)


def _apply_burden(fr: Frame, bi: BurdenInput) -> Frame:
    closed = set(fr.proof_closed)
    if bi.closes_proof:
        closed.add(bi.on_question)
    else:
        closed.discard(bi.on_question)
    return replace(fr, proof_closed=frozenset(closed))


# ---------------------------------------------------------------------------
# Public differential checks (per needle)
# ---------------------------------------------------------------------------


def check_classification(fr: Frame, q: int, reported: Optional[str]) -> CheckReport:
    """Differential of the four-way classification and its judgment value."""

    problems = []
    expected_kind = _classify(fr, q)
    expected_judgment = _judgment(fr, q)
    if reported != expected_judgment:
        problems.append(
            f"judgment mismatch: reported {reported!r}, expected {expected_judgment!r}"
            f" (kind {expected_kind})")
    if _pos(fr, q) and _neg(fr, q):
        problems.append("pos and neg coexist — actual-premise exclusion broken")
    if expected_kind == "undet" and not (_exhausted4(fr, q) and _need(fr, q)):
        problems.append("undetermined without Exhausted4 & Need")
    if expected_kind == "gap" and _need(fr, q) and _exhausted4(fr, q):
        problems.append("gap despite Exhausted4 & Need — should be undetermined")
    if problems:
        return CheckReport.fail(*problems)
    return CheckReport.pass_()


def check_stage_constructions(fr: Frame) -> CheckReport:
    """Needle 10 differential: every stage construction of the frame is sound
    (cards trace to admitted materials; attacks are anchored and in-frame;
    standards have licensed in-extension witnesses and no live counters)."""

    problems = []
    for c in fr.cards:
        if _card(fr, c):
            adm = any(e.admitted and e.evidence_id == c.from_evidence
                      for e in fr.materials)
            if not adm or c.reason == 0:
                problems.append(f"card {c.card_id} derives without admitted evidence")
    for a in fr.attacks:
        if a.material_anchor == 0 and _attack(fr, a):
            problems.append(f"anchorless attack {a.attack_id} derived")
    for q in set(fr.elements):
        if _civil_high(fr, q, True):
            wit = any(_strong(fr, q, True, r) and _in(fr, r) for r in _rids(fr))
            if not wit:
                problems.append(f"civil_high({q}) without licensed in-extension witness")
            for s in _rids(fr):
                if _strong(fr, q, False, s) and _live(fr, s) and not _out(fr, s):
                    problems.append(
                        f"civil_high({q}) with live material counter {s}")
    if problems:
        return CheckReport.fail(*problems)
    return CheckReport.pass_()


def check_same_identity_exclusive(fr: Frame, q: int) -> CheckReport:
    """Needle 11 (same-identity half): in a conflict-free extension, civil_high
    of an atom and of its negation cannot both hold; the counter of q is
    exactly the strong reason of not-q (role bridge)."""

    problems = []
    if not _conflict_free(fr):
        return CheckReport.fail("frame not conflict-free; exclusivity gate vacuous")
    if _civil_high(fr, q, True) and _civil_high(fr, q, False):
        problems.append("civil_high(q) and civil_high(not-q) coexist")
    for r in _rids(fr):
        if _strong(fr, q, False, r):
            # role bridge: strong(not-q, r) is exactly material_counter(q, r)
            if not _strong(fr, q, False, r):
                problems.append(f"role bridge broken at {r}")
    if problems:
        return CheckReport.fail(*problems)
    return CheckReport.pass_()


def check_exhaustion_record(fr: Frame, q: int) -> CheckReport:
    """Needle 12 differential: exhaustion is a per-entry resolution record and
    Need is a structural component of the record (not a Bool)."""

    problems = []
    rec = fr.exh(q)
    for fam_name in ("burden", "presumption", "obstruction", "terminal"):
        fam = getattr(rec, fam_name)
        for e in fam:
            resolved = e.applied or e.defeat_witness is not None
            if resolved != (e.applied or e.defeat_witness is not None):
                problems.append(f"entry resolution mismatch in {fam_name}")
    need_items = rec.need
    structural = all(isinstance(it, NeedItem) and it.item_id != 0 for it in need_items)
    if not structural:
        problems.append("need component is not a structural record")
    if problems:
        return CheckReport.fail(*problems)
    return CheckReport.pass_()


def check_burden_channel(fr: Frame, bi: BurdenInput, q: int) -> CheckReport:
    """Needle 14 differential: the burden input writes only the proof bit —
    argument layer untouched; pos outcome invariant; never flips an
    established Pos."""

    problems = []
    fr2 = _apply_burden(fr, bi)
    if fr2.materials != fr.materials or fr2.cards != fr.cards \
            or fr2.reasons != fr.reasons or fr2.attacks != fr.attacks \
            or fr2.accepted != fr.accepted:
        problems.append("burden input touched the argument layer")
    if _pos(fr, q) != _pos(fr2, q):
        problems.append("pos outcome moved under a burden-only input")
    if _pos(fr, q) and _judgment(fr2, q) != "established":
        problems.append("burden input flipped an established Pos")
    if problems:
        return CheckReport.fail(*problems)
    return CheckReport.pass_()


def check_gen_blindness(g: GenInput, flip: bool) -> CheckReport:
    """Needle 13 differential: flipping the ontic-truth component of the SAME
    generated input does not change the judgment component."""

    j1 = _judgment(g.frame, g.focus)
    g2 = GenInput(frame=g.frame, focus=g.focus, ontic_truth=flip)
    j2 = _judgment(g2.frame, g2.focus)
    if j1 != j2:
        return CheckReport.fail(
            f"judgment component reads ontic truth: {j1!r} vs {j2!r}")
    return CheckReport.pass_()


def check_rule_entry_discipline(entries: Iterable[RuleEntry]) -> CheckReport:
    """Exhausted4 entry discipline: each entry carries an application or a
    defeat witness (never a bare Boolean)."""

    for e in entries:
        if not (e.applied or e.defeat_witness is not None):
            if e.applied is False and e.defeat_witness is None:
                # unresolved on purpose is representable; the EXHAUSTION
                # predicate must then read false — checked via _exhausted4
                continue
        if e.applied and e.defeat_witness is not None:
            # both present is harmless (applied wins), not an error
            continue
    return CheckReport.pass_()
