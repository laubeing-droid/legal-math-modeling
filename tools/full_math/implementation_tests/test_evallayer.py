"""Evaluation-layer tests for needles 10-14 (W1-12; plan section 5, I:764-768).

Needle 10 eval_has_licensed_derivation: per-construction soundness (card/
attack/standard/final), anchorless-attack rejection (negative), live-counter
blocking (negative), same-snapshot finalization closure, and the end-to-end
licensed-derivation traceability of a Pos outcome.

Needle 11 final_binary_decisions_exclusive: Pos/Neg exclusion from ACTUAL
premises (no conflict-freeness assumption) swept over adversarial frames, and
the strong-reason same-identity exclusion of CivilHigh under a conflict-free
extension.

Needle 12 final_undetermined_iff_exhausted: corrected iff WITH the structural
Need component; the old simple form REFUTED (gap frame: exhausted + no binary
+ no Need reads None, never undetermined); the fragment coverage theorem
(covered + no Need forces a binary outcome); undetermined witness.

Needle 13 proof_failure_not_ontic_negation: one GenInput whose record-truth
side is TRUE while the derivation side REALLY fails on the same input
(material present, content matching, not admitted -> card rejected -> standard
unavailable -> burden produces notEstablished); evaluation blind to the ontic
truth.

Needle 14 argument_undec_not_final_undetermined: a NEW statutory burden input
(independent channel) — before it no binary finalization (gap), after it
notEstablished (not undetermined), argument layer untouched throughout.

Receipt note (W1-12 batch form): the 60-needle table has no slot in
tools/full_math/spec/REQUIREMENTS.json (217 FullMath ids only), so there is no
validate_binding row for W1:10..14; the receipt for this batch is recorded in
.local/agent_W12_eval_layer_report.md per the W1-wave convention, and this
suite pins the Lean sources by name.
"""
from pathlib import Path

import pytest

from tools.full_math.implementation import evallayer_ref as R
from tools.full_math.implementation import evallayer_check as K

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[2]

LEAN_MODULE = (REPO / 'proofs/lean/juris_lean/JurisLean/Seams/'
               'UnifiedEvalLayer.lean')

NEEDLE_THEOREMS = (
    'eval_has_licensed_derivation',
    'final_binary_decisions_exclusive',
    'final_undetermined_iff_exhausted',
    'proof_failure_not_ontic_negation',
    'argument_undec_not_final_undetermined',
)


# ---------------------------------------------------------------------------
# Source pinning (W1-12 batch receipt anchor)
# ---------------------------------------------------------------------------


def test_lean_module_pins_all_five_needles():
    """The Lean contract file exists and declares the five needle theorems by
    their original acceptance names (appendix I.13)."""
    text = LEAN_MODULE.read_text(encoding='utf-8')
    for name in NEEDLE_THEOREMS:
        assert f'theorem {name}' in text, name


# ---------------------------------------------------------------------------
# Needle 10: per-construction soundness + traceability + closure
# ---------------------------------------------------------------------------


def test_card_construction_positive_and_negative():
    """Card derives from an admitted material with a named reason (positive);
    the same card is REJECTED when the material is not admitted (negative —
    the needle-13 material state, kept independently)."""
    assert R.legal_derives_card(R.N11_FRAME, R.N11_CARD) is True
    assert R.legal_derives_card(R.N13_FRAME, R.N13_CARD) is False
    rep = K.check_stage_constructions(R.N11_FRAME)
    assert rep.ok, rep.reasons
    rep = K.check_stage_constructions(R.N13_FRAME)
    assert rep.ok, rep.reasons


def test_anchorless_attack_never_derives():
    """Anchorless certificate sits IN the attack table yet never derives
    (only 'not adopted' is not an attack premise)."""
    a = R.N10_ANCHORLESS
    assert a in R.N10_FRAME.attacks
    assert a.material_anchor == 0
    assert R.legal_derives_attack(R.N10_FRAME, a) is False
    assert K.check_stage_constructions(R.N10_FRAME).ok


def test_standard_holds_and_is_blocked_by_live_counter():
    """CivilHigh holds on the full positive chain (positive) and is BLOCKED by
    an unresolved live material counter (negative frame: both-polarity strong
    reasons accepted, no attacks -> the counter is live and not out)."""
    assert R.legal_derives_standard(R.N11_FRAME, 2) is True

    neg_reason = R.ReasonNode(reason_id=40, claim=2, polarity=False,
                              strong=True, leaves=(25,), warrant=8)
    fr = R.replace(
        R.N11_FRAME,
        reasons=R.N11_FRAME.reasons + (neg_reason,),
        accepted=R.N11_FRAME.accepted + (40,))
    assert R.conflict_free(fr) is True
    # same-identity role bridge: the negative strong reason IS the counter
    assert R.material_counter(fr, 2, 40) is True
    assert R.live_ext(fr, 40) is True
    assert R.out_ext(fr, 40) is False
    assert R.legal_derives_standard(fr, 2) is False
    assert K.check_stage_constructions(fr).ok


def test_finalization_closed_and_traceability():
    """Needle 10 flagship (Python side): a Pos outcome's every element has an
    in-extension licensed strong reason whose leaves all trace to ADMITTED
    materials; and the frame-attack closure holds."""

    fr = R.N11_FRAME
    assert R.pos_outcome(fr, 1) is True
    for e in fr.elems(1):
        witnesses = [
            rn for rn in fr.reasons
            if rn.claim == e and rn.polarity and rn.reason_id in fr.accepted
            and R.reason_licensed(fr, rn)]
        assert witnesses, 'no licensed in-extension witness'
        for rn in witnesses:
            for leaf in rn.leaves:
                card = next(c for c in fr.cards if c.card_id == leaf)
                assert R.legal_derives_card(fr, card)
                assert any(
                    m.admitted and m.evidence_id == card.from_evidence
                    for m in fr.materials)
    # same-snapshot closure: every live counter of an element is out
    for e in fr.elems(1):
        for s in R.reason_ids(fr):
            if R.material_counter(fr, e, s):
                assert (not R.live_ext(fr, s)) or R.out_ext(fr, s)


def test_burden_channel_leaves_evidence_layer():
    """Stage separation: the burden input does not move card/attack/standard
    derivability (burden output never feeds back as evidence)."""
    fr = R.N13_FRAME
    fr2 = R.apply_burden_input(fr, R.N14_BURDEN_INPUT)
    assert R.legal_derives_card(fr, R.N13_CARD) == R.legal_derives_card(fr2, R.N13_CARD)
    for a in fr.attacks:
        assert R.legal_derives_attack(fr, a) == R.legal_derives_attack(fr2, a)
    assert R.legal_derives_standard(fr, 2) == R.legal_derives_standard(fr2, 2)
    assert K.check_burden_channel(fr, R.N14_BURDEN_INPUT, 1).ok


# ---------------------------------------------------------------------------
# Needle 11: exclusion from actual premises + same-identity counter role
# ---------------------------------------------------------------------------


def _frames_family():
    """Adversarial family: bar/burden/proof-closure/establishment variants of
    the witness frames (no conflict-freeness assumption involved)."""
    out = [R.N11_FRAME, R.N13_FRAME, R.N14_FRAME, R.N12_BASE_FRAME,
           R.N12_UNDET_FRAME]
    for barred in (True, False):
        for closed in (True, False):
            out.append(R.replace(
                R.N13_FRAME,
                barred=frozenset({1}) if barred else frozenset(),
                proof_closed=frozenset({1}) if closed else frozenset()))
    return out


def test_pos_neg_exclusive_on_adversarial_family():
    """Pos and Neg never coexist — the exclusion is read off the ACTUAL
    premise structure (first Neg branch vs Pos's ¬B; second vs E)."""
    for fr in _frames_family():
        for q in (1, 2, 7):
            pos, neg = R.pos_outcome(fr, q), R.neg_outcome(fr, q)
            assert not (pos and neg), (fr, q)
            rep = K.check_classification(fr, q, R.final_judgment(fr, q))
            assert rep.ok, rep.reasons


def test_civil_high_same_identity_exclusive():
    """Under a conflict-free extension, CivilHigh(q) and CivilHigh(¬q) cannot
    both hold; on the witness the positive side holds and the negative side
    fails (both non-vacuous)."""
    fr = R.N11_FRAME
    assert R.conflict_free(fr) is True
    assert R.civil_high(fr, 2) is True
    assert R.civil_high_neg(fr, 2) is False
    assert K.check_same_identity_exclusive(fr, 2).ok

    # both-polarity coexistence attempt: neither standard survives (the
    # counter is live and unanswered) — exclusivity not violated either way
    neg_reason = R.ReasonNode(reason_id=40, claim=2, polarity=False,
                              strong=True, leaves=(25,), warrant=8)
    fr2 = R.replace(fr, reasons=fr.reasons + (neg_reason,),
                    accepted=fr.accepted + (40,))
    assert R.conflict_free(fr2) is True
    assert R.civil_high(fr2, 2) is False
    assert R.civil_high_neg(fr2, 2) is False
    assert K.check_same_identity_exclusive(fr2, 2).ok


def test_role_bridge_is_definitional():
    """Strong(¬q, r) IS MaterialCounter(q, r) — the same-identity second role."""
    assert R.strong_for(R.N11_FRAME, 2, False, 35) == \
        R.material_counter(R.N11_FRAME, 2, 35)


# ---------------------------------------------------------------------------
# Needle 12: corrected iff + old simple form refuted + fragment coverage
# ---------------------------------------------------------------------------


def test_corrected_iff_on_all_witnesses():
    """undetermined ⇔ Exhausted4 ∧ Need ∧ ¬Pos ∧ ¬Neg on every witness."""
    for fr in (R.N11_FRAME, R.N12_BASE_FRAME, R.N12_UNDET_FRAME,
               R.N13_FRAME, R.N14_FRAME):
        q = 1
        lhs = R.final_judgment(fr, q) == R.UNDETERMINED
        rhs = (R.exhausted4(fr, q) and R.need_holds(fr, q)
               and not R.pos_outcome(fr, q) and not R.neg_outcome(fr, q))
        assert lhs == rhs, (fr, lhs, rhs)
        assert K.check_exhaustion_record(fr, q).ok
        assert K.check_classification(fr, q, R.final_judgment(fr, q)).ok


def test_old_simple_form_refuted_by_gap_frame():
    """The old simplification ('exhausted and no binary ⇔ undetermined') is
    FALSE: the gap frame is exhausted, has no binary outcome, and NO Need —
    it reads as the norm disposal gap (None), never as undetermined."""
    fr = R.N12_BASE_FRAME
    assert R.exhausted4(fr, 1) is True
    assert R.need_holds(fr, 1) is False
    assert R.pos_outcome(fr, 1) is False
    assert R.neg_outcome(fr, 1) is False
    assert R.final_judgment(fr, 1) is None
    assert R.final_judgment(fr, 1) != R.UNDETERMINED


def test_undetermined_witness_nonvacuous():
    """Exhausted + Need (prior-pending, no statutory alternative) + no binary
    ⇒ undetermined (the corrected iff's positive instance)."""
    fr = R.N12_UNDET_FRAME
    assert R.need_holds(fr, 1) is True
    assert R.final_judgment(fr, 1) == R.UNDETERMINED


def test_covered_fragment_forces_binary():
    """Fragment coverage theorem (Python side): covered (Ready+F+all elements
    on the claimant burden path) and NO Need ⇒ Pos or Neg — hence inside the
    fragment, no-binary implies Need and the old simple form is re-derived."""

    def sweep(fr):
        q = 1
        if R.covered_fragment(fr, q) and not R.need_holds(fr, q):
            assert (R.pos_outcome(fr, q) or R.neg_outcome(fr, q)), fr
        if R.covered_fragment(fr, q) and not R.pos_outcome(fr, q) \
                and not R.neg_outcome(fr, q):
            assert R.need_holds(fr, q), fr

    sweep(R.N13_FRAME)          # covered, no need -> Neg fires
    assert R.covered_fragment(R.N13_FRAME, 1) is True
    assert R.need_holds(R.N13_FRAME, 1) is False
    assert R.final_judgment(R.N13_FRAME, 1) == R.NOT_ESTABLISHED

    # counter-variant: burden NOT on claimant -> not covered -> gap allowed
    assert R.covered_fragment(R.N12_BASE_FRAME, 1) is False
    assert R.final_judgment(R.N12_BASE_FRAME, 1) is None


# ---------------------------------------------------------------------------
# Needle 13: same-input record truth + real derivation failure
# ---------------------------------------------------------------------------


def test_proof_failure_not_ontic_negation_same_input():
    """One GenInput: ontic truth TRUE (the material recording the fact is
    present with matching content) AND the derivation REALLY fails on the
    same frame (card rejected, standard unavailable) AND the burden rule
    produces notEstablished — three readings of the same g."""
    g = R.N13_GEN
    e = 2
    assert e in g.frame.elems(g.focus)
    assert g.ontic_truth is True
    # derivation side, on the SAME frame: material present, content matches,
    # but not admitted -> card rejected -> standard unavailable
    assert any(m.content_claim == e and not m.admitted
               for m in g.frame.materials)
    assert all(not R.legal_derives_card(g.frame, c) for c in g.frame.cards)
    assert R.legal_derives_standard(g.frame, e) is False
    # judgment side: burden rule produces notEstablished (not undetermined)
    assert R.gen_truth_judgment(g) == (True, R.NOT_ESTABLISHED)
    assert K.check_stage_constructions(g.frame).ok
    assert K.check_classification(g.frame, 1, R.final_judgment(g.frame, 1)).ok


def test_evaluation_blind_to_ontic_truth():
    """Flipping the record-truth component of the SAME generated input leaves
    the judgment component unchanged (knowing R later changes nothing)."""
    assert K.check_gen_blindness(R.N13_GEN, False).ok
    assert K.check_gen_blindness(R.N13_GEN, True).ok
    g_flip = R.GenInput(frame=R.N13_GEN.frame, focus=R.N13_GEN.focus,
                        ontic_truth=False)
    assert R.gen_truth_judgment(g_flip) == (False, R.NOT_ESTABLISHED)


# ---------------------------------------------------------------------------
# Needle 14: new statutory burden input channel
# ---------------------------------------------------------------------------


def test_burden_input_triggers_reevaluation():
    """Before the input: proof opportunity open -> no binary finalization
    (gap) — missing evidence does NOT auto-produce a burden outcome.  After:
    the SAME snapshot re-evaluates to notEstablished (and is not
    undetermined)."""
    fr = R.N14_FRAME
    bi = R.N14_BURDEN_INPUT
    assert bi.input_id != 0 and bi.statutory_basis != 0
    assert fr.f_closed(1) is False
    assert R.final_judgment(fr, 1) is None
    fr2 = R.apply_burden_input(fr, bi)
    assert fr2.f_closed(1) is True
    assert R.neg_outcome(fr2, 1) is True
    assert R.final_judgment(fr2, 1) == R.NOT_ESTABLISHED
    assert R.final_judgment(fr2, 1) != R.UNDETERMINED
    assert K.check_classification(fr2, 1, R.final_judgment(fr2, 1)).ok
    assert K.check_burden_channel(fr, bi, 1).ok


def test_argument_layer_untouched_and_unaccepted():
    """The burden input writes only the proof bit: materials/cards/reasons/
    attacks/accepted are identical; the claim reason stays OUT of the
    accepted extension before and after (undecided at the argument layer,
    finalized as notEstablished at the final layer)."""
    fr = R.N14_FRAME
    fr2 = R.apply_burden_input(fr, R.N14_BURDEN_INPUT)
    assert fr2.materials == fr.materials
    assert fr2.cards == fr.cards
    assert fr2.reasons == fr.reasons
    assert fr2.attacks == fr.attacks
    assert fr2.accepted == fr.accepted
    for f in (fr, fr2):
        assert not R.in_ext(f, 30)


def test_burden_input_never_flips_established_pos():
    """A burden-only input cannot flip an established Pos (Pos invariance +
    actual-premise exclusion)."""
    fr = R.N11_FRAME
    assert R.final_judgment(fr, 1) == R.ESTABLISHED
    for closed in (True, False):
        bi = R.BurdenInput(input_id=7, statutory_basis=55, on_question=1,
                           closes_proof=closed)
        fr2 = R.apply_burden_input(fr, bi)
        assert R.pos_outcome(fr2, 1) is True
        assert R.final_judgment(fr2, 1) == R.ESTABLISHED
        assert K.check_burden_channel(fr, bi, 1).ok


def test_general_trigger_conditions():
    """The general re-evaluation theorem's premise shape: ready + F-written +
    element with claimant burden not established + not pos ⇒ notEstablished."""
    fr = R.N14_FRAME
    bi = R.N14_BURDEN_INPUT
    assert fr.is_ready(1)
    assert any(fr.burden_on(e) and not R.civil_high(fr, e)
               for e in fr.elems(1))
    assert not R.pos_outcome(fr, 1)
    assert bi.on_question == 1 and bi.closes_proof
    assert R.final_judgment(R.apply_burden_input(fr, bi), 1) == R.NOT_ESTABLISHED


if __name__ == '__main__':
    raise SystemExit(pytest.main([__file__, '-q']))
