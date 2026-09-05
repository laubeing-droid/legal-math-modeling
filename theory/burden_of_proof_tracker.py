#!/usr/bin/env python3
"""
Burden of Proof Tracker (方向 2)

Models burden of proof as a state transfer function between Kripke worlds.

Key formalizations:
- BurdenOfProof = (holder, standard, subject) tuple on each Kripke world
- World fork (appeal) inherits BurdenOfProof from parent world
- Burden reversal = transfer function that swaps holder
- Timely filing = transfer guard that blocks late submissions
- New evidence (二审) = exceptional transfer after world fork

Based on the 2026-06-01 design session insight:
"W2 forks from W1, BurdenOfProof is fully inherited, not reset.
If reset, it would encourage evidence ambush — explicitly prohibited
by PRC Civil Procedure Law Article 65."
"""
from __future__ import annotations
from dataclasses import dataclass, field
from enum import Enum
from typing import Dict, List, Optional, Set, Tuple
from datetime import date


class BurdenHolder(Enum):
    PLAINTIFF = "plaintiff"
    DEFENDANT = "defendant"
    COURT = "court"  # Court-initiated investigation


class EvidenceStandard(Enum):
    PREPONDERANCE = "preponderance"          # 优势证据（民事一般）
    CLEAR_AND_CONVINCING = "clear_convincing" # 明显证据
    BEYOND_REASONABLE_DOUBT = "beyond_doubt"  # 排除合理怀疑（刑事）
    PRIMA_FACIE = "prima_facie"              # 初步证据


class TransferType(Enum):
    NORMAL = "normal"              # 正常举证
    REVERSAL = "reversal"          # 举证责任倒置
    INHERITED = "inherited"        # 世界分叉继承
    BLOCKED = "blocked"            # 逾期阻断
    EXCEPTIONAL = "exceptional"    # 新证据例外


@dataclass(frozen=True)
class BurdenOfProof:
    """The burden of proof state on a Kripke world."""
    holder: BurdenHolder
    standard: EvidenceStandard
    subject: str              # What needs to be proved (legal claim)
    deadline: Optional[date]  # Filing deadline (None = no deadline)
    source_rule: str          # Legal basis (e.g., "民诉法第65条")


@dataclass
class KripkeWorld:
    """A Kripke world with burden-of-proof state."""
    id: str
    parent_id: Optional[str]          # Parent world (None for root)
    burdens: Dict[str, BurdenOfProof]  # claim → BurdenOfProof
    facts: Set[str]                    # Established facts
    stage: str                         # "trial", "appeal", "retrial"
    modal_status: str                  # "◇" (contested) or "□" (res judicata)


@dataclass
class BurdenTransfer:
    """A transfer of burden between worlds."""
    from_world: str
    to_world: str
    claim: str
    transfer_type: TransferType
    old_holder: BurdenHolder
    new_holder: BurdenHolder
    reason: str


class BurdenOfProofTracker:
    """
    Tracks burden of proof across Kripke world transitions.

    Implements:
    1. World forking with full burden inheritance
    2. Burden reversal (举证责任倒置)
    3. Filing deadline enforcement (逾期举证阻断)
    4. New evidence exception (新证据例外)
    """

    def __init__(self):
        self.worlds: Dict[str, KripkeWorld] = {}
        self.transfers: List[BurdenTransfer] = []

    def create_world(self, world_id: str, parent_id: Optional[str],
                     stage: str) -> KripkeWorld:
        """Create a new Kripke world, inheriting burdens from parent."""
        burdens = {}
        facts = set()

        if parent_id and parent_id in self.worlds:
            parent = self.worlds[parent_id]
            # KEY RULE: BurdenOfProof is fully inherited, NOT reset
            # PRC Civil Procedure Law Art. 65
            burdens = dict(parent.burdens)
            facts = set(parent.facts)
            modal_status = "◇"  # Appeal reverts to contested

            # Record inheritance transfers
            for claim, burden in burdens.items():
                self.transfers.append(BurdenTransfer(
                    from_world=parent_id,
                    to_world=world_id,
                    claim=claim,
                    transfer_type=TransferType.INHERITED,
                    old_holder=burden.holder,
                    new_holder=burden.holder,
                    reason="World fork: burden inherited per Art. 65"
                ))
        else:
            modal_status = "◇"

        world = KripkeWorld(
            id=world_id,
            parent_id=parent_id,
            burdens=burdens,
            facts=facts,
            stage=stage,
            modal_status=modal_status,
        )
        self.worlds[world_id] = world
        return world

    def set_burden(self, world_id: str, claim: str,
                   holder: BurdenHolder, standard: EvidenceStandard,
                   deadline: Optional[date] = None,
                   source_rule: str = "") -> None:
        """Set the burden of proof for a claim in a world."""
        self.worlds[world_id].burdens[claim] = BurdenOfProof(
            holder=holder,
            standard=standard,
            subject=claim,
            deadline=deadline,
            source_rule=source_rule,
        )

    def reverse_burden(self, world_id: str, claim: str,
                       new_holder: BurdenHolder, reason: str) -> BurdenTransfer:
        """
        Reverse (倒置) the burden of proof.

        Example: In product liability (产品责任), the burden of proof
        reverses from plaintiff to defendant for defect causation.
        """
        world = self.worlds[world_id]
        old_burden = world.burdens.get(claim)

        old_holder = old_burden.holder if old_burden else BurdenHolder.PLAINTIFF
        world.burdens[claim] = BurdenOfProof(
            holder=new_holder,
            standard=EvidenceStandard.CLEAR_AND_CONVINCING,
            subject=claim,
            deadline=old_burden.deadline if old_burden else None,
            source_rule=reason,
        )

        transfer = BurdenTransfer(
            from_world=world_id,
            to_world=world_id,
            claim=claim,
            transfer_type=TransferType.REVERSAL,
            old_holder=old_holder,
            new_holder=new_holder,
            reason=reason,
        )
        self.transfers.append(transfer)
        return transfer

    def submit_evidence(self, world_id: str, claim: str,
                        evidence: str, filing_date: date) -> Tuple[bool, str]:
        """
        Submit evidence for a claim. Returns (accepted, reason).

        Rules:
        1. If filing_date > deadline and no exception: BLOCKED
        2. If world is appeal and evidence is "new": check Art. 65 exception
        3. Otherwise: accepted
        """
        world = self.worlds[world_id]
        burden = world.burdens.get(claim)

        if burden is None:
            return False, f"No burden found for claim '{claim}'"

        # Check deadline
        if burden.deadline and filing_date > burden.deadline:
            # Check new evidence exception (Art. 65, para 2)
            if world.stage == "appeal" and self._is_new_evidence_exception(
                    world, claim, evidence):
                world.facts.add(evidence)
                self.transfers.append(BurdenTransfer(
                    from_world=world_id,
                    to_world=world_id,
                    claim=claim,
                    transfer_type=TransferType.EXCEPTIONAL,
                    old_holder=burden.holder,
                    new_holder=burden.holder,
                    reason="New evidence exception per Art. 65 para 2"
                ))
                return True, "Accepted: new evidence exception (Art. 65 para 2)"

            # BLOCKED: timely filing requirement
            self.transfers.append(BurdenTransfer(
                from_world=world_id,
                to_world=world_id,
                claim=claim,
                transfer_type=TransferType.BLOCKED,
                old_holder=burden.holder,
                new_holder=burden.holder,
                reason=f"Blocked: filed {filing_date} after deadline {burden.deadline}"
            ))
            return False, f"Blocked: filing after deadline ({burden.deadline})"

        # Normal acceptance
        world.facts.add(evidence)
        return True, "Accepted: timely filing"

    def _is_new_evidence_exception(self, world: KripkeWorld,
                                    claim: str, evidence: str) -> bool:
        """
        Check if evidence qualifies as "new evidence" under Art. 65.

        PRC Civil Procedure Law Art. 65, para 2:
        "Evidence provided due to intentional or gross negligence beyond
        the time limit shall not be adopted by the people's court.
        However, if the evidence is related to basic facts of the case,
        the court shall adopt it, with a reprimand and fine."
        """
        # Simplified: evidence is "new" if it's related to basic facts
        # and wasn't available in the parent world
        parent = self.worlds.get(world.parent_id)
        if parent is None:
            return False
        # Evidence is "new" if it wasn't in parent's fact set
        return evidence not in parent.facts

    def get_burden_summary(self, world_id: str) -> Dict:
        """Get the burden of proof summary for a world."""
        world = self.worlds[world_id]
        return {
            "world_id": world_id,
            "stage": world.stage,
            "modal_status": world.modal_status,
            "burdens": {
                claim: {
                    "holder": burden.holder.value,
                    "standard": burden.standard.value,
                    "deadline": str(burden.deadline) if burden.deadline else "none",
                    "source": burden.source_rule,
                }
                for claim, burden in world.burdens.items()
            },
            "facts": sorted(world.facts),
            "transfer_count": sum(
                1 for t in self.transfers if t.to_world == world_id
            ),
        }


def run_example():
    """Run a complete example: contract breach → appeal with new evidence."""
    print("=" * 72)
    print("BURDEN OF PROOF TRACKER — Contract Breach + Appeal")
    print("=" * 72)

    tracker = BurdenOfProofTracker()

    # W1: Trial (一审)
    w1 = tracker.create_world("W1_trial", parent_id=None, stage="trial")
    tracker.set_burden("W1_trial", "contract_formation",
                       BurdenHolder.PLAINTIFF, EvidenceStandard.PREPONDERANCE,
                       deadline=date(2025, 6, 1),
                       source_rule="民诉法第65条")
    tracker.set_burden("W1_trial", "breach_occurred",
                       BurdenHolder.PLAINTIFF, EvidenceStandard.PREPONDERANCE,
                       deadline=date(2025, 6, 1),
                       source_rule="民诉法第65条")
    tracker.set_burden("W1_trial", "product_defect",
                       BurdenHolder.DEFENDANT, EvidenceStandard.CLEAR_AND_CONVINCING,
                       source_rule="产品质量法第41条")

    # Plaintiff submits evidence on time
    ok, reason = tracker.submit_evidence("W1_trial", "contract_formation",
                                          "signed_contract", date(2025, 5, 15))
    print(f"\nW1: Plaintiff submits contract: {ok} — {reason}")

    # Plaintiff submits evidence late
    ok, reason = tracker.submit_evidence("W1_trial", "breach_occurred",
                                          "late_witness_statement", date(2025, 7, 1))
    print(f"W1: Plaintiff submits late evidence: {ok} — {reason}")

    # Burden reversal for product defect
    tracker.reverse_burden("W1_trial", "product_defect",
                           BurdenHolder.DEFENDANT,
                           "产品质量法第41条：生产者举证")
    print(f"W1: Burden reversed for product_defect → defendant")

    # W2: Appeal (二审) — forks from W1
    w2 = tracker.create_world("W2_appeal", parent_id="W1_trial", stage="appeal")
    print(f"\nW2: Appeal created, burdens inherited from W1")

    # New evidence in appeal (exceptional transfer)
    ok, reason = tracker.submit_evidence("W2_appeal", "breach_occurred",
                                          "new_expert_report", date(2025, 9, 1))
    print(f"W2: New evidence in appeal: {ok} — {reason}")

    # Summary
    for wid in ["W1_trial", "W2_appeal"]:
        summary = tracker.get_burden_summary(wid)
        print(f"\n{'=' * 36}")
        print(f"World: {summary['world_id']} ({summary['stage']})")
        print(f"  Modal status: {summary['modal_status']}")
        print(f"  Transfers: {summary['transfer_count']}")
        for claim, info in summary['burdens'].items():
            print(f"  {claim}: holder={info['holder']}, "
                  f"std={info['standard']}, deadline={info['deadline']}")

    print(f"\n{'=' * 72}")
    print(f"Total transfers: {len(tracker.transfers)}")
    for t in tracker.transfers:
        print(f"  [{t.transfer_type.value:12s}] {t.from_world}→{t.to_world}: "
              f"{t.claim} ({t.old_holder.value}→{t.new_holder.value})")
    print(f"{'=' * 72}")

    return tracker


if __name__ == "__main__":
    run_example()
