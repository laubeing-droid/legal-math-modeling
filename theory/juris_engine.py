#!/usr/bin/env python3
"""
Juris Engine: Unified Legal Reasoning CLI
==========================================

CLI interface for the unified Horn→AAF→Banach inference pipeline.

Usage:
    python -m juris_engine --input case.json --output result.json
    python -m juris_engine --facts "合同成立" "未付款" --jurisdiction CN --domain contract

Input JSON format:
{
  "facts": ["合同成立", "未付款"],
  "rules": [
    {"id": "R1", "premises": ["合同成立", "未付款"], "head": "违约成立", "exceptions": []}
  ],
  "jurisdiction": "CN",
  "domain": "contract"
}

Output JSON format:
{
  "conclusion": "违约成立",
  "confidence": 0.82,
  "trust_label": "PROVED_BY_ARTIFACT",
  "explanation": "...",
  "horn_closure": ["合同成立", "未付款", "违约成立"],
  "grounded_extension": ["R1"],
  "defeated_rules": [],
  "deviation_score": 0.15
}
"""

import json
import sys
import argparse
from pathlib import Path

# Add project root to path
_PROJECT_ROOT = Path(__file__).resolve().parent
if str(_PROJECT_ROOT) not in sys.path:
    sys.path.insert(0, str(_PROJECT_ROOT))


def infer(facts: list, rules: list, jurisdiction: str = "CN",
          domain: str = "contract") -> dict:
    """Run the unified inference pipeline.

    Args:
        facts: List of fact strings
        rules: List of rule dicts with id, premises, head, exceptions
        jurisdiction: CN / US / HK
        domain: Legal domain

    Returns:
        Inference result dict
    """
    from theory.argumentation_horn_unification import HornToDungBridge, HornRule

    # Build Horn rules
    horn_rules = []
    for r in rules:
        horn_rules.append(HornRule(
            id=r["id"],
            premises=r.get("premises", []),
            head=r["head"],
            exceptions=r.get("exceptions", []),
        ))

    # Run inference
    bridge = HornToDungBridge(horn_rules, set(facts))
    frame = bridge.construct_deductive_frame()
    ge = frame.grounded_extension()

    # Extract results
    closure = bridge.facts  # defeat-aware closure
    accepted_ids = {arg.rule_id for arg in ge}
    all_rule_ids = {r.id for r in horn_rules}
    defeated_ids = all_rule_ids - accepted_ids

    # Compute trust label
    trust_label = "PROVED_BY_ARTIFACT" if len(defeated_ids) == 0 else "PARTIAL"

    # Compute confidence (simple heuristic)
    total_rules = len(horn_rules)
    accepted_count = len(accepted_ids)
    confidence = accepted_count / max(total_rules, 1)

    # Generate explanation
    accepted_rules = [r for r in horn_rules if r.id in accepted_ids]
    explanation_parts = []
    for r in accepted_rules:
        if r.premises:
            explanation_parts.append(
                f"规则 {r.id}：前提 {r.premises} 均满足 → 推导 {r.head}")
        else:
            explanation_parts.append(
                f"规则 {r.id}：公理（无前提）→ 推导 {r.head}")

    return {
        "conclusion": sorted(closure - set(facts)),
        "confidence": round(confidence, 3),
        "trust_label": trust_label,
        "explanation": "; ".join(explanation_parts) if explanation_parts else "无推导",
        "horn_closure": sorted(closure),
        "grounded_extension": sorted(accepted_ids),
        "defeated_rules": sorted(defeated_ids),
        "jurisdiction": jurisdiction,
        "domain": domain,
    }


def main():
    parser = argparse.ArgumentParser(
        description="Juris Engine: Unified Legal Reasoning CLI")
    parser.add_argument("--input", "-i", type=str,
                        help="Input JSON file")
    parser.add_argument("--output", "-o", type=str,
                        help="Output JSON file (default: stdout)")
    parser.add_argument("--facts", nargs="+",
                        help="Facts (alternative to --input)")
    parser.add_argument("--jurisdiction", default="CN",
                        help="Jurisdiction: CN/US/HK (default: CN)")
    parser.add_argument("--domain", default="contract",
                        help="Legal domain (default: contract)")

    args = parser.parse_args()

    if args.input:
        with open(args.input, encoding="utf-8") as f:
            case = json.load(f)
        facts = case.get("facts", [])
        rules = case.get("rules", [])
        jurisdiction = case.get("jurisdiction", args.jurisdiction)
        domain = case.get("domain", args.domain)
    elif args.facts:
        facts = args.facts
        rules = []
        jurisdiction = args.jurisdiction
        domain = args.domain
    else:
        parser.print_help()
        sys.exit(1)

    result = infer(facts, rules, jurisdiction, domain)

    output_json = json.dumps(result, ensure_ascii=False, indent=2)
    if args.output:
        with open(args.output, "w", encoding="utf-8") as f:
            f.write(output_json)
        print(f"Result written to {args.output}")
    else:
        print(output_json)


if __name__ == "__main__":
    main()
