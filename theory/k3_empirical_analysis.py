#!/usr/bin/env python3
"""
k≤3 Boundary Empirical Analysis (A11)

Parses the 2,117 PRC Horn rules from YAML and computes:
1. Exception chain length distribution (k values)
2. Premise atom count distribution
3. Dependency depth estimation
4. HORN vs NON_HORN distribution by namespace
5. Formalizability metric (symbolic vs NL premises)
6. Rules exceeding k=3 boundary

Source: configs/zh_CN/rules.yaml (juris-calculus)
"""
from __future__ import annotations
import json
import sys
from collections import Counter, defaultdict
from pathlib import Path

# YAML source path
YAML_PATHS = [
    Path(r"D:\同步网盘\软件开发\论文\实验数据\4.20260608claude数学模型迭代源码（见theroy和md）\juris-calculus\configs\zh_CN\rules.yaml"),
    Path("configs/zh_CN/rules.yaml"),  # fallback
]

def find_yaml():
    for p in YAML_PATHS:
        if p.exists():
            return p
    return None


def load_rules(yaml_path: Path):
    """Load rules from YAML, return list of dicts."""
    import yaml
    with open(yaml_path, "r", encoding="utf-8") as f:
        data = yaml.safe_load(f)
    if not data or not isinstance(data, dict):
        return []
    return data.get("rules", [])


import unicodedata


def is_symbolic_atom(atom: str) -> bool:
    """Check if an atom name is purely symbolic (no CJK characters)."""
    for ch in atom:
        if unicodedata.category(ch).startswith("Lo") and ord(ch) >= 0x2E80:
            return False
    return True


def analyze_rules(rules: list) -> dict:
    """Run full analysis on rule set."""
    total = len(rules)
    ns_counter = Counter()
    head_type_counter = Counter()
    exception_len_counter = Counter()
    premise_count_counter = Counter()
    mechanical_count = 0
    symbolic_premise_count = 0
    total_premises = 0
    exception_chains = []
    k_exceeding = []

    for rule in rules:
        rid = rule.get("id", "?")
        ns = rule.get("namespace", "unknown")
        head_type = rule.get("head_type", "HORN")
        exceptions = rule.get("exception_chain", []) or []
        premises = rule.get("premise_atoms", []) or []
        mech = rule.get("mechanical_exception", False)

        ns_counter[ns] += 1
        head_type_counter[head_type] += 1
        exception_len_counter[len(exceptions)] += 1
        premise_count_counter[len(premises)] += 1

        if mech:
            mechanical_count += 1

        for p in premises:
            total_premises += 1
            if is_symbolic_atom(p):
                symbolic_premise_count += 1

        # k = exception chain length as proxy for dependency depth
        k = len(exceptions)
        exception_chains.append({"id": rid, "k": k, "ns": ns, "head_type": head_type})
        if k > 3:
            k_exceeding.append({"id": rid, "k": k, "ns": ns, "exceptions": exceptions})

    # Compute summary
    horn_count = head_type_counter.get("HORN", 0)
    non_horn_count = head_type_counter.get("NON_HORN", 0)

    k_gt_3 = sum(1 for r in exception_chains if r["k"] > 3)
    k_gt_4 = sum(1 for r in exception_chains if r["k"] > 4)
    k_gt_5 = sum(1 for r in exception_chains if r["k"] > 5)

    formalizability = symbolic_premise_count / total_premises if total_premises > 0 else 0

    return {
        "total_rules": total,
        "namespaces": dict(ns_counter.most_common()),
        "head_types": dict(head_type_counter),
        "exception_length_distribution": dict(sorted(exception_len_counter.items())),
        "premise_count_distribution": dict(sorted(premise_count_counter.items())),
        "mechanical_exceptions": mechanical_count,
        "total_premises": total_premises,
        "symbolic_premises": symbolic_premise_count,
        "formalizability_ratio": round(formalizability, 4),
        "k_gt_3_count": k_gt_3,
        "k_gt_3_pct": round(k_gt_3 / total * 100, 2) if total > 0 else 0.0,
        "k_gt_4_count": k_gt_4,
        "k_gt_4_pct": round(k_gt_4 / total * 100, 2) if total > 0 else 0.0,
        "k_gt_5_count": k_gt_5,
        "k_gt_5_pct": round(k_gt_5 / total * 100, 2) if total > 0 else 0.0,
        "k_exceeding_3_rules": k_exceeding[:20],  # first 20 for inspection
    }


def print_report(result: dict):
    """Print human-readable report."""
    print("=" * 72)
    print("k≤3 BOUNDARY EMPIRICAL ANALYSIS")
    print("Source: juris-calculus configs/zh_CN/rules.yaml")
    print("=" * 72)

    total = result['total_rules']
    if total == 0:
        print("\nNo rules found. Nothing to analyze.")
        return

    print(f"\n1. TOTAL RULES: {total}")
    print(f"   HORN: {result['head_types'].get('HORN', 0)}")
    print(f"   NON_HORN: {result['head_types'].get('NON_HORN', 0)}")

    print(f"\n2. NAMESPACE DISTRIBUTION:")
    for ns, count in result["namespaces"].items():
        pct = count / total * 100
        print(f"   {ns:15s}: {count:4d} ({pct:5.1f}%)")

    print(f"\n3. EXCEPTION CHAIN LENGTH DISTRIBUTION (k values):")
    for k, count in result["exception_length_distribution"].items():
        pct = count / total * 100
        bar = "█" * int(pct / 2)
        marker = " ← EXCEEDS k≤3" if k > 3 else ""
        print(f"   k={k}: {count:4d} ({pct:5.1f}%) {bar}{marker}")

    print(f"\n4. k≤3 BOUNDARY ANALYSIS:")
    print(f"   Rules with k > 3: {result['k_gt_3_count']} ({result['k_gt_3_pct']}%)")
    print(f"   Rules with k > 4: {result['k_gt_4_count']} ({result['k_gt_4_pct']}%)")
    print(f"   Rules with k > 5: {result['k_gt_5_count']} ({result['k_gt_5_pct']}%)")

    within = total - result["k_gt_3_count"]
    print(f"   WITHIN k≤3: {within} ({round(within/total*100, 2)}%)")

    print(f"\n5. FORMALIZABILITY:")
    print(f"   Total premise atoms: {result['total_premises']}")
    print(f"   Symbolic atoms: {result['symbolic_premises']}")
    print(f"   Formalizability ratio: {result['formalizability_ratio']:.2%}")

    print(f"\n6. MECHANICAL EXCEPTIONS: {result['mechanical_exceptions']}")

    if result["k_exceeding_3_rules"]:
        print(f"\n7. SAMPLE RULES EXCEEDING k≤3 (first 20):")
        for r in result["k_exceeding_3_rules"]:
            print(f"   {r['id']:12s} k={r['k']} ns={r['ns']}")

    print(f"\n{'=' * 72}")
    print("CONCLUSION:")
    if result["k_gt_3_pct"] < 5:
        print(f"  k≤3 boundary covers {100 - result['k_gt_3_pct']}% of rules.")
        print(f"  The boundary is EMPIRICALLY VALIDATED for this rule set.")
    elif result["k_gt_3_pct"] < 20:
        print(f"  k≤3 boundary covers {100 - result['k_gt_3_pct']}% of rules.")
        print(f"  The boundary is MOSTLY VALID but {result['k_gt_3_count']} rules need TAINTED flag.")
    else:
        print(f"  k≤3 boundary covers only {100 - result['k_gt_3_pct']}% of rules.")
        print(f"  Consider raising the boundary or redesigning rule encoding.")
    print("=" * 72)


def main():
    yaml_path = find_yaml()
    if yaml_path is None:
        print("ERROR: rules.yaml not found. Provide path as argument.")
        sys.exit(1)

    print(f"Loading rules from: {yaml_path}")
    rules = load_rules(yaml_path)
    print(f"Loaded {len(rules)} rules.")

    result = analyze_rules(rules)
    print_report(result)

    # Save JSON
    out_path = Path("docs/analysis/k3_analysis_result.json")
    out_path.parent.mkdir(parents=True, exist_ok=True)
    with open(out_path, "w", encoding="utf-8") as f:
        json.dump(result, f, indent=2, ensure_ascii=False)
    print(f"\nJSON saved to: {out_path}")


if __name__ == "__main__":
    main()
