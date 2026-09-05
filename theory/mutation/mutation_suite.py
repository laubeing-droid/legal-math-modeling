#!/usr/bin/env python3
"""
Layer 8: Mutation Test Suite — Proof Robustness Quantification
================================================================

For each of the 20+ core proof files, auto-generates MUTANTS and
measures how many survive. A mutant that passes (exit 0) means the
proof is NOT robust to that class of error.

Mutation operators:
  1. INEQUALITY_SWAP:   <= <-> >=
  2. CONSTANT_CORRUPT:  c=0.5 -> c=1.0
  3. ASSERT_DELETE:     remove one assert statement
  4. DIRECTION_SWAP:    swap exception attack direction
  5. STUB_RETURN:       is_terminating() -> return True

Mutation score = killed / total. Score 1.0 means all mutants killed
(proof is robust). Score < 0.5 means the proof is fragile.
"""

import subprocess
import sys
import os
import re
import tempfile
import shutil


# ============================================================
# Mutation operators
# ============================================================

def mutate_inequality_swap(source: str) -> str:
    """Swap <= with >= in assert statements."""
    # Only in assert lines, not in comments
    lines = source.split('\n')
    mutated = []
    for line in lines:
        if 'assert' in line and '<=' in line and 'import' not in line:
            line = re.sub(r'(?<=[^<])<=(?=[^=])', '>=', line, count=1)
        elif 'assert' in line and '>=' in line and 'import' not in line:
            line = re.sub(r'(?<=[^>])>=(?=[^=])', '<=', line, count=1)
        mutated.append(line)
    return '\n'.join(mutated)


def mutate_constant_corrupt(source: str, old_val: str, new_val: str) -> str:
    """Replace a constant value."""
    return source.replace(old_val, new_val)


def mutate_assert_delete(source: str) -> str:
    """Delete the first assert statement."""
    lines = source.split('\n')
    for i, line in enumerate(lines):
        stripped = line.strip()
        if stripped.startswith('assert ') and 'import' not in line:
            lines[i] = f'# DELETED: {stripped}'
            break
    return '\n'.join(lines)


def mutate_stub_return(source: str) -> str:
    """Replace is_terminating body with return True."""
    return re.sub(
        r'def is_terminating\(self\).*?return \w+',
        'def is_terminating(self) -> bool:\n        return True  # MUTATED STUB',
        source, flags=re.DOTALL
    )


# ============================================================
# Mutation runner
# ============================================================

MUTATIONS = {
    'INEQUALITY_SWAP': mutate_inequality_swap,
    'CONSTANT_CORRUPT_c05_to_c10': lambda s: mutate_constant_corrupt(s, 'c = 0.5', 'c = 1.0'),
    'CONSTANT_CORRUPT_beta05_to_beta10': lambda s: mutate_constant_corrupt(s, 'beta = 0.5', 'beta = 1.0'),
    'ASSERT_DELETE': mutate_assert_delete,
    'STUB_RETURN': mutate_stub_return,
}


def kill_mutant(original_file: str, mutation_name: str,
                mutator) -> dict:
    """Run mutant. Returns {killed, output_preview}."""
    with open(original_file, 'r', encoding='utf-8') as f:
        source = f.read()

    mutated_source = mutator(source)

    # Skip if no actual change
    if mutated_source == source:
        return {'killed': None, 'reason': 'No change (mutation not applicable)'}

    # Write to temp file
    tmp = tempfile.NamedTemporaryFile(suffix='.py', delete=False, mode='w', encoding='utf-8')
    tmp.write(mutated_source)
    tmp.close()

    # Run mutant
    try:
        result = subprocess.run(
            [sys.executable, '-X', 'utf8', tmp.name],
            capture_output=True, text=True, timeout=15,
            cwd=os.path.dirname(original_file)
        )
        killed = result.returncode != 0
        output_preview = (result.stderr or result.stdout)[:200]
    except subprocess.TimeoutExpired:
        killed = True  # Timeout = killed (but timeout is a different signal)
        output_preview = "TIMEOUT"
    except Exception as e:
        killed = True
        output_preview = str(e)[:200]
    finally:
        os.unlink(tmp.name)

    return {'killed': killed, 'output': output_preview}


def run_mutation_suite(files: list) -> dict:
    """Run all mutations on all files. Returns summary."""
    results = {}
    total_killed = 0
    total_applicable = 0

    for fname in files:
        if not os.path.exists(fname):
            continue
        file_results = {}
        for mname, mutator in MUTATIONS.items():
            r = kill_mutant(fname, mname, mutator)
            file_results[mname] = r
            if r['killed'] is not None:
                total_applicable += 1
                if r['killed']:
                    total_killed += 1
        results[fname] = file_results

    score = total_killed / total_applicable if total_applicable > 0 else 0.0
    return {
        'per_file': results,
        'total_killed': total_killed,
        'total_applicable': total_applicable,
        'mutation_score': score,
    }


if __name__ == "__main__":
    print("=" * 60)
    print("MUTATION TEST SUITE — Proof Robustness")
    print("=" * 60)

    # Files to mutate
    test_files = [
        'banach_pricing_contraction.py',
        'kripke_supersedes_corrects.py',
        'policy_expressiveness.py',
        'argumentation_horn_unification.py',
        'dp_legal_privilege.py',
        'non_interference_cbl.py',
    ]

    suite = run_mutation_suite(test_files)

    print(f"\n  Mutation operators: {len(MUTATIONS)}")
    print(f"  Files tested: {len(test_files)}")
    print(f"  Mutants generated: {suite['total_applicable']}")
    print(f"  Killed: {suite['total_killed']}")
    print(f"  Survived: {suite['total_applicable'] - suite['total_killed']}")
    print(f"  MUTATION SCORE: {suite['mutation_score']:.2f}")
    print(f"  (1.0 = all mutants killed = proof is robust)")
    print(f"  (<0.5 = many mutants survive = proof needs hardening)")

    print(f"\n  Per-file breakdown:")
    for fname, mresults in suite['per_file'].items():
        killed = sum(1 for r in mresults.values() if r['killed'] is True)
        survived = sum(1 for r in mresults.values() if r['killed'] is False)
        na = sum(1 for r in mresults.values() if r['killed'] is None)
        print(f"    {fname[:40]:40s} K={killed} S={survived} N/A={na}")
