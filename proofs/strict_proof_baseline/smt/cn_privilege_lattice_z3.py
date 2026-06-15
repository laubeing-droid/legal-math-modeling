#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
cn_privilege_lattice_z3.py
P0-B': CN Privilege Lattice — Z3 Python proof script

Attempts to prove that no monotonic epsilon function exists over the 10-level
CN legal hierarchy under a conflicting value assignment.  If z3-solver is
installed, the script builds the identical constraint system as the .smt2
draft and reports sat/unsat/unknown.

Epistemic status: PENDING_TOOLCHAIN (Z3 may or may not be installed)
"""

from __future__ import annotations

import sys

# ---------------------------------------------------------------------------
# 0. Tool-chain probe
# ---------------------------------------------------------------------------
Z3_AVAILABLE = False
Z3_VERSION: str | None = None
z3 = None  # type: ignore

try:
    import z3

    Z3_AVAILABLE = True
    Z3_VERSION = z3.get_version_string() if hasattr(z3, "get_version_string") else "unknown"
except Exception as exc:
    Z3_AVAILABLE = False
    Z3_VERSION = None
    print(f"[WARN] z3-solver not available: {exc}", file=sys.stderr)


# ---------------------------------------------------------------------------
# 1. Data model — 10 CN legal levels
# ---------------------------------------------------------------------------
LEVELS = [
    ("L0", "宪法", "Constitution"),
    ("L1", "法律", "Law"),
    ("L2", "行政法规", "Administrative Regulation"),
    ("L3", "地方性法规", "Local Regulation"),
    ("L4", "部门规章", "Department Rule"),
    ("L5", "地方政府规章", "Local Government Rule"),
    ("L6", "司法解释", "Judicial Interpretation"),
    ("L7", "自治条例", "Autonomy Regulation"),
    ("L8", "经济特区法规", "SEZ Regulation"),
    ("L9", "军事法规", "Military Regulation"),
]

# Partial-order edges: (dominator, dominated) meaning eps[dom] >= eps[sub]
PARTIAL_ORDER = [
    (0, 1),   # Constitution > Law
    (1, 2),   # Law > Administrative Regulation
    (2, 4),   # Administrative Regulation > Department Rule
    (2, 3),   # Administrative Regulation > Local Regulation
    (3, 5),   # Local Regulation > Local Government Rule
    (1, 6),   # Law > Judicial Interpretation
    (2, 6),   # Administrative Regulation > Judicial Interpretation
    (1, 7),   # Law > Autonomy Regulation
    (1, 8),   # Law > SEZ Regulation
    (1, 9),   # Law > Military Regulation
]

# The conflicting constraint: eps[6] > eps[2]  (Judicial > Administrative)
CONFLICTING_CONSTRAINTS = [
    (6, 2),   # eps6 > eps2  contradicts  eps2 >= eps6
]


# ---------------------------------------------------------------------------
# 2. Build and solve the SMT problem
# ---------------------------------------------------------------------------
def build_and_solve() -> dict:
    """Construct the Z3 solver and return a result dictionary."""
    result = {
        "z3_available": Z3_AVAILABLE,
        "z3_version": Z3_VERSION,
        "status": "UNKNOWN",
        "model": None,
        "error": None,
    }

    if not Z3_AVAILABLE:
        result["status"] = "UNKNOWN"
        result["error"] = "z3-solver is not installed in this environment"
        return result

    try:
        solver = z3.Solver()

        # Real variables for epsilon values
        eps = [z3.Real(f"eps{i}") for i in range(len(LEVELS))]

        # Monotonicity constraints from partial order
        for dom, sub in PARTIAL_ORDER:
            solver.add(eps[dom] >= eps[sub])

        # Conflicting value assignment
        for high, low in CONFLICTING_CONSTRAINTS:
            solver.add(eps[high] > eps[low])

        # Sanity bounds [0, 1]
        for e in eps:
            solver.add(e >= 0.0, e <= 1.0)

        # Check
        smt_result = solver.check()
        result["status"] = str(smt_result)

        if smt_result == z3.sat:
            m = solver.model()
            result["model"] = {
                LEVELS[i][0]: float(m[eps[i]].as_fraction())
                for i in range(len(LEVELS))
                if m[eps[i]] is not None
            }
        elif smt_result == z3.unsat:
            result["model"] = None
        else:
            result["model"] = None

    except Exception as exc:
        result["status"] = "ERROR"
        result["error"] = str(exc)

    return result


# ---------------------------------------------------------------------------
# 3. Main entry point
# ---------------------------------------------------------------------------
def main() -> int:
    print("=" * 70)
    print("CN Privilege Lattice — Z3 Monotonic-Epsilon Proof (P0-B')")
    print("=" * 70)

    result = build_and_solve()

    print(f"\nZ3 available : {result['z3_available']}")
    print(f"Z3 version   : {result['z3_version']}")
    print(f"SMT result   : {result['status']}")

    if result["error"]:
        print(f"Error detail : {result['error']}")

    if result["model"]:
        print("\nCounter-example model (sat means monotonic epsilon EXISTS):")
        for key, val in result["model"].items():
            print(f"  {key} = {val:.4f}")
    elif result["status"] == "unsat":
        print("\nConclusion: UNSAT — no monotonic epsilon satisfies all constraints.")
        print("This confirms the draft proof in cn_privilege_lattice.smt2.")

    print("\n" + "=" * 70)
    print("__epistemic_status__")
    print("=" * 70)
    import pprint

    pprint.pprint(__epistemic_status__, width=70)

    return 0 if result["status"] in ("unsat", "sat") else 1


# ---------------------------------------------------------------------------
# 4. Epistemic status metadata
# ---------------------------------------------------------------------------
__epistemic_status__ = {
    "status": "PENDING_TOOLCHAIN",
    "artifact": "proof/smt/cn_privilege_lattice_z3.py",
    "checker_command": "python cn_privilege_lattice_z3.py",
    "assumptions": [
        "Z3 可用 (z3-solver 已安装)",
        "有限域假设 (Real 变量限制在 [0,1])",
        "偏序关系符合中国立法法层级",
    ],
    "limitations": [
        "工具链不可用，脚本为 draft",
        "若 Z3 未安装则返回 UNKNOWN",
        "矛盾约束为构造性示例，非唯一证明路径",
    ],
}

if __name__ == "__main__":
    sys.exit(main())
