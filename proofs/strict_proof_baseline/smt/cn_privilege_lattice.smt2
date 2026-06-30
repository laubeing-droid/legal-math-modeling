; cn_privilege_lattice.smt2
; P0-B': CN Privilege Lattice — No Monotonic Epsilon Function Exists
; 
; This SMT-LIB 2 draft proves that no monotonic epsilon function can satisfy
; a specific set of privilege-value constraints over the 10-level CN legal
; hierarchy.  The proof is by contradiction: assume epsilon exists and is
; monotonic w.r.t. the statutory partial order, then add an explicit
; conflicting value assignment; Z3 should return UNSAT.
;
; Epistemic status: TOOLCHAIN_PENDING (Z3 not available in this environment)

(set-logic QF_LRA)
(set-option :produce-models true)

; ---------------------------------------------------------------------------
; 1. 10 CN legal levels (declared as integer constants for readability)
; ---------------------------------------------------------------------------
(declare-const L0 Int)   ; 宪法         (Constitution)
(declare-const L1 Int)   ; 法律         (Law)
(declare-const L2 Int)   ; 行政法规     (Administrative Regulation)
(declare-const L3 Int)   ; 地方性法规   (Local Regulation)
(declare-const L4 Int)   ; 部门规章     (Department Rule)
(declare-const L5 Int)   ; 地方政府规章 (Local Government Rule)
(declare-const L6 Int)   ; 司法解释     (Judicial Interpretation)
(declare-const L7 Int)   ; 自治条例     (Autonomy Regulation)
(declare-const L8 Int)   ; 经济特区法规 (SEZ Regulation)
(declare-const L9 Int)   ; 军事法规     (Military Regulation)

(assert (= L0 0))
(assert (= L1 1))
(assert (= L2 2))
(assert (= L3 3))
(assert (= L4 4))
(assert (= L5 5))
(assert (= L6 6))
(assert (= L7 7))
(assert (= L8 8))
(assert (= L9 9))

; ---------------------------------------------------------------------------
; 2. Epsilon values — one real variable per level
; ---------------------------------------------------------------------------
(declare-const eps0 Real)
(declare-const eps1 Real)
(declare-const eps2 Real)
(declare-const eps3 Real)
(declare-const eps4 Real)
(declare-const eps5 Real)
(declare-const eps6 Real)
(declare-const eps7 Real)
(declare-const eps8 Real)
(declare-const eps9 Real)

; ---------------------------------------------------------------------------
; 3. Partial order (higher privilege = higher statutory force)
;    Monotonicity: if A dominates B in the hierarchy, then eps(A) >= eps(B)
; ---------------------------------------------------------------------------

; Constitution > Law > Administrative Regulation > Department Rule
(assert (>= eps0 eps1))
(assert (>= eps1 eps2))
(assert (>= eps2 eps4))

; Constitution > Law > Administrative Regulation > Local Regulation > Local Gov Rule
(assert (>= eps0 eps1))
(assert (>= eps1 eps2))
(assert (>= eps2 eps3))
(assert (>= eps3 eps5))

; Constitution > Law > Judicial Interpretation
(assert (>= eps0 eps1))
(assert (>= eps1 eps6))

; Administrative Regulation > Judicial Interpretation (dominant doctrinal view)
(assert (>= eps2 eps6))

; Law > Autonomy Regulation / SEZ Regulation / Military Regulation
(assert (>= eps1 eps7))
(assert (>= eps1 eps8))
(assert (>= eps1 eps9))

; ---------------------------------------------------------------------------
; 4. Conflicting value assignment (the "impossible" epsilon)
;    A proposed privilege metric that places Judicial Interpretation
;    strictly above Administrative Regulation contradicts the monotonicity
;    constraint eps2 >= eps6 derived from the statutory partial order.
; ---------------------------------------------------------------------------
(assert (> eps6 eps2))   ; Judicial Interpretation claimed higher than Admin Regulation

; ---------------------------------------------------------------------------
; 5. Sanity bounds (optional, keeps the search space finite for QF_LRA)
; ---------------------------------------------------------------------------
(assert (and (>= eps0 0.0) (<= eps0 1.0)))
(assert (and (>= eps1 0.0) (<= eps1 1.0)))
(assert (and (>= eps2 0.0) (<= eps2 1.0)))
(assert (and (>= eps3 0.0) (<= eps3 1.0)))
(assert (and (>= eps4 0.0) (<= eps4 1.0)))
(assert (and (>= eps5 0.0) (<= eps5 1.0)))
(assert (and (>= eps6 0.0) (<= eps6 1.0)))
(assert (and (>= eps7 0.0) (<= eps7 1.0)))
(assert (and (>= eps8 0.0) (<= eps8 1.0)))
(assert (and (>= eps9 0.0) (<= eps9 1.0)))

; ---------------------------------------------------------------------------
; 6. Check — expected result: UNSAT (no monotonic epsilon can satisfy all
;    the above constraints simultaneously)
; ---------------------------------------------------------------------------
(check-sat)
(get-model)

; ---------------------------------------------------------------------------
; Epistemic metadata (appended as comments for human readers)
; ---------------------------------------------------------------------------
; __epistemic_status__ = {
;     "status": "TOOLCHAIN_PENDING",
;     "artifact": "proof/smt/cn_privilege_lattice.smt2",
;     "checker_command": "z3 cn_privilege_lattice.smt2",
;     "assumptions": ["Z3 可用", "有限域假设 (QF_LRA)", "偏序关系符合中国立法法层级"],
;     "limitations": ["工具链不可用，文件为 draft", "矛盾约束为构造性示例，非唯一证明路径"]
; }
