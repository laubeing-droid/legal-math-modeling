;; graph_similarity_range.smt2
;; Prove: score = 0.6*jaccard + 0.4*size_ratio ∈ [0,1]
;;        where size_ratio = 0.5*vertex_ratio + 0.5*edge_ratio
;;
;; STATUS: Ready for any SMT-LIB2 compliant solver (Z3, CVC5, etc.)
;;
;; Verification command:
;;   z3 graph_similarity_range.smt2
;;   cvc5 --lang smt2 graph_similarity_range.smt2

(set-logic QF_NRA)

;; Declare variables
(declare-fun jaccard () Real)
(declare-fun vertex_ratio () Real)
(declare-fun edge_ratio () Real)
(declare-fun score () Real)

;; Define score formula
;; score = 0.6*jaccard + 0.4*(0.5*vertex_ratio + 0.5*edge_ratio)
;;       = (6/10)*jaccard + (2/10)*vertex_ratio + (2/10)*edge_ratio
(assert (= score
    (+ (* (/ 6.0 10.0) jaccard)
       (* (/ 2.0 10.0) vertex_ratio)
       (* (/ 2.0 10.0) edge_ratio))))

;; Input bounds: all ratios in [0,1]
(assert (>= jaccard 0.0))
(assert (<= jaccard 1.0))
(assert (>= vertex_ratio 0.0))
(assert (<= vertex_ratio 1.0))
(assert (>= edge_ratio 0.0))
(assert (<= edge_ratio 1.0))

;; ==========================================
;; GOAL: Prove score ∈ [0, 1]
;; Strategy: Show both (score < 0) and (score > 1) are UNSAT
;; ==========================================

;; --- Push scope for first check: score < 0 ---
(push)
(assert (< score 0.0))
(check-sat)
;; Expected: unsat  (score cannot be negative)
(pop)

;; --- Push scope for second check: score > 1 ---
(push)
(assert (> score 1.0))
(check-sat)
;; Expected: unsat  (score cannot exceed 1)
(pop)

;; ==========================================
;; Full proof of score ∈ [0,1]
;; ==========================================
(push)
(assert (not (and (>= score 0.0) (<= score 1.0))))
(check-sat)
;; Expected: unsat  (score is always in [0,1])
(pop)

;; If all (check-sat) return unsat, then score ∈ [0,1] is PROVEN.
;; If any returns sat, a counterexample exists.

;; ==========================================
;; Alternative: Verify boundary cases
;; ==========================================

;; Case: all inputs = 0 -> score should be 0
(push)
(assert (= jaccard 0.0))
(assert (= vertex_ratio 0.0))
(assert (= edge_ratio 0.0))
(assert (not (= score 0.0)))
(check-sat)
;; Expected: unsat
(pop)

;; Case: all inputs = 1 -> score should be 1
(push)
(assert (= jaccard 1.0))
(assert (= vertex_ratio 1.0))
(assert (= edge_ratio 1.0))
(assert (not (= score 1.0)))
(check-sat)
;; Expected: unsat
(pop)

;; Case: only jaccard = 1, others = 0 -> score = 0.6
(push)
(assert (= jaccard 1.0))
(assert (= vertex_ratio 0.0))
(assert (= edge_ratio 0.0))
(assert (not (= score (/ 6.0 10.0))))
(check-sat)
;; Expected: unsat
(pop)

;; Case: only vertex_ratio = 1, others = 0 -> score = 0.2
(push)
(assert (= jaccard 0.0))
(assert (= vertex_ratio 1.0))
(assert (= edge_ratio 0.0))
(assert (not (= score (/ 2.0 10.0))))
(check-sat)
;; Expected: unsat
(pop)

;; Case: only edge_ratio = 1, others = 0 -> score = 0.2
(push)
(assert (= jaccard 0.0))
(assert (= vertex_ratio 0.0))
(assert (= edge_ratio 1.0))
(assert (not (= score (/ 2.0 10.0))))
(check-sat)
;; Expected: unsat
(pop)

(exit)
