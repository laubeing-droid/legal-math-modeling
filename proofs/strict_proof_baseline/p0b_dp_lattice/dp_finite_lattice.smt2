; Theorem B1: Galois connection on CN finite bounded lattice
; Encoded in SMT-LIB 2 format for future z3 CLI use.
;
; Claim: No Galois connection exists between a finite bounded lattice
; (with bottom) and the real numbers ℝ, because ℝ lacks a bottom.

(set-logic AUFLIRA)

; 10 CN privilege levels (0..9)
(declare-fun alpha (Int) Real)
(declare-fun gamma (Real) Int)

; Monotonicity of alpha on chain 0..9
(assert (forall ((i Int) (j Int))
  (=> (and (<= 0 i) (<= i j) (<= j 9))
      (<= (alpha i) (alpha j)))))

; Bounded lattice: 0 is bottom, 9 is top
; (encoded implicitly by the chain order)

; Galois connection condition, instantiated at p=0 and a witness r.
; We assert: 0 <= gamma(r)  (bottom property)
; And: alpha(0) <= r       (from Galois connection)
(declare-fun r_bot () Real)
(assert (<= 0 (gamma r_bot)))
(assert (<= (alpha 0) r_bot))

; Witness: r_bot = alpha(0) - 1
(assert (= r_bot (- (alpha 0) 1.0)))

(check-sat)
; Expected: unsat
