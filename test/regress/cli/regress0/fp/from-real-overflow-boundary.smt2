; REQUIRES: unrestricted-mode
; EXPECT: unsat
; The exact overflow threshold of Float32 under RNE is the midpoint between
; the largest finite value and 2^128, i.e. 2^128 - 2^103 = 340282356779733661
; 637539395458142568448. The tie rounds to +oo, so the reals converting to
; +oo are exactly those at or above the threshold. Both disjuncts contradict
; that: x is strictly below the threshold and y is at it.
(set-logic ALL)
(declare-const x Real)
(declare-const y Real)
(assert (or (and (> x 340282356779733661637539395458142568447.0)
                 (< x 340282356779733661637539395458142568448.0)
                 (fp.isInfinite ((_ to_fp 8 24) RNE x)))
            (and (>= y 340282356779733661637539395458142568448.0)
                 (not (fp.isInfinite ((_ to_fp 8 24) RNE y))))))
(check-sat)
