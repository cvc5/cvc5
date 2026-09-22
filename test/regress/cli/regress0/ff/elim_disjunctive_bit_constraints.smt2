; REQUIRES: cocoa
; EXPECT: sat
; ffElimDisjunctiveBit should only fire when both branches of an OR constrain
; the same variable. Here (= x 0) and (= y 1) involve different variables,
; so the OR must not be rewritten to x*x=x (which would discard the y=1 branch).
(set-logic QF_FF)
(declare-const x (_ FiniteField 3))
(declare-const y (_ FiniteField 3))
(assert (or (= x #f0m3) (= y #f1m3)))
(assert (= (ff.add x x) #f1m3))
(check-sat)
