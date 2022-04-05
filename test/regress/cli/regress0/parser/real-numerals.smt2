(set-logic QF_NRA)
(set-info :status sat)
; note according to SMT-LIB, a NUMERAL specifies a Real when the logic contains reals but not ints
(define-fun x () Real 0)
(assert (<= (- 1) x 3))
(check-sat)
