; EXPECT: unsat
;; Logic not supported in Alethe
; DISABLE-TESTER: alethe
(set-logic QF_NRAT)
(declare-fun x () Real)
(assert (>= x 0))
(assert (< (sqrt x) 0))
(check-sat)
