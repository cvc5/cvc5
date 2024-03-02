; EXPECT: unsat
;; Logic not supported in Alethe
; DISABLE-TESTER: alethe
(set-logic QF_NRAT)
(assert (= 0.0 (sin 7)))
(check-sat)
