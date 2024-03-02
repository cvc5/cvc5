; COMMAND-LINE: --nl-ext=full
; EXPECT: unsat
;; Logic not supported in Alethe
; DISABLE-TESTER: alethe
(set-logic QF_UFNRAT)
(declare-fun x () Real)
(assert (> (cos x) 1.0))
(check-sat)
