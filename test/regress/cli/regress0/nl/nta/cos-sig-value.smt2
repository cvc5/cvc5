; COMMAND-LINE: --nl-ext=full
; EXPECT: unsat
;; Logic not supported in Alethe
; DISABLE-TESTER: alethe
(set-logic QF_UFNRAT)
(set-info :status unsat)
(declare-fun x () Real)
(assert (not (= (cos 0.0) 1.0)))
(check-sat)
