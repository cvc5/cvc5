; COMMAND-LINE: --nl-ext=full --nl-ext-tplanes
; EXPECT: unsat
;; Logic not supported in Alethe
; DISABLE-TESTER: alethe
(set-logic QF_UFNRAT)
(set-info :status unsat)
(declare-fun x () Real)
(assert (not (= (+ (sin 0.2) (sin (- 0.2))) 0.0)))
(check-sat)
