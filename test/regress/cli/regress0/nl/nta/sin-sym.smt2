; COMMAND-LINE: --nl-ext=full --nl-ext-tplanes
; EXPECT: unsat
(set-logic QF_UFNRAT)
(set-info :status unsat)
(declare-fun x () Real)
(assert (not (= (+ (sin 0.2) (sin (- 0.2))) 0.0)))
(check-sat)
